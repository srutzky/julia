// This file is a part of Julia. License is MIT: https://julialang.org/license

/*
  stackwalk.c
  utilities for walking the stack and looking up information about code addresses
*/
#include <inttypes.h>
#include "julia.h"
#include "julia_internal.h"
#include "threading.h"
#include "julia_assert.h"

// define `jl_unw_get` as a macro, since (like setjmp)
// returning from the callee function will invalidate the context
#ifdef _OS_WINDOWS_
#define jl_unw_get(context) RtlCaptureContext(context)
#elif !defined(JL_DISABLE_LIBUNWIND)
#define jl_unw_get(context) unw_getcontext(context)
#else
void jl_unw_get(void *context) {};
#endif

#ifdef __cplusplus
extern "C" {
#endif

static int jl_unw_init(bt_cursor_t *cursor, bt_context_t *context) JL_NOTSAFEPOINT;
static int jl_unw_step(bt_cursor_t *cursor, uintptr_t *ip, uintptr_t *sp, uintptr_t *fp) JL_NOTSAFEPOINT;

// Return 1 if needs more space, 0 otherwise.
//
// `maxsize` is the size of the buffers `bt_data` (and `sp` if non-NULL). It
// must be at least JL_BT_MAX_ENTRY_SIZE to accommodate extended backtrace
// entries.  If `sp != NULL`, the stack pointer corresponding `bt_data[i]` is
// stored in `sp[i]`.
//
// jl_unw_stepn will return 1 if there are more frames to come. The number of
// elements of bt_data which were used are returned in bt_size.
int jl_unw_stepn(bt_cursor_t *cursor, jl_bt_element_t *bt_data, size_t *bt_size,
                 uintptr_t *sp, size_t maxsize, int add_interp_frames) JL_NOTSAFEPOINT
{
    jl_ptls_t ptls = jl_get_ptls_states();
    volatile size_t n = 0;
    volatile int need_more_space = 0;
    uintptr_t theip;
    uintptr_t thesp;
    uintptr_t thefp;
#if defined(_OS_WINDOWS_) && !defined(_CPU_X86_64_)
    assert(!jl_in_stackwalk);
    jl_in_stackwalk = 1;
#endif
#if !defined(_OS_WINDOWS_)
    jl_jmp_buf *old_buf = ptls->safe_restore;
    jl_jmp_buf buf;
    if (!jl_setjmp(buf, 0)) {
        ptls->safe_restore = &buf;
#endif
        while (1) {
            if (n + JL_BT_MAX_ENTRY_SIZE > maxsize) {
                // Postpone advancing the cursor: may need more space
                need_more_space = 1;
                break;
            }
            int have_more_frames = jl_unw_step(cursor, &theip, &thesp, &thefp);
            if (sp)
                sp[n] = thesp;
            jl_bt_element_t *bt_entry = bt_data + n;
            bt_entry->uintptr = theip;
            if (add_interp_frames && jl_is_enter_interpreter_frame(theip)) {
                size_t entry_sz = jl_capture_interp_frame(bt_entry, thesp, thefp, maxsize-n);
                // Preserve native frame if interpreter frame capture failed.
                n += entry_sz == 0 ? 1 : entry_sz;
            } else {
                n++;
            }
            if (!have_more_frames)
                break;
        }
#if !defined(_OS_WINDOWS_)
    }
    else {
        // The unwinding fails likely because a invalid memory read.
        // Back off one frame since it is likely invalid.
        // This seems to be good enough on x86 to make the LLVM debug info
        // reader happy.
        if (n > 0) n -= 1;
    }
    ptls->safe_restore = old_buf;
#endif
#if defined(_OS_WINDOWS_) && !defined(_CPU_X86_64_)
    jl_in_stackwalk = 0;
#endif
    *bt_size = n;
    return need_more_space;
}

size_t rec_backtrace_ctx(jl_bt_element_t *bt_data, size_t maxsize,
                         bt_context_t *context)
{
    size_t bt_size = 0;
    bt_cursor_t cursor;
    if (!jl_unw_init(&cursor, context))
        return 0;
    jl_unw_stepn(&cursor, bt_data, &bt_size, NULL, maxsize, 1);
    return bt_size;
}

size_t rec_backtrace(jl_bt_element_t *bt_data, size_t maxsize)
{
    bt_context_t context;
    memset(&context, 0, sizeof(context));
    jl_unw_get(&context);
    return rec_backtrace_ctx(bt_data, maxsize, &context);
}

static jl_value_t *array_ptr_void_type JL_ALWAYS_LEAFTYPE = NULL;
JL_DLLEXPORT jl_value_t *jl_backtrace_from_here(int returnsp)
{
    jl_array_t *ip = NULL;
    jl_array_t *sp = NULL;
    jl_array_t *bt2 = NULL;
    JL_GC_PUSH3(&ip, &sp, &bt2);
    if (array_ptr_void_type == NULL) {
        array_ptr_void_type = jl_apply_type2((jl_value_t*)jl_array_type, (jl_value_t*)jl_voidpointer_type, jl_box_long(1));
    }
    ip = jl_alloc_array_1d(array_ptr_void_type, 0);
    sp = returnsp ? jl_alloc_array_1d(array_ptr_void_type, 0) : NULL;
    bt2 = jl_alloc_array_1d(jl_array_any_type, 0);
    const size_t maxincr = 1000;
    bt_context_t context;
    bt_cursor_t cursor;
    memset(&context, 0, sizeof(context));
    jl_unw_get(&context);
    if (jl_unw_init(&cursor, &context)) {
        size_t offset = 0;
        while (1) {
            jl_array_grow_end(ip, maxincr);
            uintptr_t *sp_ptr = NULL;
            if (returnsp) {
                sp_ptr = (uintptr_t*)jl_array_data(sp) + offset;
                jl_array_grow_end(sp, maxincr);
            }
            size_t size_incr = 0;
            int need_more_space = jl_unw_stepn(&cursor, (jl_bt_element_t*)jl_array_data(ip) + offset,
                                               &size_incr, sp_ptr, maxincr, 1);
            offset += size_incr;
            if (!need_more_space) {
                jl_array_del_end(ip, jl_array_len(ip) - offset);
                if (returnsp)
                    jl_array_del_end(sp, jl_array_len(sp) - offset);
                break;
            }
        }

        size_t n = 0;
        jl_bt_element_t *bt_data = (jl_bt_element_t*)jl_array_data(ip);
        while (n < jl_array_len(ip)) {
            jl_bt_element_t* bt_entry = bt_data + n;
            if (!jl_bt_is_native(bt_entry)) {
                size_t njlvals = jl_bt_num_jlvals(bt_entry);
                for (size_t j = 0; j < njlvals; j++)
                    jl_array_ptr_1d_push(bt2, jl_bt_entry_jlvalue(bt_entry, j));
            }
            n += jl_bt_entry_size(bt_entry);
        }
    }
    jl_value_t *bt = returnsp ? (jl_value_t*)jl_svec(3, ip, bt2, sp) : (jl_value_t*)jl_svec(2, ip, bt2);
    JL_GC_POP();
    return bt;
}

void decode_backtrace(jl_bt_element_t *bt_data, size_t bt_size,
                      jl_array_t **btout, jl_array_t **bt2out)
{
    jl_array_t *bt = NULL;
    jl_array_t *bt2 = NULL;
    JL_GC_PUSH2(&bt, &bt2);
    if (array_ptr_void_type == NULL) {
        array_ptr_void_type = jl_apply_type2((jl_value_t*)jl_array_type, (jl_value_t*)jl_voidpointer_type, jl_box_long(1));
    }
    bt = jl_alloc_array_1d(array_ptr_void_type, bt_size);
    static_assert(sizeof(jl_bt_element_t) == sizeof(void*),
                  "jl_bt_element_t is presented as Ptr{Cvoid} on julia side");
    memcpy(bt->data, bt_data, bt_size * sizeof(jl_bt_element_t));
    bt2 = jl_alloc_array_1d(jl_array_any_type, 0);
    // Scan the backtrace buffer for any gc-managed values
    for (size_t i = 0; i < bt_size; i += jl_bt_entry_size(bt_data + i)) {
        jl_bt_element_t* bt_entry = bt_data + i;
        if (jl_bt_is_native(bt_entry))
            continue;
        size_t njlvals = jl_bt_num_jlvals(bt_entry);
        for (size_t j = 0; j < njlvals; j++)
            jl_array_ptr_1d_push(bt2, jl_bt_entry_jlvalue(bt_entry, j));
    }
    *btout = bt;
    *bt2out = bt2;
    JL_GC_POP();
}

JL_DLLEXPORT void jl_get_backtrace(jl_array_t **btout, jl_array_t **bt2out)
{
    jl_excstack_t *s = jl_get_ptls_states()->current_task->excstack;
    jl_bt_element_t *bt_data = NULL;
    size_t bt_size = 0;
    if (s && s->top) {
        bt_data = jl_excstack_bt_data(s, s->top);
        bt_size = jl_excstack_bt_size(s, s->top);
    }
    decode_backtrace(bt_data, bt_size, btout, bt2out);
}

// Return data from the exception stack for `task` as an array of Any, starting
// with the top of the stack and returning up to `max_entries`. If requested by
// setting the `include_bt` flag, backtrace data in bt,bt2 format is
// interleaved.
JL_DLLEXPORT jl_value_t *jl_get_excstack(jl_task_t* task, int include_bt, int max_entries)
{
    JL_TYPECHK(catch_stack, task, (jl_value_t*)task);
    jl_ptls_t ptls = jl_get_ptls_states();
    if (task != ptls->current_task &&
        task->state != failed_sym && task->state != done_sym) {
        jl_error("Inspecting the exception stack of a task which might "
                 "be running concurrently isn't allowed.");
    }
    jl_array_t *stack = NULL;
    jl_array_t *bt = NULL;
    jl_array_t *bt2 = NULL;
    JL_GC_PUSH3(&stack, &bt, &bt2);
    stack = jl_alloc_array_1d(jl_array_any_type, 0);
    jl_excstack_t *excstack = task->excstack;
    size_t itr = excstack ? excstack->top : 0;
    int i = 0;
    while (itr > 0 && i < max_entries) {
        jl_array_ptr_1d_push(stack, jl_excstack_exception(excstack, itr));
        if (include_bt) {
            decode_backtrace(jl_excstack_bt_data(excstack, itr),
                             jl_excstack_bt_size(excstack, itr),
                             &bt, &bt2);
            jl_array_ptr_1d_push(stack, (jl_value_t*)bt);
            jl_array_ptr_1d_push(stack, (jl_value_t*)bt2);
        }
        itr = jl_excstack_next(excstack, itr);
        i++;
    }
    JL_GC_POP();
    return (jl_value_t*)stack;
}

#if defined(_OS_WINDOWS_)
#ifdef _CPU_X86_64_
static UNWIND_HISTORY_TABLE HistoryTable;
#else
static struct {
    DWORD64 dwAddr;
    DWORD64 ImageBase;
} HistoryTable;
#endif
static PVOID CALLBACK JuliaFunctionTableAccess64(
        _In_  HANDLE hProcess,
        _In_  DWORD64 AddrBase)
{
    //jl_printf(JL_STDOUT, "lookup %d\n", AddrBase);
#ifdef _CPU_X86_64_
    DWORD64 ImageBase;
    PRUNTIME_FUNCTION fn = RtlLookupFunctionEntry(AddrBase, &ImageBase, &HistoryTable);
    if (fn) return fn;
    if (jl_in_stackwalk) {
        return 0;
    }
    jl_in_stackwalk = 1;
    PVOID ftable = SymFunctionTableAccess64(hProcess, AddrBase);
    jl_in_stackwalk = 0;
    return ftable;
#else
    return SymFunctionTableAccess64(hProcess, AddrBase);
#endif
}
static DWORD64 WINAPI JuliaGetModuleBase64(
        _In_  HANDLE hProcess,
        _In_  DWORD64 dwAddr)
{
    //jl_printf(JL_STDOUT, "lookup base %d\n", dwAddr);
#ifdef _CPU_X86_64_
    DWORD64 ImageBase;
    PRUNTIME_FUNCTION fn = RtlLookupFunctionEntry(dwAddr, &ImageBase, &HistoryTable);
    if (fn) return ImageBase;
    if (jl_in_stackwalk) {
        return 0;
    }
    jl_in_stackwalk = 1;
    DWORD64 fbase = SymGetModuleBase64(hProcess, dwAddr);
    jl_in_stackwalk = 0;
    return fbase;
#else
    if (dwAddr == HistoryTable.dwAddr) return HistoryTable.ImageBase;
    DWORD64 ImageBase = jl_getUnwindInfo(dwAddr);
    if (ImageBase) {
        HistoryTable.dwAddr = dwAddr;
        HistoryTable.ImageBase = ImageBase;
        return ImageBase;
    }
    return SymGetModuleBase64(hProcess, dwAddr);
#endif
}

// Might be called from unmanaged thread.
int needsSymRefreshModuleList;
BOOL (WINAPI *hSymRefreshModuleList)(HANDLE);
void jl_refresh_dbg_module_list(void)
{
    if (needsSymRefreshModuleList && hSymRefreshModuleList != 0 && !jl_in_stackwalk) {
        jl_in_stackwalk = 1;
        hSymRefreshModuleList(GetCurrentProcess());
        jl_in_stackwalk = 0;
        needsSymRefreshModuleList = 0;
    }
}
static int jl_unw_init(bt_cursor_t *cursor, bt_context_t *Context)
{
    jl_refresh_dbg_module_list();
#if !defined(_CPU_X86_64_)
    if (jl_in_stackwalk) {
        return 0;
    }
    jl_in_stackwalk = 1;
    memset(&cursor->stackframe, 0, sizeof(cursor->stackframe));
    cursor->stackframe.AddrPC.Offset = Context->Eip;
    cursor->stackframe.AddrStack.Offset = Context->Esp;
    cursor->stackframe.AddrFrame.Offset = Context->Ebp;
    cursor->stackframe.AddrPC.Mode = AddrModeFlat;
    cursor->stackframe.AddrStack.Mode = AddrModeFlat;
    cursor->stackframe.AddrFrame.Mode = AddrModeFlat;
    cursor->context = *Context;
    BOOL result = StackWalk64(IMAGE_FILE_MACHINE_I386, GetCurrentProcess(), hMainThread,
        &cursor->stackframe, &cursor->context, NULL, JuliaFunctionTableAccess64, JuliaGetModuleBase64, NULL);
    jl_in_stackwalk = 0;
    return result;
#else
    *cursor = *Context;
    return 1;
#endif
}

static int readable_pointer(LPCVOID pointer)
{
    // Check whether the pointer is valid and executable before dereferencing
    // to avoid segfault while recording. See #10638.
    MEMORY_BASIC_INFORMATION mInfo;
    if (VirtualQuery(pointer, &mInfo, sizeof(MEMORY_BASIC_INFORMATION)) == 0)
        return 0;
    DWORD X = mInfo.AllocationProtect;
    if (!((X&PAGE_READONLY) || (X&PAGE_READWRITE) || (X&PAGE_WRITECOPY) || (X&PAGE_EXECUTE_READ)) ||
          (X&PAGE_GUARD) || (X&PAGE_NOACCESS))
        return 0;
    return 1;
}

static int jl_unw_step(bt_cursor_t *cursor, uintptr_t *ip, uintptr_t *sp, uintptr_t *fp)
{
    // Might be called from unmanaged thread.
#ifndef _CPU_X86_64_
    *ip = (uintptr_t)cursor->stackframe.AddrPC.Offset;
    *sp = (uintptr_t)cursor->stackframe.AddrStack.Offset;
    if (fp)
        *fp = (uintptr_t)cursor->stackframe.AddrFrame.Offset;
    if (*ip == 0 || *ip == JL_BT_NON_PTR_ENTRY) {
        // JL_BT_NON_PTR_ENTRY is a special marker in the backtrace.
        // Remove it to avoid confusing JL_BT_IS_NATIVE and corrupting the gc.
        *ip = 0;
        if (!readable_pointer((LPCVOID)*sp))
            return 0;
        cursor->stackframe.AddrPC.Offset = *(DWORD32*)*sp;      // POP EIP (aka RET)
        cursor->stackframe.AddrStack.Offset += sizeof(void*);
        return cursor->stackframe.AddrPC.Offset != 0;
    }

    BOOL result = StackWalk64(IMAGE_FILE_MACHINE_I386, GetCurrentProcess(), hMainThread,
        &cursor->stackframe, &cursor->context, NULL, JuliaFunctionTableAccess64, JuliaGetModuleBase64, NULL);
    return result;
#else
    *ip = (uintptr_t)cursor->Rip;
    *sp = (uintptr_t)cursor->Rsp;
    if (fp)
        *fp = (uintptr_t)cursor->Rbp;
    if (*ip == 0 || *ip == JL_BT_NON_PTR_ENTRY) {
        // JL_BT_NON_PTR_ENTRY is a special marker in the backtrace.
        // Remove it to avoid confusing JL_BT_IS_NATIVE and corrupting the gc.
        *ip = 0;
        if (!readable_pointer((LPCVOID)*sp))
            return 0;
        cursor->Rip = *(DWORD64*)*sp;      // POP RIP (aka RET)
        cursor->Rsp += sizeof(void*);
        return cursor->Rip != 0;
    }

    DWORD64 ImageBase = JuliaGetModuleBase64(GetCurrentProcess(), cursor->Rip);
    if (!ImageBase)
        return 0;

    PRUNTIME_FUNCTION FunctionEntry = (PRUNTIME_FUNCTION)JuliaFunctionTableAccess64(
        GetCurrentProcess(), cursor->Rip);
    if (!FunctionEntry) { // assume this is a NO_FPO RBP-based function
        cursor->Rsp = cursor->Rbp;                 // MOV RSP, RBP
        if (!readable_pointer((LPCVOID)cursor->Rsp))
            return 0;
        cursor->Rbp = *(DWORD64*)cursor->Rsp;      // POP RBP
        cursor->Rsp += sizeof(void*);
        cursor->Rip = *(DWORD64*)cursor->Rsp;      // POP RIP (aka RET)
        cursor->Rsp += sizeof(void*);
    }
    else {
        PVOID HandlerData;
        DWORD64 EstablisherFrame;
        (void)RtlVirtualUnwind(
                0 /*UNW_FLAG_NHANDLER*/,
                ImageBase,
                cursor->Rip,
                FunctionEntry,
                cursor,
                &HandlerData,
                &EstablisherFrame,
                NULL);
    }
    return cursor->Rip != 0;
#endif
}

#elif !defined(JL_DISABLE_LIBUNWIND)
// stacktrace using libunwind

static int jl_unw_init(bt_cursor_t *cursor, bt_context_t *context)
{
    return unw_init_local(cursor, context) == 0;
}

static int jl_unw_step(bt_cursor_t *cursor, uintptr_t *ip, uintptr_t *sp, uintptr_t *fp)
{
    unw_word_t reg;
    if (unw_get_reg(cursor, UNW_REG_IP, &reg) < 0)
        return 0;
    // JL_BT_NON_PTR_ENTRY is a special marker in the backtrace.
    // Remove it to avoid confusing JL_BT_IS_NATIVE and corrupting the gc.
    *ip = reg == JL_BT_NON_PTR_ENTRY ? 0 : reg;
    if (unw_get_reg(cursor, UNW_REG_SP, &reg) < 0)
        return 0;
    *sp = reg;
#ifdef UNW_REG_FP
    if (unw_get_reg(cursor, UNW_REG_FP, &reg) < 0)
        return 0;
    if (fp)
        *fp = reg;
#else
    if (fp)
        *fp = 0;
#endif
    return unw_step(cursor) > 0;
}

#ifdef LIBOSXUNWIND
int jl_unw_init_dwarf(bt_cursor_t *cursor, bt_context_t *uc)
{
    return unw_init_local_dwarf(cursor, uc) != 0;
}
size_t rec_backtrace_ctx_dwarf(uintptr_t *bt_data, size_t maxsize,
                               bt_context_t *context)
{
    size_t bt_size = 0;
    bt_cursor_t cursor;
    if (!jl_unw_init_dwarf(&cursor, context))
        return 0;
    jl_unw_stepn(&cursor, bt_data, &bt_size, NULL, maxsize, 1);
    return bt_size;
}
#endif

#else
// stacktraces are disabled
static int jl_unw_init(bt_cursor_t *cursor, bt_context_t *context)
{
    return 0;
}

static int jl_unw_step(bt_cursor_t *cursor, uintptr_t *ip, uintptr_t *sp, uintptr_t *fp)
{
    return 0;
}
#endif

JL_DLLEXPORT jl_value_t *jl_lookup_code_address(void *ip, int skipC)
{
    jl_ptls_t ptls = jl_get_ptls_states();
    jl_frame_t *frames = NULL;
    int8_t gc_state = jl_gc_safe_enter(ptls);
    int n = jl_getFunctionInfo(&frames, (uintptr_t)ip, skipC, 0);
    jl_gc_safe_leave(ptls, gc_state);
    jl_value_t *rs = (jl_value_t*)jl_alloc_svec(n);
    JL_GC_PUSH1(&rs);
    for (int i = 0; i < n; i++) {
        jl_frame_t frame = frames[i];
        jl_value_t *r = (jl_value_t*)jl_alloc_svec(7);
        jl_svecset(rs, i, r);
        if (frame.func_name)
            jl_svecset(r, 0, jl_symbol(frame.func_name));
        else
            jl_svecset(r, 0, empty_sym);
        free(frame.func_name);
        if (frame.file_name)
            jl_svecset(r, 1, jl_symbol(frame.file_name));
        else
            jl_svecset(r, 1, empty_sym);
        free(frame.file_name);
        jl_svecset(r, 2, jl_box_long(frame.line));
        jl_svecset(r, 3, frame.linfo != NULL ? (jl_value_t*)frame.linfo : jl_nothing);
        jl_svecset(r, 4, jl_box_bool(frame.fromC));
        jl_svecset(r, 5, jl_box_bool(frame.inlined));
        jl_svecset(r, 6, jl_box_voidpointer(ip));
    }
    free(frames);
    JL_GC_POP();
    return rs;
}

void jl_safe_print_codeloc(const char* func_name, const char* file_name,
                           int line, int inlined)
{
    const char *inlined_str = inlined ? " [inlined]" : "";
    if (line != -1) {
        jl_safe_printf("%s at %s:%d%s\n", func_name, file_name, line, inlined_str);
    }
    else {
        jl_safe_printf("%s at %s (unknown line)%s\n", func_name, file_name, inlined_str);
    }
}

// Print function, file and line containing native instruction pointer `ip` by
// looking up debug info. Prints multiple such frames when `ip` points to
// inlined code.
//
// The need for `do_offset` is somewhat lost in history but apparently gives
// better C stack traces in some cases. See issue #15845
void jl_print_native_codeloc(uintptr_t ip, int do_offset) JL_NOTSAFEPOINT
{
    if (do_offset)
        ip -= 1;
    // This function is not allowed to reference any TLS variables since
    // it can be called from an unmanaged thread on OSX.
    // it means calling getFunctionInfo with noInline = 1
    jl_frame_t *frames = NULL;
    int n = jl_getFunctionInfo(&frames, ip, 0, 0);
    int i;

    for (i = 0; i < n; i++) {
        jl_frame_t frame = frames[i];
        if (!frame.func_name) {
            jl_safe_printf("unknown function (ip: %p)\n", (void*)ip);
        }
        else {
            jl_safe_print_codeloc(frame.func_name, frame.file_name, frame.line, frame.inlined);
            free(frame.func_name);
            free(frame.file_name);
        }
    }
    free(frames);
}

// Print code location for backtrace buffer entry at *bt_entry
void jl_print_bt_entry_codeloc(jl_bt_element_t *bt_entry) JL_NOTSAFEPOINT
{
    if (jl_bt_is_native(bt_entry)) {
        jl_print_native_codeloc(bt_entry[0].uintptr, 1);
    }
    else if (jl_bt_entry_tag(bt_entry) == JL_BT_INTERP_FRAME_TAG) {
        size_t ip = jl_bt_entry_header(bt_entry);
        jl_value_t *code = jl_bt_entry_jlvalue(bt_entry, 0);
        if (jl_is_method_instance(code)) {
            // When we were not interpreting at top level, need to unwrap the MI.
            code = ((jl_method_instance_t*)code)->uninferred;
        }
        if (jl_is_code_info(code)) {
            jl_code_info_t *src = (jl_code_info_t*)code;
            // See also the debug info handling in codegen.cpp
            int32_t debuginfoloc = ((int32_t*)jl_array_data(src->codelocs))[ip];
            jl_value_t *locinfo = jl_array_ptr_ref(src->linetable, debuginfoloc);
            while (1) {
                assert(jl_typeis(locinfo, jl_lineinfonode_type));
                jl_value_t *method = jl_fieldref_noalloc(locinfo, 0);
                if (jl_is_method_instance(method)) {
                    method = ((jl_method_instance_t*)method)->def.value;
                    if (jl_is_method(method))
                        method = (jl_value_t*)((jl_method_t*)method)->name;
                }
                const char *func_name = jl_is_symbol(method) ?
                                        jl_symbol_name((jl_sym_t*)method) : "Unknown";
                jl_sym_t *file_sym  = (jl_sym_t*)jl_fieldref_noalloc(locinfo, 1);
                ssize_t line       = jl_unbox_long(jl_fieldref_noalloc(locinfo, 2));
                ssize_t inlined_at = jl_unbox_long(jl_fieldref_noalloc(locinfo, 3));
                jl_safe_print_codeloc(func_name, jl_symbol_name(file_sym), line, inlined_at);
                if (inlined_at == 0)
                    break;
                locinfo = jl_array_ptr_ref(src->linetable, inlined_at);
            }
        }
        else {
            // If we're using this function something bad has already happened;
            // be a bit defensive to avoid crashing while reporting the crash.
            jl_safe_printf("No code info - unknown interpreter state!\n");
        }
    }
    else {
        jl_safe_printf("Non-native bt entry with tag and header bits 0x%" PRIxPTR "\n",
                       bt_entry[1].uintptr);
    }
}

//--------------------------------------------------
// Tools for interactive debugging in gdb
JL_DLLEXPORT void jl_gdblookup(void* ip)
{
    jl_print_native_codeloc((uintptr_t)ip, 0);
}

// Print top-of-stack backtrace for current catch block
JL_DLLEXPORT void jlbacktrace(void) JL_NOTSAFEPOINT
{
    jl_excstack_t *s = jl_get_ptls_states()->current_task->excstack;
    if (!s)
        return;
    size_t bt_size = jl_excstack_bt_size(s, s->top);
    jl_bt_element_t *bt_data = jl_excstack_bt_data(s, s->top);
    for (size_t i = 0; i < bt_size; i += jl_bt_entry_size(bt_data + i)) {
        jl_print_bt_entry_codeloc(bt_data + i);
    }
}

#ifdef __cplusplus
}
#endif
