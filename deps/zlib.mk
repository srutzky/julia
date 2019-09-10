ZLIB_BB_URL_BASE := https://github.com/JuliaBinaryWrappers/Zlib_jll.jl/releases/download/Zlib-v$(ZLIB_VER)+$(ZLIB_BB_REL)
ZLIB_BB_NAME := Zlib.v$(ZLIB_VER)
$(eval $(call bb-install,zlib,ZLIB,false))
