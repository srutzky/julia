P7ZIP_BB_URL_BASE := https://github.com/JuliaBinaryWrappers/p7zip_jll.jl/releases/download/p7zip-v$(P7ZIP_VER)+$(P7ZIP_BB_REL)
P7ZIP_BB_NAME := p7zip.v$(P7ZIP_VER)
$(eval $(call bb-install,p7zip,P7ZIP,false))
