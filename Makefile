build_dir = build
exe = latc_llvm
sec_file = latc

$(exe):
	mkdir -p $(build_dir)
	ghc --make -outputdir $(build_dir) -o $@ -isrc/ -isrc/generated Main.hs
	clang -S -emit-llvm -o lib/runtime.ll lib/runtime.c
	llvm-as lib/runtime.ll -o lib/runtime.bc
	clang latc.c -o $(sec_file)
clean:
	rm -rf $(build_dir) $(exe) $(sec_file)
	rm lib/runtime.ll 
	rm lib/runtime.bc
.PHONY: clean