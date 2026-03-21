CC=${CC:-clang}

# rm -rf build/
mkdir -p build

$CC -E -P -CC driver.c > driver.pp.c
cn instrument ./driver.pp.c --output=driver.pp.exec.c --output-dir=build --without-lemma-checks --without-loop-invariants --exec-c-locs-mode
echo "Compiling..."
$CC -g -c -O0 -std=gnu11 -I$OPAM_SWITCH_PREFIX/lib/cn/runtime/include build/driver.pp.exec.c -include fulminate2.h
echo "Linking..."
$CC driver.pp.exec.o $OPAM_SWITCH_PREFIX/lib/cn/runtime/libcn_exec.a -L $OPAM_SWITCH_PREFIX/lib/cn/runtime -lcn_exec -o driver.exe
echo "Running..."
./driver.exe
echo "Done!"
