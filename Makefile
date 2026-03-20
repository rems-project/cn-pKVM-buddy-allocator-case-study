CC=clang
BUILD=build
INCLUDES=stddef.h posix_types.h getorder.h
CNFLAGS=

.PHONY: clean run

run: $(BUILD)/driver.exe
	$<

$(BUILD)/driver.pp.c: driver.c page_alloc.c $(INCLUDES)
	mkdir -p $(BUILD)
	$(CC) -E -P -CC $< > $@

$(BUILD)/driver.pp.exec.c $(BUILD)/cn.c: $(BUILD)/driver.pp.c
	cn instrument $< --output-decorated=driver.pp.exec.c --output-decorated-dir=$(BUILD) $(CNFLAGS)
	mv $@ $@~
	sed -e"/ cerb::hidden .*bswap64/d" < $@~ > $@

$(BUILD)/%.o: $(BUILD)/%.c
	$(CC) $< -o $@ -g -c -O2 -std=gnu11 -I$(OPAM_SWITCH_PREFIX)/lib/cn/runtime/include

$(BUILD)/driver.exe: $(BUILD)/cn.o $(BUILD)/driver.pp.exec.o
	$(CC) -o $@ $^ $(OPAM_SWITCH_PREFIX)/lib/cn/runtime/libcn.a

clean:
	rm -rf $(BUILD)
