CC = clang
BUILD = build
INCLUDES = stddef.h posix_types.h getorder.h
CNDIR := $(OPAM_SWITCH_PREFIX)/lib/cn/runtime

FULMOPT = --without-lemma-checks
CCOPT = -O2


.PHONY: clean run

run: $(BUILD)/driver.exe
	zsh -c 'export TIMEFMT="$$TIMEFMT %MMB rss" && time $<'

bench: $(BUILD)/driver.exe
	hyperfine $<

$(BUILD)/driver.pp.c: driver.c page_alloc.c $(INCLUDES)
	mkdir -p $(BUILD)
	$(CC) -E -P -CC $< > $@

$(BUILD)/driver.pp.exec.c: $(BUILD)/driver.pp.c
	cn instrument $(FULMOPT) $< --output=driver.pp.exec.c --output-dir=$(BUILD)
	mv $@ $@~
	sed -e "/ cerb::hidden .*bswap64/d" < $@~ > $@

$(BUILD)/driver.pp.exec.o: $(BUILD)/driver.pp.exec.c
	$(CC) -g -c -std=gnu11 -I$(CNDIR)/include $(CCOPT) $< -o $@

$(BUILD)/driver.exe: $(BUILD)/driver.pp.exec.o
	$(CC) $< -o $@ $(CNDIR)/libcn_exec.a -L$(CNDIR) -lcn_exec

clean:
	rm -rf $(BUILD)
