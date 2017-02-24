include Makefile.common

SHELL=/bin/bash

# The versions of gmp and mpfr, for matching on the archive names.
GMP_VERSION=6.1.0
MPFR_VERSION=3.1.3
# The repo to clone valgrind from.
VALGRIND_REPO_LOCATION=svn://svn.valgrind.org/valgrind/trunk
VALGRIND_REVISION=15800
VEX_REPO_LOCATION=svn://svn.valgrind.org/vex/trunk
VEX_REVISION=3210
# The architecture thhat we're buiding herbgrind for, in the syntax of
# valgrind filename conventions for this sort of thing.
TARGET_PLAT:=$(shell test `uname` = "Darwin" && echo "amd64-darwin" || echo "amd64-linux")
ARCH_PRI=amd64
ARCH_SEC=

ifdef ARCH_SEC
DEPS = deps/gmp-64/README deps/mpfr-64/README deps/gmp-32/README deps/mpfr-32/README
else
DEPS = deps/gmp-64/README deps/mpfr-64/README
endif

HEADERS=src/include/herbgrind.h src/helper/mpfr-valgrind-glue.h		\
src/helper/stack.h src/helper/instrument-util.h src/helper/ir-info.h	\
src/helper/debug.h src/options.h					\
src/runtime/value-shadowstate/shadowval.h				\
src/runtime/value-shadowstate/value-shadowstate.h			\
src/runtime/value-shadowstate/exprs.h					\
src/runtime/value-shadowstate/exprs.hh					\
src/runtime/value-shadowstate/real.h					\
src/runtime/op-shadowstate/shadowop-info.h				\
src/runtime/op-shadowstate/mark-info.h					\
src/runtime/shadowop/shadowop.h src/runtime/shadowop/conversions.h	\
src/runtime/shadowop/realop.h src/instrument/instrument.h		\
src/instrument/instrument-op.h src/instrument/instrument-storage.h	\
src/instrument/conversion.h src/instrument/semantic-op.h		\
src/instrument/floattypes.h

SOURCES=src/hg_main.c src/mathwrap.c src/include/mk-mathreplace.py	\
src/helper/mpfr-valgrind-glue.c src/helper/stack.c			\
src/helper/instrument-util.c src/helper/ir-info.c src/options.c		\
src/runtime/value-shadowstate/shadowval.c				\
src/runtime/value-shadowstate/value-shadowstate.c			\
src/runtime/value-shadowstate/shadowval.c				\
src/runtime/value-shadowstate/exprs.c					\
src/runtime/value-shadowstate/real.c					\
src/runtime/op-shadowstate/shadowop-info.c				\
src/runtime/shadowop/shadowop.c src/runtime/shadowop/conversions.c	\
src/runtime/shadowop/realop.c src/instrument/instrument.c		\
src/instrument/instrument-op.c src/instrument/instrument-storage.c	\
src/instrument/conversion.c src/instrument/semantic-op.c		\
src/instrument/floattypes.h

all: compile

# We use the README file of a repo as a proxy for whether or not that
# repo currently exists.
valgrind/README:
# Check out valgrind from source.
	svn co --ignore-externals $(VALGRIND_REPO_LOCATION)@$(VALGRIND_REVISION) valgrind
	svn co $(VEX_REPO_LOCATION)@$(VEX_REVISION) valgrind/VEX
# Run a script to modify the setup files to include the herbgrind
# directory.
	cd setup && ./modify_makefiles.sh
# Make a directory for the herbgrind tool
	mkdir valgrind/herbgrind
# ...and copy the files from the top level herbgrind folder into it.
	cp -r src/* valgrind/herbgrind/

# The herbgrind makefile needs to be recreated, if it's source .am
# file changes or we've just cloned the valgrind repo
valgrind/herbgrind/Makefile: valgrind/README src/Makefile.am
# Copy over the latest version of all the herbgrind stuff, including
# the .am file that we need for this step.
	rm -r -f valgrind/herbgrind/*
	mkdir -p valgrind/herbgrind
	cp -r src/* valgrind/herbgrind/
# Run the autogen and configure scripts to turn the .am file into a
# real makefile.
	cd valgrind && ./autogen.sh
	cd valgrind && \
		CFLAGS="-fno-stack-protector" \
		./configure --prefix=$(shell pwd)/valgrind/$(HG_LOCAL_INSTALL_NAME) \
		            --enable-only64bit \
		            --build=$(TARGET_PLAT)

# This is the target we call to bring in the dependencies, like gmp,
# mpfr, and valgrind, and to make sure the herbgrind files have been
# initially copied over.
setup: valgrind/herbgrind/Makefile $(DEPS)

# This is the target we call to actually get the executable built so
# we can run herbgrind. 
valgrind/$(HG_LOCAL_INSTALL_NAME)/lib/valgrind/herbgrind-$(TARGET_PLAT): $(SOURCES) $(HEADERS) setup
# First, we've got to make sure all the dependencies are extracted and set up.
	$(MAKE) setup
# Then, let's run the python script to generate the mathreplace header
# in src/
	rm -rf src/include/mathreplace-funcs.h
	cd src/include/ && python mk-mathreplace.py
# Copy over the herbgrind sources again, because why the hell not.
	cp -r src/* valgrind/herbgrind
# Run make install to build the binaries and put them in the right
# place.
	$(MAKE) -C valgrind/ install

# Alias the compile target to just "compile" for ease of use
compile: valgrind/$(HG_LOCAL_INSTALL_NAME)/lib/valgrind/herbgrind-$(TARGET_PLAT)

# Use the gmp README to tell if gmp has been extracted yet.
deps/gmp-%/README: setup/gmp-$(GMP_VERSION).tar.xz setup/patch_gmp.sh
# Extract gmp, and rename its folder so we don't have to use the
# version number all over the place.
	tar xf setup/gmp-$(GMP_VERSION).tar.xz
	mkdir -p deps
	mv gmp-$(GMP_VERSION) deps/gmp-$*
# Touch the README to update its timestamp so that we don't build it
# again next time unless the archive changes.
	touch deps/gmp-$*/README
# Patch the gmp files to remove instances of memory functions which
# will fail to link with the valgrind partial c library.
	cd setup && ./patch_gmp.sh $*
# Configure and make it, putting its output in the install folder
# locally instead of in a global location, so it doesn't conflict with
# other versions of gmp.
	cd deps/gmp-$*/ && \
		CFLAGS="-fno-stack-protector" \
		ABI=$* \
		./configure --prefix=$(shell pwd)/deps/gmp-$*/$(HG_LOCAL_INSTALL_NAME)
	$(MAKE) -C deps/gmp-$*
	$(MAKE) -C deps/gmp-$* install

# Adding this flag ensures that MPFR doesn't allocate any of it's
# variables as thread local. This is important because valgrind moves
# around all the tool memory, so we get lots of problems if we let the
# linker try to put thread local variables on our stack. Luckily,
# herbgrind doesn't need threads, nor does valgrind, and client
# programs will be serialized by valgrind, so it's safe to disable
# these.
MPFR_CONFIGURE_FLAGS = --disable-thread-safe

configure-mpfr-32:
	cd deps/mpfr-32/ && \
		CFLAGS="-fno-stack-protector" \
		./configure --prefix=$(shell pwd)/deps/mpfr-32/$(HG_LOCAL_INSTALL_NAME) \
		            --with-gmp-build=$(shell pwd)/deps/gmp-32 \
		            --build=i386 \
		            $(MPFR_CONFIGURE_FLAGS)

configure-mpfr-64:
	cd deps/mpfr-64/ && \
		CFLAGS="-fno-stack-protector" \
		./configure --prefix=$(shell pwd)/deps/mpfr-64/$(HG_LOCAL_INSTALL_NAME) \
		            --with-gmp-build=$(shell pwd)/deps/gmp-64 \
		            --build=amd64 \
		            $(MPFR_CONFIGURE_FLAGS)

# Use the mpfr readme to tell if mpfr has been extracted yet.
deps/mpfr-%/README: setup/mpfr-$(MPFR_VERSION).tar.xz setup/patch_mpfr.sh
# Extract mpfr, and rename its folder so we don't have to use the
# version number all over the place.
	tar xf setup/mpfr-$(MPFR_VERSION).tar.xz
	mkdir -p deps
	rm -rf deps/mpfr-$*
	mv mpfr-$(MPFR_VERSION) deps/mpfr-$*
# Touch the README to update its timestamp so that we don't build it
# again next time unless the archive changes.
	touch deps/mpfr-$*/README
# Patch the mpfr files to allow us to use alternative memory functions
# which will not fail at link time.
	cd setup && ./patch_mpfr.sh $*
# Configure and make mpfr. We want to use the gmp we built locally for
# this, and we'll install it locally too for the same reasons as
# above.
	$(MAKE) configure-mpfr-$*
	$(MAKE) -C deps/mpfr-$*
	$(MAKE) -C deps/mpfr-$* install

wc:
	wc $(SOURCES) $(HEADERS)

clean-deps:
	rm -rf valgrind/ deps/

clean:
	rm vgcore*

clear-preload:
	rm valgrind/$(HG_LOCAL_INSTALL_NAME)/lib/vgpreload_herbgrind*

.PHONY: test backup-logs

test: compile
	python bench/test.py

backup-logs:
	tar czf logs.tar.gz logs
	rsync logs.tar.gz uwplse.org:/var/www/herbie/herbgrind/$(shell hostname)_logs.tar.gz
	rm logs.tar.gz
