
VERSION	  := $(shell cut -d\" -f2 src/version.ml)
TARGET	  := flap
PACKAGE	  := flap-$(shell whoami)-$(VERSION)

BTARGET	 = $(TARGET).byte
OTARGET	 = $(TARGET).native
BLTARGET = $(TARGET).cma
BNTARGET = $(TARGET).cmxa
STARGET	 = $(OTARGET)

#########################
## Tools configuration ##
#########################

# Menhir can be told to produce a parser that explains what
# it is doing.
ifeq ($(DEBUGPARSING), yes)
  MENHIROPT=-yaccflag --explain -yaccflag --trace
else
  MENHIROPT=-yaccflag --explain
endif

# In Emacs, use classic display to enable error jumping.
TERM = $(shell echo $$TERM)
ifeq ($(TERM), dumb)
 OCAMLBUILDFLAGS = -cflag "-dtypes" -tag debug -classic-display -no-hygiene $(MENHIROPT)
else
 OCAMLBUILDFLAGS = -no-hygiene $(MENHIROPT)
endif

OCAMLBUILD = ocamlbuild -use-menhir $(OCAMLBUILDFLAGS)

OCAMLDOC = ocamldoc
HEADACHE = headache

#########
# Rules #
#########

.PHONY: all-generic byte opt doc clean dist install uninstall headers clear

all-generic: clear $(STARGET) $(TARGET)

$(TARGET):
	ln -sf $(STARGET) $(TARGET)

clear:
	rm -f $(STARGET)

opt: $(OTARGET)

byte: $(BTARGET)

%:
	@ $(OCAMLBUILD) src/$@

byte-debug:
	$(OCAMLBUILD) -tag debug src/$(BTARGET)
	rm -f $(STARGET)
	ln -s $(BTARGET) $(STARGET)

ifeq ($(strip $(PREFIX)),)
install uninstall:
	@echo "Cannot (un)install $(EXECUTABLE): the PREFIX variable is undefined." && false
else
install: $(EXECUTABLE)
	mkdir -p $(PREFIX)/bin/
	install $(STARGET) $(PREFIX)/bin/$(TARGET)
uninstall:
	/bin/rm -f $(PREFIX)/bin/$(TARGET)
endif

#######################
# Administrative part #
#######################

headers:
	for i in src/*.ml src/*.mli src/*.mly; do \
	   $(HEADACHE) -h admin/header -c admin/headache.cfg $$i; \
	done

clean:
	@ $(OCAMLBUILD) -clean
	find . -name '*~' -exec rm '{}' \;
	rm -fr *~ $(TARGET) $(OTARGET) $(BTARGET) $(PACKAGE) $(PACKAGE).tar.gz

doc: byte
	$(OCAMLBUILD) $(TARGET).docdir/index.html
	mkdir -p doc/html
	rm -f $(TARGET).docdir/style.css 2> /dev/null
	mv $(TARGET).docdir/* doc/html
	rm $(TARGET).docdir

dist:
	@echo "Attention! Seuls les fichiers connus par git seront mis dans l'archive" 
	rm -fr $(PACKAGE)
	mkdir $(PACKAGE)
	for i in `git ls-files`; do	\
	  if test -f $$i; then					\
	    cp -fr --parents $$i $(PACKAGE);			\
	  else							\
	    mkdir -p $$i;					\
	  fi;							\
	done
	tar cfz $(PACKAGE).tar.gz $(PACKAGE)

check: all
	$(MAKE) -C tests check
