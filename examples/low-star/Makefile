FSTAR_HOME=../..
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
ALLOCATOR_DIR = ../../runtime/allocator
ALLOCATOR_FILES = $(ALLOCATOR_DIR)/camlstack.o $(ALLOCATOR_DIR)/stack.o \
	$(ALLOCATOR_DIR)/bitmask.o $(ALLOCATOR_DIR)/camlstack.mli

FSTAR_OCAML_LIB=prims.ml FStar_List.ml FStar_All.ml FStar_ST.ml

OCAML = ocamlfind ocamlopt -g -package batteries -linkpkg -thread -I ../../lib/ml \
 -I $(ALLOCATOR_DIR) $(ALLOCATOR_FILES) $(addprefix ../../lib/ml/, $(FSTAR_OCAML_LIB))

all: verify

test: codegen demo

# Those ml files are copied back from the low-level folder, same as what Abhishek
# was doing. It would be good to have extraction working so that we get the good
# files immediately
codegen: demo.fst
	$(FSTAR) $^
#	Broken, those files were removed
	cp ../low-level/Located.ml .
	cp ../low-level/Lref.ml .
	cp ../low-level/RST.ml .
	cp ../low-level/Seq.ml .
	cp ../low-level/SSTArray.ml .
	cp ./ml/CSystem.ml ./ml/CBuffer.ml ./ml/Test.ml .

SST_FILES=ListSet.ml Stack.ml FStar_FunctionalExtensionality.ml FStar_Ghost.ml Located.ml \
	Lref.ml Regions.ml RST.ml Seq.ml RSTArray.ml RSTWhile.ml

demo: $(SST_FILES) CBuffer.ml CSystem.ml Demo.ml Test.ml
	make -C ../../runtime/allocator
	gcc -I$(shell ocamlc -where) -c ./ml/cfun.c -o cfun.o
	cp ./ml/CSystem.ml ./ml/CBuffer.ml .
	$(OCAML) cfun.o -o $@ $^
	./demo
	@echo "Content of the output.txt file :"
	@cat output.txt

verify: demo.fst
	$(FSTAR) $^

### NB : only works using the c-extraction branch of F* ###

# First example (monomorphization)
test1: codegen1

codegen1: ex1.fst
#	Because of excessive debugging information, not printing F* output
	$(FSTAR) $^ > /dev/null
	@echo
	@echo "Verification was successful, testing compilation..."
	@echo
	gcc -c Ex1.c
	@echo "Compilation went well"
	@echo
	@echo "Produced C code :"
	@cat Ex1.c

test2: codegen2

codegen2: ex2.fst
#	Because of excessive debugging information, not printing F* output
	$(FSTAR) $^ > /dev/null
	@echo
	@echo "Verification was successful, compiling..."
	@echo
	gcc Ex2.c ./test/test2.c -o test2
	@echo "123, not encrypted so far" > test2.txt
	@echo
	@echo "Created dummy file containing \" 123, not encrypted so far"
	@echo
	./test2 test2.txt
	@rm test2.txt
###

clean:
	rm -f *.ml *.cmi *.cmo *.cmx *.o || true
