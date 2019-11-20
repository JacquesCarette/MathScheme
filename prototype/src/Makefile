all: 
	ocamlbuild -use-ocamlfind -package xmlm matita.native main.native mmt.native

main.native:
	ocamlbuild main.native

mmt.native:
	ocamlbuild mmt.native

matita.native:
	ocamlbuild -use-ocamlfind matita.native

mssyntax.cma: $(OBJECT_FILES)
	$(OCAMLC) -a -o mssyntax.cma $(OCAMLFLAGS) $(OBJECT_FILES)

# Build and test	
test: main.native
	set -ex; \
	for i in parse bind; \
	do \
	  ./main.native -level $$i ../../../doc/biform-theories/Algebra/Base.msl > sa1-$$i.v; \
	  ./main.native -level $$i sa1-$$i.v > sa2-$$i.v; \
	  diff sa1-$$i.v sa2-$$i.v; \
	done
	# flattening isn't expected to be idempotent;
	set -ex; \
	for i in flatten reduce; \
	do \
	  ./main.native -level $$i ../../../doc/biform-theories/Algebra/Base.msl > sa1-$$i.v; \
	  ./main.native -level $$i sa1-$$i.v > sa2-$$i.v; \
	done
	./main.native -level typecheck ../../../doc/biform-theories/Algebra/Base.msl

testmatita: matita.native
	./matita.native ../../../doc/biform-theories/Algebra/Base.msl
	matitac matita/*.ma | grep FAIL

tom.native:
	ocamlbuild -use-ocamlfind tom.native

# Clean up
clean:
	ocamlbuild -clean; \
	for i in parse bind flatten reduce; \
	do \
	  rm -f sa1-$$i.v sa2-$$i.v; \
	done
