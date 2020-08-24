all : lib
lib : objsize.cmxa

.PHONY : all clean

objsize.cmxa: objsize.cmx
	ocamlmklib -verbose -o objsize -linkall $^
	cp -n objsize.a libobjsize.a

objsize.cmi : objsize.mli
	ocamlopt -verbose -c $<

objsize.cmx : objsize.ml objsize.cmi
	ocamlopt -verbose -c $<

clean :
	rm -f objsize.*cm* objsize.o objsize.a libobjsize.a
