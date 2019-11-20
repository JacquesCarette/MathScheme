MathScheme Printers:

If at anytime you have question which cannot be answered here feel free
to email me, Vincent Maccio, at vincentmaccio@gmail.com. Dr. Carette is 
also fairly familiar with these files.

Description:

The MathShcheme family of printers is aimed to create a variety of styles
and syntaxes to be outputted for user consumption. The system consists of
the following files.
-printers.ml
-configuration.ml
-options.ml

For an in depth descriction of how the modules interact I suggest you
read the description section of the file
- /trunk/code/chiron/readme_chiron_printers.txt
The MathScheme printers use the same design and architecture ideas that 
the Chiron printers do. It is also recommended to read the source file 
- /trunk/code/syntax/src/syntax.ml
for an understanding of the internal representation of MathScheme types.

Compilation:

Printers.ml and corresponding modules are part of the makefile and should be
compiled with a 'make' in the directory trunk/code/syntax/src

You can also manually compile these file using the following commands.
:> ocamlc -c configuration.ml
:> ocamlc -c options.ml
:> ocamlc -c printers.ml

Testing:

Whenever you make a change to the printer make sure it still expands
the file Base.ml properly. This is a benchmark which we have been using.
To do this simply run a 'make test' in the directory

- /trunk/code/syntax/src

This will produc several files. The file to check is sa1e.v, if this 
prints properly than the printer is good to check in. For testing other
expressions there is the file

- /trunk/code/syntax/src/printer_tests.ml

Here you can make your own internally represented MathScheme types to 
see how they print out under certain parameters. Feel free to play around
with the options as well as switch between the different configuration to
see and understand how things work. 

To compile and build, first compile the other modules (you will need to 
do this each time you make a change to the configuration or options)

:> ocamlc -c configuration.ml
:> ocamlc -c options.ml
:> ocamlc -c printers.ml

Next compile and build the printer using these commands 
:> ocamlc -c printer_tests.ml
:> ocamlc -o "printer_tests" configuration.cmo options.cmo syntax.cmo printers.cmo "printer_tests.ml"

Then to run the file.
:> ./printer_tests

Latex: 

When using the Latex configuration you will need to output code to a file
and then add these two lines. At the top add

/input{mlh}

and at the bottom add 

/input{mlf]

It is suggested to read the Latex section of readme_chiron_printer.txt 
for details concerning how the Latex components work.
