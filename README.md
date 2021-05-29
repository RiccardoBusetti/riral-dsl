# FLC 2021 Compiler Project
This repository contains all the code for the Formal Languages & Compilers project of year 2021 at unibz.
## How to run
In order to run the language you will need to create the code file with `.rl` extension and you can run it via the commands in the `MakeFile`.

A script has been provided to automate the compilation and execution, in order to run the script you need to go into the root folder of the project and execute the `run.sh` file. Note that by default the script will search for a file called `input.rl` in the root folder of the project, if you need to specify a different input file, just change it in the script.

The outputs of the program will be written by default to an `output.txt` file which will be located in the root folder of the project. You can also change this by changing the `OUTPUT_FILE` macro in the `calc-yacc.y` file.
