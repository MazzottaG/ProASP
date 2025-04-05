# ProASP
In order to use ProASP please open the cloned repository in your terminal and type:
```
make
```
## Compile a ASP program into an ProASP solver
In order to build and to execute a ParoASP solver, the utility script wrapper.py can be used.

To compile a ProASP solver three files are needed:

* "path/to_compile.asp": this file contains the rules that should be compiled into propagators
* "path/to_ground.asp": this file contains the rules that should be compiled into variable-elimination procedures
* "path/to_lazy.asp": this file contains the rules that should be compiled into post-propagator procedures

```
python3 wrapper.py compile --comp path/to_compile.asp --ground --propagators path/to_ground.asp --lazy  path/to_lazy.asp
```
Note: if all the three files are specified, ProASP-Lazy compiles an hybrid ProASP solver in which the rules inside the to_lazy file are compiled into post-propagators.

By moving rules among the three files, all available versionns of ProASP (namely ground, compiled and hybrid) can be compiled, with or without post-propagators

## Run an ProASP-Lazy Solver
In order to run a generated ProASP solver, a file containing input facts is needed:
```
python3 wrapper.py execute --instance path/instance.asp
```

Note: ProASP works on Linux and MacOS
