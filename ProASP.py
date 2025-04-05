import os
import platform
import subprocess
import re
import argparse

def get_current_folder():
    return os.path.basename(os.getcwd())

def current_folder_is_project_folder():
    if get_current_folder() == 'ProASP':
        return True
    return False

def execute_command(cmd, return_out = False):
    try:
        print(f"\tExecuting: {cmd}")
        # Run the command and capture output
        result = subprocess.run(cmd, shell=True, 
                                #stdout=subprocess.PIPE, 
                                stderr=subprocess.PIPE, 
                                text=True)
        if not result.stdout is None:
            print(result.stdout)
    except Exception as e:
        print(f"Error executing command {cmd} {str(e)}")
        exit(1)


def main():
    if not current_folder_is_project_folder():
        print(f"This script must be run from inside the 'ProASP' directory... Current directory: {get_current_folder()}")
        exit(1)

    clean_command : str = "make clean"
    make_command : str = "make -j "

    parser = argparse.ArgumentParser(prog = "LazyProASP-wrapper", description = "Compiles or executes a ProASP solver\n")
    subparsers = parser.add_subparsers(dest='action')

    compile_parser = subparsers.add_parser('compile', help="Compile a proASP solver", aliases=['compile'])
    compile_parser.add_argument('--comp', help="path to a file containing rules that will be compiled\n", default='')
    compile_parser.add_argument('--ground', help="path to a file containing rules that will be grounded\n", default='')
    compile_parser.add_argument('--lazy', help="path to a file containing rules that will be compiled into post-propagators\n", default='')
    compile_parser.add_argument('--lazyness', type=int, choices=[0, 1], help=" degree of lazyness of the solver\n", default=0)

    execute_parser = subparsers.add_parser('execute', help="Execute a ProASP solver", aliases=['execute'])
    execute_parser.add_argument('--instance', help="path to a file containing rules that will be compiled into post-propagators\n", required=True)

    
    args = parser.parse_args()
    
    #project setup
    compiler_lib = "Compiler/lib"
    antlr_lib = f"{compiler_lib}/libantlr4-runtime.a"
    antlr_lib_macos = f"{compiler_lib}/macos-libantlr4-runtime.a"
    antlr_lib_linux = f"{compiler_lib}/linux-libantlr4-runtime.a"
    if not os.path.isfile(antlr_lib):
        generator_folder = "glucose-4.2.1/sources/simp/generators"
        propagator_folder = "glucose-4.2.1/sources/simp/propagators"
        execute_command(f"mkdir {generator_folder}")
        execute_command(f"mkdir {propagator_folder}")
       
        if platform.system() == "Darwin":
            execute_command(f"cp {antlr_lib_macos} {antlr_lib}")
        else:
            execute_command(f"cp {antlr_lib_linux} {antlr_lib}")

    if args.action == 'compile':
        if args.comp == "" and args.ground == "":
            print("At least one among comp, ground must be specified")
            compile_parser.print_help()
            exit(1)
        execute_command(f"{clean_command} -C Compiler/")
        
        lazyness: str = ""
        if args.lazyness == 1:
            lazyness = "LAZYNESS=LAZYNESS_1"

        print(f'Compiling with args: {args}')
        print(f'to_compile {args.comp} to ground {args.ground} to lazy {args.lazy}')

        print("Doing make:")
        execute_command(make_command + f"-C Compiler {lazyness} ")
        print("Compiler ready... Compiling solver:")

        print("Compiling ASP solver:")

        compile_command : str = f"./Compiler/output/main {args.comp} {args.ground} {args.lazy}"
        execute_command(compile_command)
        
        print("Compiling custom solver:")
        compile_command : str = f"{make_command} -C glucose-4.2.1/sources/simp/"
        execute_command(compile_command)

    elif args.action == 'execute':
        print(f'Executing over instance {args.instance}')
        execute_command(f'./glucose-4.2.1/sources/simp/glucose {args.instance}')
    else:
        print("No command selected")
        parser.print_help()

if __name__ == "__main__":
    main()