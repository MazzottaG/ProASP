#include <stdio.h>
#include <stdlib.h>
#include <getopt.h>
#include <iostream>
#include <vector>
#include <unordered_set>

#define COMPILE_OPT 0
#define RUN_OPT 1
#define SOURCE_OPT 2
#define FILE_OPT 3
#define GROUNDING_OPT 4
#define INSTANCE_OPT 5

const int UNKNOWN = -1;
const int COMPILE = 0;
const int RUN     = 1;
const std::string solver_folder = "glucose-4.2.1";
class Exec{
    protected:
        std::vector<std::string> commands;
    public:
        virtual ~Exec(){
            
        }
        virtual void build(const std::string& src,const std::string& file,std::string ground="")=0;
        void lauch(){
            for(std::string command : commands){
                // std::cout << "CMD: "<< command<<std::endl;
                int returncode = system(command.c_str());
                // if(returncode != 0){
                //     std::cout << "Warning: Command "<<command<<" exited with code "<<returncode<<std::endl;
                // }
            }
        }
};
class Run: public Exec{
    virtual void build(const std::string& src,const std::string& file,std::string ground=""){
      std::cout << "Running instance: "<< file <<std::endl;
        commands=std::vector<std::string>({
            src+"/"+solver_folder+"/sources/simp/proasp -verb=0 -no-pre "+file
        });
    }
};
class Compile: public Exec{
    virtual void build(const std::string& src,const std::string& file,std::string ground=""){
        commands=std::vector<std::string>({
            // "make clean -C "+src+"/Compiler",
            // "make -j -C "+src+"/Compiler",
            src+"/Compiler/output/main "+file+(ground!="" ? " "+ground : ""),
            "make clean -C "+src+"/"+solver_folder+"/sources/simp",
            "make -j -C "+src+"/"+solver_folder+"/sources/simp"
        });
    }
};
void exitError(Exec* m,int returncode,std::string message){
    std::cout << message<<std::endl;
    if(m != nullptr){
        delete m;
    }
    exit(returncode);
}
int main (int argc, char **argv)
{
  std::cout << "ProASP Solver"<<std::endl;
  int mode_flag = UNKNOWN;
  Exec* mode = nullptr;

  std::string src = "";
  std::string file = "";
  std::string grounding = "";
  std::string instance = "";
  int c;

  while (1)
    {
      static struct option long_options[] =
        {
          /* These options set a flag. */
          {"compile", no_argument,       0, COMPILE_OPT},
          {    "run", no_argument,       0, RUN_OPT},
          /* These options don’t set a flag.
             We distinguish them by their indices. */
          {      "source",  required_argument, 0, SOURCE_OPT},
          {    "instance",  required_argument, 0, INSTANCE_OPT},
          { "propagators",  required_argument, 0, FILE_OPT},
          {   "grounding",  required_argument, 0, GROUNDING_OPT},
          {0, 0, 0, 0}
        };
      /* getopt_long stores the option index here. */
      int option_index = 0;

      c = getopt_long (argc, argv, "",
                       long_options, &option_index);

      /* Detect the end of the options. */
      if (c == -1)
        break;

      switch (c)
        {
        case SOURCE_OPT:
          src = optarg;
          break;
        case FILE_OPT:
          file = optarg;
          break;
        case GROUNDING_OPT:
          grounding = optarg;
          break;
        case INSTANCE_OPT:
          instance = optarg;
          break;
        case RUN_OPT:
            if(mode_flag != COMPILE){
                mode_flag=RUN;
                if(mode == nullptr){
                    mode=new Run();
                }
            }
            else exitError(mode,180,"Error parsing options: run and compile mode are mutually exclusive");
          break;
        
        case COMPILE_OPT:
            if(mode_flag != RUN){
                mode_flag=COMPILE;
                if(mode == nullptr){
                    mode=new Compile();
                }
            }
            else exitError(mode,180,"Error parsing options: run and compile mode are mutually exclusive");
          break;

        case '?':
          /* getopt_long already printed an error message. */
          break;

        default:
          abort ();
        }
    }
    if(mode == nullptr){
      std::cout << "Missing ProASP Mode:"<<std::endl;
      std::cout << "         run mode: "<<argv[0]<<" --run --source path/to/proasp/home --instance path/to/instance/file"<<std::endl;
      std::cout << "     compile mode: "<<argv[0]<<" --compile --source path/to/proasp/home --propagators path/to/rules/for/compilation --grounding path/to/rules/for/grounding"<<std::endl;

    }else if(mode_flag == RUN && (grounding!="" || file!="" || instance == "")){
      std::cout << "Error launching ProASP in run mode: "<<argv[0]<<" --run --source path/to/proasp/home --instance path/to/instance/file"<<std::endl;
    }else if(mode_flag == COMPILE && (instance!="" || grounding=="" || file=="")){
      std::cout << "Error launching ProASP in compile mode: "<<argv[0]<<" --compile --source path/to/proasp/home --propagators path/to/rules/for/compilation --grounding path/to/rules/for/grounding"<<std::endl;
    }else{
      std::cout << "Launching ProASP"<< std::endl;
      mode->build(src,mode_flag == RUN ? instance : file,grounding);
      mode->lauch();
      exit (0);
    }
  exit(180);
    
}
