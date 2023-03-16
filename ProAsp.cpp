#include <stdio.h>
#include <stdlib.h>
#include <getopt.h>
#include <iostream>
#include <vector>
#include <unordered_set>

const int UNKNOWN = -1;
const int COMPILE = 0;
const int RUN     = 1;
class Exec{
    protected:
        std::vector<std::string> commands;
    public:
        virtual ~Exec(){
            
        }
        virtual void build(const std::string& src,const std::string& file)=0;
        void lauch(){
            for(std::string command : commands){
                int returncode = system(command.c_str());
                if(returncode != 0){
                    std::cout << "Warning: Command "<<command<<" exited with code "<<returncode<<std::endl;
                }
            }
        }
};
class Run: public Exec{
    virtual void build(const std::string& src,const std::string& file){
        commands=std::vector<std::string>({
            src+"/glucose-4.2.1/sources/simp/glucose -no-pre -verb=0 "+file
        });
    }
};
class Compile: public Exec{
    virtual void build(const std::string& src,const std::string& file){
        commands=std::vector<std::string>({
            "make clean -C "+src+"/Compiler",
            "make -j -C "+src+"/Compiler",
            src+"/Compiler/output/main "+file,
            "make clean -C "+src+"/glucose-4.2.1/sources/simp",
            "make -j -C "+src+"/glucose-4.2.1/sources/simp"
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
  int mode_flag = UNKNOWN;
  Exec* mode = nullptr;

  std::string src = "";
  std::string file = "";
  int c;

  while (1)
    {
      static struct option long_options[] =
        {
          /* These options set a flag. */
          {"compile", no_argument,       0, 'c'},
          {    "run", no_argument,       0, 'r'},
          /* These options don’t set a flag.
             We distinguish them by their indices. */
          {"source",  required_argument, 0, 's'},
          {  "file",  required_argument, 0, 'f'},
          {0, 0, 0, 0}
        };
      /* getopt_long stores the option index here. */
      int option_index = 0;

      c = getopt_long (argc, argv, "rcs:f:",
                       long_options, &option_index);

      /* Detect the end of the options. */
      if (c == -1)
        break;

      switch (c)
        {
        case 's':
          src = optarg;
          break;
        case 'f':
          file = optarg;
          break;
        
        case 'r':
            if(mode_flag != COMPILE){
                mode_flag=RUN;
                if(mode == nullptr){
                    mode=new Run();
                }
            }
            else exitError(mode,180,"Error parsing options: run and compile mode are mutually exclusive");
          break;
        
        case 'c':
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
    mode->build(src,file);
    mode->lauch();
    exit (0);
}
