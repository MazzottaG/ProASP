import os

cnfFolder = "../test/3cnfgen"
for filename in os.listdir(cnfFolder):
    f = open(f"{cnfFolder}/{filename}","r")
    for line in f:
        if not line[0] in ["c","p"]: 
            constraint = ", ".join([-int(lit) for lit in line.strip().split(" ")[:-1]])
            print(f":- {constraint}.")
    f.close()
    break
    
    