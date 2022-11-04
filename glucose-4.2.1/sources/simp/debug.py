d_p_2=[[x.split(")")[0].split("(")[1]] for x in ["p_2(5)",
"p_2(4)",
"p_2(2)",
"p_2(1)",
"p_2(0)"]]

d_p_0=[x.split("(")[1].split(")")[0].split(",") for x in ["p_0(0,2)",
"p_0(1,1)",
"p_0(1,3)",
"p_0(0,5)",
"p_0(3,3)"]]
d_aux=[]
# #p_2(2) p_0(X_2,X_1) p_2(X_0) p_2(X_0) not aux_0(X_2,X_1,X_0) X_1 > 2 
gen=True
while gen:
    gen = False
    if ["2"] in d_p_2:
        for p_0 in d_p_0:
            X2=p_0[0]
            X1=p_0[1]
            if int(X1) > 2:
                for p_2 in d_p_2:
                    X0=p_2[0]
                    if [X2,X1,X0] not in d_aux:
                        d_aux.append([X2,X1,X0])
    for aux in d_aux:
        if [aux[0]] not in d_p_2:
            d_p_2.append([aux[0]])
            gen=True

exists_aux=[]
for aux in d_aux:
    t = int(aux[0])
    if t not in exists_aux:
        exists_aux.append(t)

print(exists_aux)