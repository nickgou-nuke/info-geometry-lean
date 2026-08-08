R = QQ[x0,x1,x2,x3,Degrees=>{1,1,1,1}];
I = ideal(x0^2-1,x1^2+1,x2^2+1,x3^2+1);
print("MACAULAY2_CL14_QUADRATIC_IDEAL");
print trim gens gb I;
print("Dmodules package status:");
print isPackageInstalled "Dmodules";
