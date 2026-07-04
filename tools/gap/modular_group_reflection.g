# modular_group_reflection.g
# Representation of modular group and J reflection
G := Group((1,2,3,4,5,6,7), (2,7)(3,6)(4,5));
J := (2,7)(3,6)(4,5);
sigma_t := (1,2,3,4,5,6,7);
sigma_minust := sigma_t^-1;

Print("Checking Tomita-Takesaki J-modular reflection...\n");
if J^2 = () then
    Print("J is a reflection (J^2 = 1).\n");
fi;

if J * sigma_t * J = sigma_minust then
    Print("Verified J sigma_t J = sigma_{-t}.\n");
else
    Print("Verification failed.\n");
fi;
QUIT;
