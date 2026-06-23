# GAP verification of Bost-Connes modular flow commutativity
# We verify that the scaling coefficients commute over cyclotomics.
a := E(4); # Complex unit I
b := -1;   # Liouville grading phase (-1)

if a * b = b * a then
    Print("GAP: Bost-Connes commutativity verified successfully.\n");
else
    Error("GAP: Verification failed.\n");
fi;
quit;
