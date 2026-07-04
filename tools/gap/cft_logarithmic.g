# Formalization of Logarithmic CFT Nilpotent Boundaries

Print("Formalizing Logarithmic CFT Nilpotent Boundaries\n");

# Define the indeterminate h over the Rationals
h := Indeterminate(Rationals, "h");

# Define the L_0 matrix (Jordan block of size 2 with eigenvalue h)
L_0 := [[h, 1], [0, h]];

# Define the Identity matrix of size 2
I := [[1, 0], [0, 1]];

# Compute the exact polynomial limits (L_0 - h*I)
L_0_minus_hI := L_0 - h * I;

# Square it algebraically
nilpotent_limit := L_0_minus_hI ^ 2;

# Expected zero matrix
zero_matrix := 0 * I;

Print("L_0:\n");
Display(L_0);
Print("\n");

Print("L_0 - h*I:\n");
Display(L_0_minus_hI);
Print("\n");

Print("(L_0 - h*I)^2:\n");
Display(nilpotent_limit);
Print("\n");

if IsZero(nilpotent_limit) then
    Print("Success: The squared matrix exactly reduces to the zero matrix.\n");
else
    Print("Error: The squared matrix is NOT the zero matrix.\n");
fi;

QUIT;
