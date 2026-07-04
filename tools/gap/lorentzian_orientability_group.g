# Lorentzian Orientability Group: O(p,q) invariants over discrete spaces
# Evaluates quotient invariant structures mapped to chiral sheets.

Print("Evaluating quotient invariant structures of O(p,q) pseudo-orthogonal group...\n");

# Define O(p,q) over a discrete space GF(q_field)
# Let's take O(3,1) which has dimension 4.
p := 3;
q_sig := 1;
dim := p + q_sig;
q_field := 5; # Using GF(5)

# In GAP, orthogonal groups of dimension 4 over finite fields come in two types: +1 and -1.
G := GO(1, dim, q_field);
Print("Constructed G = O(3,1) ~ GO(+1, 4, 5) over GF(5)\n");
Print("Size of G: ", Size(G), "\n");

# The chiral sheets correspond to the orientability components, given by the abelianization G/G'
D := DerivedSubgroup(G);
Q := G / D;
Print("Abelianization (Chiral sheets quotient) Size: ", Size(Q), "\n");

# Compute the character table of G
ct := CharacterTable(G);
irr := Irr(ct);
Print("Total number of irreducible characters: ", Length(irr), "\n");

# Extract 1D (linear) characters, which represent the quotient invariant structures over the chiral sheets
linear_chars := Filtered(irr, chi -> chi[1] = 1);
Print("Number of quotient invariant structures (linear characters): ", Length(linear_chars), "\n");

# Evaluate invariant structure of each chiral sheet
sheet_idx := 1;
for chi in linear_chars do
    ker_size := Size(KernelOfCharacter(chi));
    Print("Sheet ", sheet_idx, ": Character kernel size = ", ker_size, ", Invariant quotient size = ", Size(G)/ker_size, "\n");
    sheet_idx := sheet_idx + 1;
od;

Print("Success.\n");
quit;
