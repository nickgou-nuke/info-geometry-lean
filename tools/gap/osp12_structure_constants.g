# GAP script to verify osp(1|2) structure constants and super-Jacobi identities

Print("==================================================================\n");
Print("GAP: Structure Constants and Super-Jacobi for osp(1|2)\n");
Print("==================================================================\n");

# Basis elements: H=1, Ep=2, Em=3, G1=4, G2=5
deg := [0, 0, 0, 1, 1];

# Initialize bracket table
bracket_basis := [];
for i in [1..5] do
    bracket_basis[i] := [];
    for j in [1..5] do
        bracket_basis[i][j] := [0, 0, 0, 0, 0];
    od;
od;

# Define basis vectors
H  := [1, 0, 0, 0, 0];
Ep := [0, 1, 0, 0, 0];
Em := [0, 0, 1, 0, 0];
G1 := [0, 0, 0, 1, 0];
G2 := [0, 0, 0, 0, 1];

# Explicit non-zero brackets
# Even-Even (sl2)
bracket_basis[1][2] := 2 * Ep;   # [H, Ep] = 2*Ep
bracket_basis[1][3] := -2 * Em;  # [H, Em] = -2*Em
bracket_basis[2][3] := H;        # [Ep, Em] = H

# Even-Odd
bracket_basis[1][4] := G1;       # [H, G1] = G1
bracket_basis[1][5] := -G2;      # [H, G2] = -G2
bracket_basis[2][5] := G1;       # [Ep, G2] = G1
bracket_basis[3][4] := G2;       # [Em, G1] = G2

# Odd-Odd (anticommutators)
bracket_basis[4][4] := 2 * Ep;   # {G1, G1} = 2*Ep
bracket_basis[5][5] := -2 * Em;  # {G2, G2} = -2*Em
bracket_basis[4][5] := -H;       # {G1, G2} = -H

# Fill in the rest using graded antisymmetry/symmetry
for i in [1..5] do
    for j in [1..5] do
        if i <> j then
            if deg[i] * deg[j] = 0 then
                # even-even or even-odd => antisymmetric
                bracket_basis[j][i] := -bracket_basis[i][j];
            else
                # odd-odd => symmetric
                bracket_basis[j][i] := bracket_basis[i][j];
            fi;
        fi;
    od;
od;

# Function to compute bracket of two arbitrary linear combinations
bracket := function(x, y)
    local res, i, j;
    res := [0, 0, 0, 0, 0];
    for i in [1..5] do
        for j in [1..5] do
            res := res + x[i] * y[j] * bracket_basis[i][j];
        od;
    od;
    return res;
end;

# Verify all super-bracket relations
Print("Verifying super-bracket table:\n");
names := ["H", "Ep", "Em", "G1", "G2"];

# Jacobi verification:
# (-1)^(deg[Z]*deg[X]) * [X, [Y, Z]] +
# (-1)^(deg[X]*deg[Y]) * [Y, [Z, X]] +
# (-1)^(deg[Y]*deg[Z]) * [Z, [X, Y]] = 0
failures := 0;
checked := 0;

for x in [1..5] do
    for y in [1..5] do
        for z in [1..5] do
            vx := [0,0,0,0,0]; vx[x] := 1;
            vy := [0,0,0,0,0]; vy[y] := 1;
            vz := [0,0,0,0,0]; vz[z] := 1;
            
            dx := deg[x]; dy := deg[y]; dz := deg[z];
            
            s1 := (-1)^(dz * dx);
            term1 := s1 * bracket(vx, bracket(vy, vz));
            
            s2 := (-1)^(dx * dy);
            term2 := s2 * bracket(vy, bracket(vz, vx));
            
            s3 := (-1)^(dy * dz);
            term3 := s3 * bracket(vz, bracket(vx, vy));
            
            total := term1 + term2 + term3;
            checked := checked + 1;
            
            if total <> [0,0,0,0,0] then
                Print("  Jacobi FAILED for ", names[x], ", ", names[y], ", ", names[z], "\n");
                failures := failures + 1;
            fi;
        od;
    od;
od;

Print("  Checked ", checked, " triples. Failures: ", failures, "\n");
if failures = 0 then
    Print("  ✓ All Super-Jacobi identities verified successfully!\n");
else
    Print("  ✗ Super-Jacobi verification failed!\n");
    Error("Verification failed");
fi;

Print("\nOVERALL: GAP osp(1|2) Structure Constants Verification: PASSED\n");
QUIT;
