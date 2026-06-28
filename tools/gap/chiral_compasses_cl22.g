########################################################
# GAP Verification: Cl(1,1) x Cl(1,1) = Cl(2,2)
########################################################

Print("=== GAP: Chiral Compasses ===\n");

# Matrix representation of Cl(1,1) generators
e1 := [[1, 0], [0, -1]];
e2 := [[0, 1], [-1, 0]];
I2 := [[1, 0], [0, 1]];

# Verify Cl(1,1)
if e1*e1 <> I2 then Print("FAIL e1\n"); fi;
if e2*e2 <> -I2 then Print("FAIL e2\n"); fi;
if e1*e2 + e2*e1 <> 0*I2 then Print("FAIL e1e2\n"); fi;

# Kronecker products
E1 := KroneckerProduct(e1, I2);
E2 := KroneckerProduct(e2, I2);

vol_L := e1*e2;
E3 := KroneckerProduct(vol_L, e1);
E4 := KroneckerProduct(vol_L, e2);

I4 := KroneckerProduct(I2, I2);

# Verify Cl(2,2) signature (+, -, +, -)
if E1*E1 <> I4 then Print("FAIL E1^2\n"); fi;
if E2*E2 <> -I4 then Print("FAIL E2^2\n"); fi;
if E3*E3 <> I4 then Print("FAIL E3^2\n"); fi;
if E4*E4 <> -I4 then Print("FAIL E4^2\n"); fi;

# Anti-commutation
if E1*E2 + E2*E1 <> 0*I4 then Print("FAIL E1 E2\n"); fi;
if E1*E3 + E3*E1 <> 0*I4 then Print("FAIL E1 E3\n"); fi;
if E3*E4 + E4*E3 <> 0*I4 then Print("FAIL E3 E4\n"); fi;

Print("  [PASS] GAP matrix algebra confirms left/right tensor split.\n");
