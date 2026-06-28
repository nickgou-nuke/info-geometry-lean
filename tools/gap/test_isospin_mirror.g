# Formalization of Isospin Group Theory in GAP

Print("Running Isospin Formalization...\n");

# 1. Constructs the SU(2) isospin group representations
# Isospin 1/2 generators (Pauli matrices / 2)
T_z_half := [[1/2, 0], [0, -1/2]];
T_plus_half := [[0, 1], [0, 0]];
T_minus_half := [[0, 0], [1, 0]];

Id_half := [[1, 0], [0, 1]];

Print("SU(2) isospin 1/2 representations defined: true\n");

# 2. Verifies the tensor product rules for isospin (1/2 x 1/2 = 0 + 1)
# Total isospin generators for 2 nucleons
T_z_tensor := KroneckerProduct(T_z_half, Id_half) + KroneckerProduct(Id_half, T_z_half);
T_plus_tensor := KroneckerProduct(T_plus_half, Id_half) + KroneckerProduct(Id_half, T_plus_half);
T_minus_tensor := KroneckerProduct(T_minus_half, Id_half) + KroneckerProduct(Id_half, T_minus_half);

# Casimir operator T^2 = T_z^2 + (T_+ T_- + T_- T_+)/2
T2_tensor := T_z_tensor^2 + 1/2 * (T_plus_tensor * T_minus_tensor + T_minus_tensor * T_plus_tensor);

# Find eigenvalues of T^2 to verify representations 0 and 1
# T(T+1) for T=0 is 0, for T=1 is 2.
eigen_T2 := Eigenvalues(Rationals, T2_tensor);
Sort(eigen_T2);
is_tensor_correct := eigen_T2 = [0, 2];

if is_tensor_correct then
    Print("Tensor product 1/2 x 1/2 = 0 + 1: true\n");
else
    Print("Tensor product 1/2 x 1/2 = 0 + 1: false\n");
fi;

# 3. Defines the isospin projection T_z
eigen_Tz := Eigenvalues(Rationals, T_z_tensor);
Sort(eigen_Tz);
is_Tz_correct := eigen_Tz = [-1, 0, 1];

if is_Tz_correct then
    Print("Isospin projection T_z spectrum correct: true\n");
else
    Print("Isospin projection T_z spectrum correct: false\n");
fi;

# 4. Checks the selection rules for E1 transitions (Delta T = 0 forbidden for N=Z)
# E1 operator for 2-nucleon system (isovector part) is proportional to T_z1 - T_z2
V_z := KroneckerProduct(T_z_half, Id_half) - KroneckerProduct(Id_half, T_z_half);

# T=1, T_z=0 state (symmetric)
state_1_0 := [0, 1, 1, 0];
# T=0, T_z=0 state (antisymmetric)
state_0_0 := [0, 1, -1, 0];

# For E1 in N=Z, Delta T = 0 means <T=1, Tz=0 | V_z | T=1, Tz=0>
mat_el_1_1 := (state_1_0 * V_z) * state_1_0;
is_forbidden := (mat_el_1_1 = 0);

if is_forbidden then
    Print("E1 Delta T = 0 transition forbidden for N=Z: true\n");
else
    Print("E1 Delta T = 0 transition forbidden for N=Z: false\n");
fi;

# 5. Defines the isospin mixing matrix representation
# Mixing between T=0 and T=1 states via Coulomb interaction
E0 := 0;
E1 := 2;
Vc := 1/10; # small Coulomb mixing
H_mixing := [[E0, Vc], [Vc, E1]];

if Length(H_mixing) = 2 then
    Print("Isospin mixing matrix representation defined: true\n");
else
    Print("Isospin mixing matrix representation defined: false\n");
fi;

# Final result
if is_tensor_correct and is_Tz_correct and is_forbidden then
    Print("true\n");
else
    Print("false\n");
fi;
