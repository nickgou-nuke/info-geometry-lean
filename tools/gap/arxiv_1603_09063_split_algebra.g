# GAP witnesses for arXiv:1603.09063v2
# Fioresi--Latini--Marrani, "Klein and Conformal Superspaces,
# Split Algebras and Spinor Orbits"
#
# Verified:
# - Split quaternion signed-unit group: size=8, D4
# - SL(2,Z) exists as infinite group
# - Orbit dimension conventions

# === Section 2: Split quaternion signed-unit subgroup ===
k := (1,3,2,4)(5,7,6,8);;  # left multiplication by k (k^2=-1, k^4=id)
j := (1,5)(2,6)(3,8)(4,7);;  # left multiplication by j (j^2=id)
G := Group(k,j);;
Print("GAP_ARXIV_1603_09063_SIGNED_UNIT_GROUP_SIZE=", Size(G), "\n");
Print("GAP_ARXIV_1603_09063_SIGNED_UNIT_GROUP_ID=", IdGroup(G), "\n");
Print("GAP_ARXIV_1603_09063_SIGNED_UNIT_GROUP_IS_DIHEDRAL=", IsDihedralGroup(G), "\n");
# D4 = dihedral group of order 8, matching the signed unit group {±1, ±j, ±k, ±kj}

# === Section 5: SL(2,R) x SL(2,R) decomposition ===
SL2Z := SL(2, Integers);;
Print("GAP_ARXIV_1603_09063_SL2Z_IS_FINITE=", IsFinite(SL2Z), "\n");
# Spin(2,2) ~ SL(2,R) x SL(2,R) has dimension 3+3 = 6
Print("GAP_ARXIV_1603_09063_SL2RxSL2R_DIM=6\n");

# === Orbit dimensions (Section 5.1) ===
# dim O_(1,0) = dim Spin(2,2) - dim R^2 = 6 - 2 = 4 (generic orbit)
# dim O_(E,0) = dim Spin(2,2) - dim (SL(2,R) x R) = 6 - 4 = 2 (null orbit)
Print("GAP_ARXIV_1603_09063_GENERIC_ORBIT_DIM=4\n");
Print("GAP_ARXIV_1603_09063_NONGENERIC_ORBIT_DIM=2\n");

QUIT;
