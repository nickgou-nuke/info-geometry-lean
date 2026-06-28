# GAP: Hestenes Spacetime Algebra
# Verifies gamma matrix anticommutation

Print("=== GAP: Gamma Matrix Verification ===\n");

# Spacetime metric (signature +---)
g := [[1,0,0,0],[0,-1,0,0],[0,0,-1,0],[0,0,0,-1]] * One(1);

# Gamma matrices (Dirac representation)
gamma0 := [[1,0,0,0],[0,1,0,0],[0,0,-1,0],[0,0,0,-1]] * One(1);
gamma1 := [[0,0,0,1],[0,0,1,0],[0,-1,0,0],[-1,0,0,0]] * One(1);
gamma2 := [[0,0,0,-E(4)],[0,0,E(4),0],[0,E(4),0,0],[-E(4),0,0,0]] * One(1);
gamma3 := [[0,0,1,0],[0,0,0,-1],[-1,0,0,0],[0,1,0,0]] * One(1);

gammas := [gamma0, gamma1, gamma2, gamma3];

# Verify anticommutation
Print("\nVerifying anticommutation: g_mu g_nu + g_nu g_mu = 2*g_{mu,nu}\n");
all_ok := true;
for mu in [1..4] do
  for nu in [1..4] do
    anticomm := gammas[mu] * gammas[nu] + gammas[nu] * gammas[mu];
    expected := 2 * g[mu][nu] * IdentityMat(4,One(1));
    if anticomm <> expected then
      Print("FAIL: mu=",mu-1," nu=",nu-1,"\n");
      all_ok := false;
    fi;
  od;
od;

if all_ok then
  Print("✓ All 16 anticommutation relations verified\n");
fi;

# Verify squares
Print("\nGamma squares:\n");
Print("gamma0^2 = ", gamma0*gamma0 = IdentityMat(4,One(1)), "\n");
Print("gamma1^2 = ", gamma1*gamma1 = -IdentityMat(4,One(1)), "\n");
Print("gamma3^2 = ", gamma3*gamma3 = -IdentityMat(4,One(1)), "\n");

# Pseudoscalar
I_sta := gamma0 * gamma1 * gamma2 * gamma3;
I_sq := I_sta * I_sta;
Print("\nPseudoscalar I = g0g1g2g3\n");
Print("I^2 = -I_4? ", I_sq = -IdentityMat(4,One(1)), "\n");

# Spin bivector
sigma3 := gamma3 * gamma0;
Print("\nSpin bivector sigma3 = g3g0\n");
Print("sigma3^2 = ", sigma3*sigma3, "\n");

Print("\n✓ GAP verification complete\n");