# GAP script for Madelung-Legendre Synthesis verification
Print("=== GAP: Madelung-Legendre Synthesis Verification ===\n");

# Define a 3x3 matrix K
K := [[1, 2, 3], [4, 5, 6], [7, 8, -6]]; # Trace is 1 + 5 - 6 = 0

tr_K := TraceMat(K);
Print("Trace of K: ", tr_K, "\n");

# Let's verify trace of beta * K
beta := 5;
u := beta * K;
tr_u := TraceMat(u);
Print("Trace of 5 * K: ", tr_u, "\n");

if tr_u = beta * tr_K then
  Print("Linearity of trace: trace(beta * K) = beta * trace(K) holds!\n");
else
  Error("Trace linearity failed!");
fi;

# Check that if trace(K) = 0, then for any beta, trace(beta * K) = 0
if tr_K = 0 then
  if tr_u = 0 then
    Print("Divergence-free flow is preserved under scaling!\n");
    Print("All GAP verifications passed!\n");
  else
    Error("Scaling preservation failed!");
  fi;
else
  Error("Setup trace(K) must be 0!");
fi;
