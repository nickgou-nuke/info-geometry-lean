# Export the Borel witnesses needed by the native quotient transport.
# This script consumes the exact carrier and quotient enumeration owned by
# verify_g2_true_bruhat_cover.g; it introduces no alternate basis or action.

Read("scripts/verify_g2_true_bruhat_cover.g");

for k in [1..12] do
  for i in correctedOrbits[k] do
    witness := First(Elements(B), b -> b * correctedW[k] in Q[i]);
    if witness = fail then
      Error("orbit representative has no B-action witness");
    fi;
    rightWitness := (witness * correctedW[k])^-1 * Representative(Q[i]);
    if not rightWitness in B then
      Error("orbit representative has no right B factor");
    fi;
    Print("FLAG_CELL_LEFT_WITNESS_", k-1, "_", i-1, "=",
      ExtRepOfObj(Factorization(B, witness)), "\n");
    Print("FLAG_CELL_RIGHT_WITNESS_", k-1, "_", i-1, "=",
      ExtRepOfObj(Factorization(B, rightWitness)), "\n");
  od;
od;
