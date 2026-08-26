# Export the Borel witnesses needed by the native quotient transport.
# This script consumes the exact carrier and quotient enumeration owned by
# verify_g2_true_bruhat_cover.g; it introduces no alternate basis or action.

Read("scripts/verify_g2_true_bruhat_cover.g");
Read("scripts/generated_g2_lean_flag_words.g");

flagWordGens := Concatenation(pcgens, [s, correctedT]);
leanRepresentative := function(i)
  return Product(List(leanFlagWords[i], t -> flagWordGens[t[1]]^t[2]));
end;

fixedPCExtRep := function(M)
  local mask, bits, candidate, i, out;
  # Exact image test for Lean's canonical pcWord.  Its matrix is the
  # anti-hom image p5*p4*...*p0, so GAP normal-form coordinates must not be
  # copied or merely list-reversed.
  for mask in [0..63] do
    bits := List([1..6], i -> (QuoInt(mask, 2^(i-1)) mod 2) = 1);
    candidate := IdentityMat(8, F);
    for i in [6,5..1] do
      if bits[i] then candidate := candidate * pcgens[i]; fi;
    od;
    if candidate = M then
      out := [];
      for i in [1..6] do
        if bits[i] then Add(out, [i, 1]); fi;
      od;
      return Concatenation(out);
    fi;
  od;
  Error("witness matrix has no exact Lean pcWord image");
end;

for k in [1..12] do
  for i in correctedOrbits[k] do
    witness := First(Elements(B), b ->
      ((b * correctedW[k])^-1 * leanRepresentative(i)) in B);
    if witness = fail then
      Error("orbit representative has no B-action witness");
    fi;
    rightWitness := (witness * correctedW[k])^-1 * leanRepresentative(i);
    if not rightWitness in B then
      Error("orbit representative has no right B factor");
    fi;
    # The Lean carrier is anti-homomorphic.  GAP's equation is
    # witness * W * rightWitness = target, while Lean reads the matrix of
    # left * W * right in reverse.  Therefore the Lean factors are swapped.
    Print("FLAG_CELL_LEFT_WITNESS_", k-1, "_", i-1, "=",
      fixedPCExtRep(rightWitness), "\n");
    Print("FLAG_CELL_RIGHT_WITNESS_", k-1, "_", i-1, "=",
      fixedPCExtRep(witness), "\n");
  od;
od;
