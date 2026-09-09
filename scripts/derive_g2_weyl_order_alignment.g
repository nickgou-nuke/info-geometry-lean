# Explicit order/coset alignment diagnostic for the Lean and corrected Weyl lists.
# This is evidence for witness regeneration, not a Lean theorem.
Read("scripts/verify_g2_true_bruhat_cover.g");

for j in [1..12] do
  leanPos := PositionProperty(Q, q -> leanW[j] in q);
  correctedPos := PositionProperty(Q, q -> correctedW[j] in q);
  if leanPos = fail or correctedPos = fail then
    Error("Weyl representative is outside the enumerated quotient");
  fi;
  Print("WEYL_ALIGNMENT_", j-1, "=lean_coset:", leanPos,
    ",corrected_coset:", correctedPos, "\n");
od;

Print("WEYL_ALIGNMENT_CERTIFICATE=PASS\n");
