import InfoGeometry.OperatorAlgebra.PeirceSpine.EndomorphismCharge
/-!
# Axiom audit for the endomorphism charge results

## BUCKET 1 — Kernel-verified identities
This audit prints the dependencies of the owner theorems.

## BUCKET 2 — Conditional consequences
The printed results retain their owner hypotheses.

## BUCKET 3 — Open interpretation
The audit does not certify analytic or physical consequences.
-/
open InfoGeometry.OperatorAlgebra.PeirceSpine
#print axioms tripotent_comm_fifth
#print axioms endomorphismCharge_fifth
#print axioms endomorphismCharge_pow_apply
#print axioms chargeIter_fifth_of_linear
