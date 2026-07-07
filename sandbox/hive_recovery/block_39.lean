/-- 
A G₂ Automorphism of the Split-Octonions is a linear map that preserves 
the Zorn composition: f(mulZ X Y) = mulZ f(X) f(Y).
The Strong Force SU(3) gauge subgroup is precisely defined as the subgroup 
of G₂ automorphisms that leaves the idempotent trifactor OP1 strictly invariant.
-/
def IsSU3Automorphism (cp : ZornCompositionDatum R) (f : ZornMatrix R → ZornMatrix R) : Prop :=
  (∀ X Y, f (cp.mulZ X Y) = cp.mulZ (f X) (f Y)) ∧ 
  (f OP1 = OP1) ∧ 
  (f OP2 = OP2)