import InfoGeometry.SuperGrassmannian.TrialityAutomorphismMotive

/-!
# Clifford action equivariance under internal Zorn-axis cycling

The product-ring automorphisms on the three sector ring and their induced
maps on its additive Grothendieck completion are owned by
`TrialityAutomorphismMotive`.  This file proves the operator-level
compatibility of the internal cyclic Zorn-coordinate automorphism with both
typed Clifford actions.  It does not identify the product-ring completion
with projective-module algebraic `K₀`, or identify the internal axis cycle
with a full `Out(D₄)` action.
-/

noncomputable section

namespace InfoGeometry.SuperGrassmannian.TrialityCliffordAxisEquivariance

open CanonicalZornCompositionTriality
open InfoGeometry.Canonical.CanonicalZornTrialitySpinEquivariance
open CanonicalZornProjectiveTKKBridge
open InfoGeometry.Physics.SplitOctonionBraidSU3

/-- The internal Zorn-axis cycle intertwines with the typed action
`8ᵥ × 8ₛ → 8꜀`. -/
theorem cliffordPlus_axisCycle (V : Vector8) (S : SpinorPlus8) :
    cliffordPlus (vectorAxisCycle V) (spinorPlusAxisCycle S) =
      spinorMinusAxisCycle (cliffordPlus V S) := by
  apply ZornCopy.ext
  change zornMul (canonicalTriality V.val) (canonicalTriality S.val) =
    canonicalTriality (zornMul V.val S.val)
  exact (canonicalTriality_mul V.val S.val).symm

/-- The internal Zorn-axis cycle intertwines with the conjugate typed action
`8ᵥ × 8꜀ → 8ₛ`. -/
theorem cliffordMinus_axisCycle (V : Vector8) (C : SpinorMinus8) :
    cliffordMinus (vectorAxisCycle V) (spinorMinusAxisCycle C) =
      spinorPlusAxisCycle (cliffordMinus V C) := by
  apply ZornCopy.ext
  change zornMul (zornConj (canonicalTriality V.val))
      (canonicalTriality C.val) =
    canonicalTriality (zornMul (zornConj V.val) C.val)
  rw [← canonicalTriality_conj, ← canonicalTriality_mul]

end InfoGeometry.SuperGrassmannian.TrialityCliffordAxisEquivariance
