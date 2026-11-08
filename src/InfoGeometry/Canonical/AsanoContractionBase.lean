import InfoGeometry.Canonical.LeeYangAsanoDigest
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-
# InfoGeometry.Canonical.AsanoContractionBase

Base theorem surface for the Asano contraction lane.

This file promotes the two-variable Asano root-transfer step to a canonical,
kernel-checked theorem surface so the repeated-contraction induction can target
it directly.
-/

noncomputable section

namespace InfoGeometry.Canonical.AsanoContractionBase

open InfoGeometry.Canonical.LeeYangAsanoDigest

/--
Base Asano contraction step.

If the two-variable affine polynomial satisfies the determinant-zero transfer
hypotheses, then every contracted root lands in the Asano forbidden set.
-/
theorem asano_repeated_contraction_base
    (P : TwoVarAffinePolynomial)
    (K1 K2 : Set ℂ)
    (hD : P.D ≠ 0)
    (hDet : P.A * P.D - P.B * P.C = 0)
    (hRoots : ∀ z1 z2 : ℂ, P.eval z1 z2 = 0 → z1 ∈ K1 ∧ z2 ∈ K2) :
    ∀ z : ℂ, P.contract z = 0 → (-z) ∈ TwoVarAffinePolynomial.setMul K1 K2 := by
  intro z hz
  exact P.asano_case2_zero_transfer K1 K2 hD hDet hRoots z hz

end InfoGeometry.Canonical.AsanoContractionBase
