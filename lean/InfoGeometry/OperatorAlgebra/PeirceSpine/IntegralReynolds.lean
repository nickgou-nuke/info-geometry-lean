/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import Mathlib.Tactic.Module

/-!
# The integral four-sandwich Reynolds operator

For an idempotent `P` in an arbitrary associative ring, the existing Peirce
generators give the additive operator

`K X = V² X + V (Φ X Φ - J X J) + Σ X Σ`.

The existing Fourier mass channel is `2 K`. This file retains the integral
normalization: no inverse of `2`, `V`, or `4 V²` is assumed. Its main identity
is `K (K X) = 4 V² K X` on the centralizer of `V`. An explicit commutator
defect records what changes on the full ambient ring. The same centralizer
condition gives absorption of the scale-two parity sum.

The generator evaluations do not assert that `1, P, N₊, N₋` are linearly
independent in an arbitrary realization, nor that the image is the scalar
center of the ambient ring.
-/

set_option autoImplicit false

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The sum of the four existing group-sandwich channels, bundled as an
additive endomorphism. The definition requires no idempotency hypothesis. -/
def integralReynolds (P A C : B) : B →+ B where
  toFun X := grpId P A C X + grpPhi P A C X + grpJ P A C X + grpSig P A C X
  map_zero' := by
    simp only [grpId, grpPhi, grpJ, grpSig, mul_zero, zero_mul, neg_zero, add_zero]
  map_add' X Y := by
    simp only [grpId, grpPhi, grpJ, grpSig, mul_add, add_mul, neg_add_rev]
    abel

@[simp]
theorem integralReynolds_apply (P A C X : B) :
    integralReynolds P A C X =
      grpId P A C X + grpPhi P A C X + grpJ P A C X + grpSig P A C X := rfl

/-- The ordered sandwich formula for the integral operator. -/
theorem integralReynolds_eq_sandwich (P A C X : B) :
    integralReynolds P A C X =
      genV P A C ^ 2 * X +
        genV P A C * (genPhi P A C * X * genPhi P A C -
          genJ P A C * X * genJ P A C) +
        genSig P A C * X * genSig P A C := by
  simp only [integralReynolds_apply, grpId, grpPhi, grpJ, grpSig, pow_two,
    mul_sub]
  abel

/-- The Fourier owner uses twice the integral four-sandwich sum. -/
theorem fourierV_eq_two_integralReynolds (P A C X : B) :
    fourierV P A C X = (2 : ℤ) • integralReynolds P A C X := rfl

section Idempotent

variable {P : B} (hP : P * P = P)
include hP

/-- Left multiplication by the mass commutes with the integral operator. -/
theorem integralReynolds_mass_mul (A C X : B) :
    integralReynolds P A C (genV P A C * X) =
      genV P A C * integralReynolds P A C X := by
  simp only [integralReynolds_apply, grpId, grpPhi, grpJ, grpSig]
  peirce_nf hP

/-- Right multiplication by the mass also commutes with the integral operator. -/
theorem integralReynolds_mul_mass (A C X : B) :
    integralReynolds P A C (X * genV P A C) =
      integralReynolds P A C X * genV P A C := by
  simp only [integralReynolds_apply, grpId, grpPhi, grpJ, grpSig]
  peirce_nf hP

/-- The mass centralizer is invariant under the integral operator. -/
theorem integralReynolds_commute_mass (A C X : B)
    (hVX : Commute (genV P A C) X) :
    Commute (genV P A C) (integralReynolds P A C X) := by
  change genV P A C * integralReynolds P A C X =
    integralReynolds P A C X * genV P A C
  rw [← integralReynolds_mass_mul hP A C X, hVX.eq,
    integralReynolds_mul_mass hP A C X]

/-- The exact ambient composition defect. Every correction factors through
`comm X V`, so the centralizer hypothesis in the next theorem has an explicit
algebraic role. No cancellation by an integer or by `V` is used. -/
theorem integralReynolds_comp_defect (A C X : B) :
    integralReynolds P A C (integralReynolds P A C X) -
        (4 : ℤ) • ((genV P A C * genV P A C) * integralReynolds P A C X) =
      (genV P A C * genV P A C) *
        (comm X (genV P A C) * genV P A C +
          (3 : ℤ) • (genV P A C * comm X (genV P A C)) +
          (2 : ℤ) •
            (genPhi P A C * comm X (genV P A C) * genPhi P A C -
              genJ P A C * comm X (genV P A C) * genJ P A C)) := by
  simp only [integralReynolds_apply, grpId, grpPhi, grpJ, grpSig]
  peirce_nf hP

/-- On the mass centralizer, composing the integral operator with itself
multiplies its output by `4 V²`. This is a scaled idempotence law, without
assuming that its operator-valued scale is invertible. -/
theorem integralReynolds_comp_of_commute (A C X : B)
    (hVX : Commute (genV P A C) X) :
    integralReynolds P A C (integralReynolds P A C X) =
      (4 : ℤ) • ((genV P A C * genV P A C) * integralReynolds P A C X) := by
  have hcomm : comm X (genV P A C) = 0 := sub_eq_zero.mpr hVX.eq.symm
  apply sub_eq_zero.mp
  rw [integralReynolds_comp_defect hP A C X]
  simp only [hcomm, mul_zero, zero_mul, smul_zero, sub_self, add_zero]

/-- The existing Fourier normalization has scale eight on the same domain.
The factor two multiplies the whole four-sandwich operator. -/
theorem fourierV_comp_of_commute (A C X : B)
    (hVX : Commute (genV P A C) X) :
    fourierV P A C (fourierV P A C X) =
      (8 : ℤ) • ((genV P A C * genV P A C) * fourierV P A C X) := by
  simp only [fourierV_eq_two_integralReynolds, map_zsmul,
    integralReynolds_comp_of_commute hP A C X hVX, mul_smul_comm]
  module

/-- The first generator has the unnormalized scale `4 V²`. -/
theorem integralReynolds_one (A C : B) :
    integralReynolds P A C 1 = (4 : ℤ) • (genV P A C * genV P A C) := by
  simp only [integralReynolds_apply, grpId, grpPhi, grpJ, grpSig]
  peirce_nf hP

/-- The cut has the unnormalized scale `2 V²`. In particular, the integral
operator is not claimed to hit the whole scalar coefficient ring. -/
theorem integralReynolds_cut (A C : B) :
    integralReynolds P A C P = (2 : ℤ) • (genV P A C * genV P A C) := by
  simp only [integralReynolds_apply, grpId, grpPhi, grpJ, grpSig]
  peirce_nf hP

/-- The integral operator annihilates the upper Peirce generator. -/
theorem integralReynolds_conePlus (A C : B) :
    integralReynolds P A C (conePlus P A) = 0 := by
  simp only [integralReynolds_apply, grpId, grpPhi, grpJ, grpSig]
  peirce_nf hP

/-- The integral operator annihilates the lower Peirce generator. -/
theorem integralReynolds_coneMinus (A C : B) :
    integralReynolds P A C (coneMinus P C) = 0 := by
  simp only [integralReynolds_apply, grpId, grpPhi, grpJ, grpSig]
  peirce_nf hP

/-- On integer linear combinations of the four generators, the output is
an even integer multiple of `V²`. This is an evaluation formula, not a basis
or freeness assertion. -/
theorem integralReynolds_four_generator_zsmul (A C : B) (a b c d : ℤ) :
    integralReynolds P A C
        (a • (1 : B) + b • P + c • conePlus P A + d • coneMinus P C) =
      (4 * a + 2 * b) • (genV P A C * genV P A C) := by
  rw [map_add, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, map_zsmul,
    integralReynolds_one hP, integralReynolds_cut hP,
    integralReynolds_conePlus hP, integralReynolds_coneMinus hP]
  simp only [smul_zero, add_zero]
  module

/-- Conjugation by the Peirce sign intertwines the integral operator on all
ambient inputs, before any mass-centralizer hypothesis is imposed. -/
theorem integralReynolds_parity_covariant (A C X : B) :
    invS P * integralReynolds P A C X * invS P =
      integralReynolds P A C (invS P * X * invS P) := by
  simp only [integralReynolds_apply, grpId, grpPhi, grpJ, grpSig]
  peirce_nf hP

/-- The exact defect of invariance under parity conjugation. -/
theorem integralReynolds_parity_defect (A C X : B) :
    integralReynolds P A C (invS P * X * invS P) - integralReynolds P A C X =
      genV P A C * comm X (genV P A C) -
        invS P * (genV P A C * comm X (genV P A C)) * invS P := by
  simp only [integralReynolds_apply, grpId, grpPhi, grpJ, grpSig]
  peirce_nf hP

/-- On the mass centralizer, parity conjugation does not change the output. -/
theorem integralReynolds_parity_of_commute (A C X : B)
    (hVX : Commute (genV P A C) X) :
    integralReynolds P A C (invS P * X * invS P) = integralReynolds P A C X := by
  have hcomm : comm X (genV P A C) = 0 := sub_eq_zero.mpr hVX.eq.symm
  apply sub_eq_zero.mp
  rw [integralReynolds_parity_defect hP A C X]
  simp only [hcomm, mul_zero, zero_mul, sub_self]

/-- The scale-two pinching sum is absorbed by `K`, with its scale retained. -/
theorem integralReynolds_pinching_of_commute (A C X : B)
    (hVX : Commute (genV P A C) X) :
    integralReynolds P A C (X + invS P * X * invS P) =
      (2 : ℤ) • integralReynolds P A C X := by
  rw [map_add, integralReynolds_parity_of_commute hP A C X hVX]
  abel

/-- The same absorption law holds when the parity sum is applied after `K`. -/
theorem pinching_integralReynolds_of_commute (A C X : B)
    (hVX : Commute (genV P A C) X) :
    integralReynolds P A C X + invS P * integralReynolds P A C X * invS P =
      (2 : ℤ) • integralReynolds P A C X := by
  rw [integralReynolds_parity_covariant hP A C X,
    integralReynolds_parity_of_commute hP A C X hVX]
  abel

end Idempotent

end InfoGeometry.OperatorAlgebra.PeirceSpine
