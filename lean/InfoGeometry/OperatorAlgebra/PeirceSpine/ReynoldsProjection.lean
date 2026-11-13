/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CommutingInvolutionProjection
import InfoGeometry.OperatorAlgebra.PeirceSpine.TetraktysKleinActionBridge
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Normalized Peirce averaging and its off-shell discrepancy

On `V = 1`, the existing four-word Klein average, divided by its scale,
is a genuine real linear projection onto the common centralizer of `Phi`
and the Peirce parity involution. The proof holds on the full operator
algebra, with no finite-dimensional or scalar reduction.

Before specialization, the homogenized commutator channel differs from
the Fourier channel by an explicit noncommutative residual. The weighted
sum from the intake is also compared with the existing Fourier channel;
it does not have the spectrum claimed in the intake.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P)

include hP in
/-- The exact residual on arbitrary ambient inputs; `V` is not assumed
central in the ambient ring. -/
theorem hProjV_sub_fourierV (A C X : B) :
    hProjV P A C X - fourierV P A C X =
      (3 : ℤ) • (genV P A C * comm (genV P A C) X) +
        comm (genV P A C) X * genV P A C := by
  rw [hProjV_expansion hP]
  simp only [fourierV, grpId, grpPhi, grpJ, grpSig, comm]
  noncomm_ring

include hP in
/-- Agreement is valid on the centralizer of `V`. -/
theorem hProjV_eq_fourierV_of_commute (A C X : B)
    (hVX : Commute (genV P A C) X) :
    hProjV P A C X = fourierV P A C X := by
  apply sub_eq_zero.mp
  rw [hProjV_sub_fourierV hP]
  simp [comm, hVX.eq]

/-- The weighted sandwich expression as written in the supplied intake. -/
def weightedSandwichSum (P A C X : B) : B :=
  (2 : ℤ) • ((genV P A C * genV P A C) * X) +
    genV P A C * (genPhi P A C * X * genPhi P A C -
      genJ P A C * X * genJ P A C) + genSig P A C * X * genSig P A C

/-- A division-free comparison identifies the extra identity channel. -/
theorem twice_weightedSandwichSum (P A C X : B) :
    (2 : ℤ) • weightedSandwichSum P A C X =
      fourierV P A C X + (2 : ℤ) • grpId P A C X := by
  simp only [weightedSandwichSum, fourierV, grpId, grpPhi, grpJ, grpSig]
  noncomm_ring

include hP in
theorem weightedSandwichSum_genV (A C : B) :
    weightedSandwichSum P A C (genV P A C) =
      (5 : ℤ) • (genV P A C * genV P A C * genV P A C) := by
  simp only [weightedSandwichSum]
  peirce_nf hP

include hP in
theorem weightedSandwichSum_genPhi (A C : B) :
    weightedSandwichSum P A C (genPhi P A C) =
      genV P A C * genV P A C * genPhi P A C := by
  simp only [weightedSandwichSum]
  peirce_nf hP

include hP in
theorem weightedSandwichSum_genJ (A C : B) :
    weightedSandwichSum P A C (genJ P A C) =
      genV P A C * genV P A C * genJ P A C := by
  simp only [weightedSandwichSum]
  peirce_nf hP

include hP in
theorem weightedSandwichSum_genSig (A C : B) :
    weightedSandwichSum P A C (genSig P A C) =
      genV P A C * genV P A C * genSig P A C := by
  simp only [weightedSandwichSum]
  peirce_nf hP

section RealLinear

variable [Algebra ℝ B]

noncomputable section

/-- Ordered two-sided multiplication, as a native real linear map. -/
def sandwichLinearMap (s t : B) : B →ₗ[ℝ] B where
  toFun x := s * x * t
  map_add' x y := by simp [mul_add, add_mul]
  map_smul' r x := by simp [mul_smul_comm, smul_mul_assoc]

theorem sandwichLinearMap_fixed_iff (s : B) (hs : s * s = 1) (x : B) :
    sandwichLinearMap s s x = x ↔ s * x = x * s := by
  constructor
  · intro hx
    have h := congrArg (fun y : B => y * s) hx
    change (s * x * s) * s = x * s at h
    simpa only [mul_assoc, hs, mul_one] using h
  · intro hx
    change s * x * s = x
    rw [hx, mul_assoc, hs, mul_one]

/-- The normalized projection associated to the two existing conjugations. -/
def reynoldsProjection (P A C : B) : B →ₗ[ℝ] B :=
  InfoGeometry.Algebra.CommutingInvolutionProjection.average
    (sandwichLinearMap (genPhi P A C) (genPhi P A C))
    (sandwichLinearMap (invS P) (invS P))

include hP in
/-- On the unit shell, normalization produces an idempotent endomorphism. -/
theorem reynoldsProjection_isIdempotentElem (A C : B)
    (hV : genV P A C = 1) : IsIdempotentElem (reynoldsProjection P A C) := by
  apply InfoGeometry.Algebra.CommutingInvolutionProjection.average_isIdempotentElem
  · exact phiUnitSquareEquiv_involutive hP A C hV
  · intro x
    exact (parityConj_involutive_ring_action hP x 1).1
  · intro x
    exact phiUnitSquareEquiv_commutes_parity hP A C hV x

include hP in
/-- The output space is the full common centralizer, rather than a list of
four checked generator values. -/
theorem range_reynoldsProjection (A C : B) (hV : genV P A C = 1) :
    LinearMap.range (reynoldsProjection P A C) =
      (Subalgebra.centralizer ℝ ({genPhi P A C, invS P} : Set B)).toSubmodule := by
  have hPhi : genPhi P A C * genPhi P A C = 1 :=
    (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.1.trans hV
  have hS : invS P * invS P = 1 :=
    (archetype_A2_peirce_cartan_grading_and_tangent_closure hP A C).1
  rw [reynoldsProjection,
    InfoGeometry.Algebra.CommutingInvolutionProjection.range_average
      (sandwichLinearMap (genPhi P A C) (genPhi P A C))
      (sandwichLinearMap (invS P) (invS P))
      (fun x => phiUnitSquareEquiv_involutive hP A C hV x)
      (fun x => (parityConj_involutive_ring_action hP x 1).1)
      (fun x => phiUnitSquareEquiv_commutes_parity hP A C hV x)]
  ext x
  change x ∈ InfoGeometry.Algebra.CommutingInvolutionProjection.jointFixed _ _ ↔
    x ∈ Subalgebra.centralizer ℝ ({genPhi P A C, invS P} : Set B)
  rw [InfoGeometry.Algebra.CommutingInvolutionProjection.mem_jointFixed_iff,
    sandwichLinearMap_fixed_iff _ hPhi, sandwichLinearMap_fixed_iff _ hS,
    Subalgebra.mem_centralizer_iff]
  simp

include hP in
/-- The normalized linear projection is exactly the existing Fourier channel
divided by eight, on every ambient operator. -/
theorem reynoldsProjection_eq_fourierV (A C X : B) (hV : genV P A C = 1) :
    reynoldsProjection P A C X = (1 / 8 : ℝ) • fourierV P A C X := by
  obtain ⟨hi, hphi, hj, hs⟩ :=
    tetraktys_sandwich_channels_are_peirce_klein_action hP A C hV X
  rw [fourierV, hi, hphi, hj, hs]
  change (1 / 4 : ℝ) •
      (X + genPhi P A C * X * genPhi P A C + invS P * X * invS P +
        genPhi P A C * (invS P * X * invS P) * genPhi P A C) =
    (1 / 8 : ℝ) • ((2 : ℤ) •
      (X + genPhi P A C * X * genPhi P A C +
        genPhi P A C * (invS P * X * invS P) * genPhi P A C +
        invS P * X * invS P))
  simp only [two_smul]
  module

include hP in
/-- The same normalization applies to the homogenized channel on `V = 1`. -/
theorem reynoldsProjection_eq_hProjV (A C X : B) (hV : genV P A C = 1) :
    reynoldsProjection P A C X = (1 / 8 : ℝ) • hProjV P A C X := by
  rw [hProjV_eq_fourierV_of_commute hP A C X (by rw [hV]; exact Commute.one_left X)]
  exact reynoldsProjection_eq_fourierV hP A C X hV

end
end RealLinear

end InfoGeometry.OperatorAlgebra.PeirceSpine
