/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.CayleyKernelRegularity

/-!
# Universal Peirce defect identities

The identities are polynomial equations in an arbitrary associative ring.
No implication from a nonzero defect to absence of particular adjoint
eigenvectors is asserted. Numerical weights need not remain distinct in
positive characteristic.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The parity square defect is four times the metric idempotence defect. -/
theorem parity_square_defect (V : B) :
    ((2 : ℤ) • V - 1) * ((2 : ℤ) • V - 1) - 1 =
      (4 : ℤ) • (V * V - V) := by
  simp only [show (4 : ℤ) = 2 + 2 by decide, add_smul, two_smul]
  noncomm_ring

/-- The elementary dyadic inverse formula has exactly the same defect. -/
theorem shifted_dyadic_defect (V : B) :
    (1 + V) * (2 - V) - 2 = -(V * V - V) := by noncomm_ring

/-- The signed cycle has a universal cubic defect, before imposing on-shell equations. -/
theorem genSig_cubic_defect {P : B} (hP : P * P = P) (A C : B) :
    genSig P A C * genSig P A C * genSig P A C - genSig P A C =
      (genV P A C * genV P A C - 1) * genSig P A C := by peirce_nf hP

/-- The integral numerator and its opposite have the metric defect as their norm defect. -/
theorem integral_numerator_defects {P : B} (hP : P * P = P) (A C : B) :
    (1 - genV P A C - genJ P A C) * (1 - genV P A C + genJ P A C) - 1 =
        genV P A C * genV P A C - genV P A C ∧
      (1 - genV P A C + genJ P A C) * (1 - genV P A C - genJ P A C) - 1 =
        genV P A C * genV P A C - genV P A C := by
  constructor <;> peirce_nf hP

/-- On shell the integral numerator anticommutes with the actual signed cycle. -/
theorem onShell_integral_numerator_anticommutes {P : B} (hP : P * P = P) (A C : B)
    (hV : genV P A C * genV P A C = genV P A C) :
    (1 - genV P A C + genJ P A C) * genSig P A C =
      -(genSig P A C * (1 - genV P A C + genJ P A C)) := by
  obtain ⟨hpp, hmm⟩ := (genV_idempotent_iff_qgt_idempotent hP A C).mp hV
  obtain ⟨hpm, hmp⟩ := qgt_cycles_orthogonal hP A C
  have hl : (1 - genV P A C) * genSig P A C = 0 := by
    change (1 - (qgtPlus P A C + qgtMinus P A C)) *
      (qgtPlus P A C - qgtMinus P A C) = 0
    noncomm_ring [hpp, hmm, hpm, hmp]
  have hr : genSig P A C * (1 - genV P A C) = 0 := by
    change (qgtPlus P A C - qgtMinus P A C) *
      (1 - (qgtPlus P A C + qgtMinus P A C)) = 0
    noncomm_ring [hpp, hmm, hpm, hmp]
  have hj : genJ P A C * genSig P A C = -(genSig P A C * genJ P A C) := by
    peirce_nf hP
  rw [add_mul, hl, zero_add, mul_add, hr, zero_add, hj]

section Star

variable [StarRing B]

/-- Both on-shell unitary identities hold for the denominator-free integral numerator. -/
theorem onShell_integral_numerator_unitary {P : B} (hP : P * P = P)
    (hPs : star P = P) (A : B)
    (hV : genV P A (star A) * genV P A (star A) = genV P A (star A)) :
    let u := 1 - genV P A (star A) + genJ P A (star A)
    star u * u = 1 ∧ u * star u = 1 := by
  dsimp only
  have hs : star (1 - genV P A (star A) + genJ P A (star A)) =
      1 - genV P A (star A) - genJ P A (star A) := by
    simp only [star_add, star_sub, star_one, star_genV hPs, star_genJ hPs,
      sub_eq_add_neg]
  rw [hs]
  obtain ⟨hl, hr⟩ := integral_numerator_defects hP A (star A)
  rw [hV, sub_self] at hl hr
  exact ⟨sub_eq_zero.mp hl, sub_eq_zero.mp hr⟩

/-- The denominator-free integral unitary reverses the actual signed cycle. -/
theorem onShell_integral_numerator_reverses {P : B} (hP : P * P = P)
    (hPs : star P = P) (A : B)
    (hV : genV P A (star A) * genV P A (star A) = genV P A (star A)) :
    let u := 1 - genV P A (star A) + genJ P A (star A)
    u * genSig P A (star A) * star u = -genSig P A (star A) := by
  have hu := (onShell_integral_numerator_unitary hP hPs A hV).2
  dsimp only at hu ⊢
  rw [onShell_integral_numerator_anticommutes hP A (star A) hV,
    neg_mul, mul_assoc, hu, mul_one]

end Star

end InfoGeometry.OperatorAlgebra.PeirceSpine
