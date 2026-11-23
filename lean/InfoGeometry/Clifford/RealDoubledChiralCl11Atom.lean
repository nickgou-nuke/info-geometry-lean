/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinComplements
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinPhaseReal
import InfoGeometry.Algebra.GradedNullconeAlgebra

/-!
# Real doubled chiral Cl(1,1) atom

This owner records the two opposite Peirce blocks of the mirror symmetry and
the four exact products of the chiral grading with the complex structure.
All statements are theorem-backed on the existing real doubled carrier.
-/

noncomputable section

set_option linter.unusedSectionVars false

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein

namespace InfoGeometry.Clifford.RealDoubledChiralCl11Atom

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev leftProj : EndH₂ (E := E) := leftChiralProjector (E := E)
abbrev rightProj : EndH₂ (E := E) := rightChiralProjector (E := E)
abbrev mirror : EndH₂ (E := E) := etaChiral (E := E)
abbrev phase : EndH₂ (E := E) := chiralComplexStructure (E := E)

def downOp : EndH₂ (E := E) :=
  (leftProj E).comp ((mirror E).comp (rightProj E))

def upOp : EndH₂ (E := E) :=
  (rightProj E).comp ((mirror E).comp (leftProj E))

theorem downOp_sq : (downOp E).comp (downOp E) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [downOp, leftProj, rightProj, mirror, leftChiralProjector,
      rightChiralProjector, etaChiral, gamma5, spectral_epsilon, modular_j,
      one_div, sub_eq_add_neg]
  module

theorem upOp_sq : (upOp E).comp (upOp E) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [upOp, leftProj, rightProj, mirror, leftChiralProjector,
      rightChiralProjector, etaChiral, gamma5, spectral_epsilon, modular_j,
      one_div, sub_eq_add_neg]
  module

theorem downOp_upOp : (downOp E).comp (upOp E) = leftProj E := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [downOp, upOp, leftProj, rightProj, mirror, leftChiralProjector,
      rightChiralProjector, etaChiral, gamma5, spectral_epsilon, modular_j,
      one_div, sub_eq_add_neg]
  module

theorem upOp_downOp : (upOp E).comp (downOp E) = rightProj E := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [downOp, upOp, leftProj, rightProj, mirror, leftChiralProjector,
      rightChiralProjector, etaChiral, gamma5, spectral_epsilon, modular_j,
      one_div, sub_eq_add_neg]
  module

theorem downOp_add_upOp : downOp E + upOp E = mirror E := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [downOp, upOp, leftProj, rightProj, mirror,
      leftChiralProjector, rightChiralProjector, etaChiral, gamma5,
      spectral_epsilon, modular_j, one_div, sub_eq_add_neg] <;> module

theorem mirror_phase : (mirror E).comp (phase E) = gamma5 (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [mirror, phase, chiralComplexStructure, gamma5, etaChiral,
      spectral_epsilon, modular_j]

theorem phase_mirror : (phase E).comp (mirror E) = -(gamma5 (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [mirror, phase, chiralComplexStructure, gamma5, etaChiral,
      spectral_epsilon, modular_j]

theorem gamma5_phase : (gamma5 (E := E)).comp (phase E) = -(mirror E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [mirror, phase, chiralComplexStructure, gamma5, etaChiral,
      spectral_epsilon, modular_j]

theorem phase_gamma5 : (phase E).comp (gamma5 (E := E)) = mirror E := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [mirror, phase, chiralComplexStructure, gamma5, etaChiral,
      spectral_epsilon, modular_j]

open InfoGeometry.Algebra.GradedNullconeAlgebra

/-- In the operator ring `EndH₂ (E := E)`, `γ₅ * γ₅ = 1`. -/
theorem gamma5_mul_self :
    (gamma5 (E := E)) * (gamma5 (E := E)) = (1 : EndH₂ (E := E)) :=
  gamma5_involution (E := E)

/-- Chiral parity conjugation `α(A) = γ₅ * A * γ₅` on `EndH₂ (E := E)`. -/
def chiralParityConj (A : EndH₂ (E := E)) : EndH₂ (E := E) :=
  parityConj (gamma5 (E := E)) A

/-- Curved `ℤ/2`-graded differential `∂_F(A) = F * A - (γ₅ * A * γ₅) * F` on `EndH₂ (E := E)`. -/
def chiralCurvedDiff (F A : EndH₂ (E := E)) : EndH₂ (E := E) :=
  gradedInnerDiff (gamma5 (E := E)) F A

/-- Block-diagonal operators on `H₂ = E ⊕ E` are fixed by `chiralParityConj`. -/
theorem chiralParityConj_of_isBlockDiagonal {X : EndH₂ (E := E)}
    (hX : IsBlockDiagonal X) :
    chiralParityConj E X = X := by
  dsimp [chiralParityConj, parityConj]
  have hcomm : X * gamma5 (E := E) = gamma5 (E := E) * X := hX
  calc
    gamma5 (E := E) * X * gamma5 (E := E)
        = gamma5 (E := E) * (X * gamma5 (E := E)) := by rw [mul_assoc]
    _ = gamma5 (E := E) * (gamma5 (E := E) * X) := by rw [hcomm]
    _ = (gamma5 (E := E) * gamma5 (E := E)) * X := by rw [← mul_assoc]
    _ = 1 * X := by rw [gamma5_mul_self E]
    _ = X := one_mul X

/-- Off-block-diagonal operators on `H₂ = E ⊕ E` are negated by `chiralParityConj`. -/
theorem chiralParityConj_of_isOffBlockDiagonal {F : EndH₂ (E := E)}
    (hF : IsOffBlockDiagonal F) :
    chiralParityConj E F = -F := by
  dsimp [chiralParityConj, parityConj]
  have hanti : F * gamma5 (E := E) = -(gamma5 (E := E) * F) := hF
  calc
    gamma5 (E := E) * F * gamma5 (E := E)
        = gamma5 (E := E) * (F * gamma5 (E := E)) := by rw [mul_assoc]
    _ = gamma5 (E := E) * -(gamma5 (E := E) * F) := by rw [hanti]
    _ = -((gamma5 (E := E) * gamma5 (E := E)) * F) := by
      apply ContinuousLinearMap.ext
      intro u
      simp
    _ = -(1 * F) := by rw [gamma5_mul_self E]
    _ = -F := by rw [one_mul]

/-- Every off-block operator `F ∈ EndH₂` generates a curved `ℤ/2`-graded DG differential
satisfying the graded Leibniz rule, `∂_F²(A) = [F², A]`, Bianchi identity `∂_F(F²) = 0`,
and centrality criterion `∂_F² = 0 ↔ F² ∈ Z(EndH₂)`. -/
theorem chiralCurvedDiff_leibniz_sq_and_bianchi {F : EndH₂ (E := E)}
    (hF : IsOffBlockDiagonal F) (A B : EndH₂ (E := E)) :
    (chiralCurvedDiff E F (A * B) =
      chiralCurvedDiff E F A * B + chiralParityConj E A * chiralCurvedDiff E F B) ∧
    (chiralCurvedDiff E F (chiralCurvedDiff E F A) = (F * F) * A - A * (F * F)) ∧
    (chiralCurvedDiff E F (F * F) = 0) ∧
    ((∀ X : EndH₂ (E := E), chiralCurvedDiff E F (chiralCurvedDiff E F X) = 0) ↔
      (∀ X : EndH₂ (E := E), (F * F) * X = X * (F * F))) := by
  have hodd : parityConj (gamma5 (E := E)) F = -F :=
    chiralParityConj_of_isOffBlockDiagonal E hF
  exact ⟨gradedInnerDiff_mul (gamma5_mul_self E) F A B,
    gradedInnerDiff_sq (gamma5_mul_self E) hodd A,
    gradedInnerDiff_curvature_closed (gamma5_mul_self E) hodd,
    gradedInnerDiff_sq_eq_zero_iff_central (gamma5_mul_self E) hodd⟩

/-- Both opposite Peirce blocks `downOp` and `upOp` are off-block-diagonal (`γ₅`-odd). -/
theorem downOp_and_upOp_isOffBlockDiagonal :
    IsOffBlockDiagonal (downOp E) ∧ IsOffBlockDiagonal (upOp E) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;>
      simp [downOp, leftProj, rightProj, mirror,
        leftChiralProjector, rightChiralProjector, etaChiral, gamma5,
        spectral_epsilon, modular_j, one_div, sub_eq_add_neg]
  · apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;>
      simp [upOp, leftProj, rightProj, mirror,
        leftChiralProjector, rightChiralProjector, etaChiral, gamma5,
        spectral_epsilon, modular_j, one_div, sub_eq_add_neg]

/-- In the unilateral nilpotent regime (`downOp` or `upOp`), the curved differential on `EndH₂`
is strictly square-zero (`∂² = 0`). -/
theorem chiralCurvedDiff_downOp_and_upOp_sq_zero (A : EndH₂ (E := E)) :
    chiralCurvedDiff E (downOp E) (chiralCurvedDiff E (downOp E) A) = 0 ∧
    chiralCurvedDiff E (upOp E) (chiralCurvedDiff E (upOp E) A) = 0 := by
  rcases downOp_and_upOp_isOffBlockDiagonal E with ⟨hd, hu⟩
  have hd2 : downOp E * downOp E = 0 := downOp_sq E
  have hu2 : upOp E * upOp E = 0 := upOp_sq E
  constructor
  · rw [(chiralCurvedDiff_leibniz_sq_and_bianchi E hd A 1).2.1, hd2, zero_mul, mul_zero, sub_self]
  · rw [(chiralCurvedDiff_leibniz_sq_and_bianchi E hu A 1).2.1, hu2, zero_mul, mul_zero, sub_self]

end InfoGeometry.Clifford.RealDoubledChiralCl11Atom
