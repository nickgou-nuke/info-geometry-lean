/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Dirac-Hodge Coupling on the Hestenes-Krein Doubled Space

The Hestenes-Krein doubled space `DoubledSpace E = E × E` carries the
canonical operators:
  J : (x,ξ) ↦ (ξ,x)   — modular conjugation (swap)
  ε : (x,ξ) ↦ (x,-ξ)  — fundamental symmetry (sign flip on ghost)
  K = J ∘ ε           — clock axis / complex structure

On this space, a Dirac-Hodge pair is any continuous linear operator `S_left`
and its Hodge dual `S_right = J ∘ S_left ∘ J`. The conjugation statement is
proved below. Range projections and trace readouts require an additional
finite-dimensional carrier and are deliberately not introduced here.

## Genuine Theorems (all proved)

1. J² = I, ε² = I                    (involutions — in DoubledSpace)
2. J·ε = -ε·J                        (anticommutation — in DoubledSpace)
3. K² = -I                           (complex structure)
4. J·K·J = -K                        (Legendre flip: Hodge star = -K)
5. J-conjugation preserves the isometry property of `S_left`.

The former range-projection and trace claims are not consequences of the
present infinite-dimensional `DoubledSpace` carrier, so they are not asserted.

All theorems operate directly on `DoubledSpace E` with its concrete
modular conjugation and fundamental symmetry.
-/

set_option linter.unusedVariables false

open Complex

noncomputable section

namespace InfoGeometry.Krein.DiracHodgeDoubledSpace

open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### 1. The Canonical Operators on Doubled Space -/

/-- Modular conjugation: J(x,ξ) = (ξ,x). -/
abbrev J : DoubledSpace E →L[ℝ] DoubledSpace E := modular_j

/-- Fundamental symmetry: ε(x,ξ) = (x,-ξ). -/
abbrev ε : DoubledSpace E →L[ℝ] DoubledSpace E := spectral_epsilon

/-- Clock axis / canonical complex structure: K = J ∘ ε. -/
abbrev K : DoubledSpace E →L[ℝ] DoubledSpace E := clockAxis

/-! ### 2. Involutions and Anticommutation (from DoubledSpace) -/

/-- J is an involution: J² = I. -/
theorem J_involution (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    modular_j (E := E) ∘L modular_j (E := E) = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [modular_j]

/-- ε is an involution: ε² = I. -/
theorem ε_involution (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    spectral_epsilon (E := E) ∘L spectral_epsilon (E := E) = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [spectral_epsilon]

/-- J and ε anticommute: J·ε = -ε·J. -/
theorem J_ε_anticomm (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    modular_j (E := E) ∘L spectral_epsilon (E := E) = -(spectral_epsilon (E := E) ∘L modular_j (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [modular_j, spectral_epsilon]

/-! ### 3. Complex Structure: K² = -I -/

/-- Lemma: ε·J = -(J·ε). Follows from J·ε = -(ε·J) by conjugating with J. -/
lemma ε_J_eq_neg_J_ε (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    spectral_epsilon (E := E) ∘L modular_j (E := E) = -(modular_j (E := E) ∘L spectral_epsilon (E := E)) := by
  calc
    spectral_epsilon ∘L modular_j
        = (modular_j ∘L modular_j) ∘L (spectral_epsilon ∘L modular_j) := by
          rw [J_involution E]; simp
    _ = modular_j ∘L (modular_j ∘L spectral_epsilon) ∘L modular_j := by
      simp [ContinuousLinearMap.comp_assoc]
    _ = modular_j ∘L (-(spectral_epsilon ∘L modular_j)) ∘L modular_j := by
      rw [J_ε_anticomm E]
    _ = -((modular_j ∘L spectral_epsilon) ∘L (modular_j ∘L modular_j)) := by
      simp [ContinuousLinearMap.comp_assoc]
    _ = -(modular_j ∘L spectral_epsilon) := by rw [J_involution E]; simp

/-- The clock axis K = J·ε satisfies K² = -I. -/
theorem K_sq_neg_id (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    clockAxis (E := E) ∘L clockAxis (E := E) = -ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  dsimp [clockAxis, complex_i]
  calc
    (modular_j ∘L spectral_epsilon) ∘L (modular_j ∘L spectral_epsilon)
        = modular_j ∘L (spectral_epsilon ∘L modular_j) ∘L spectral_epsilon := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = modular_j ∘L (-(modular_j ∘L spectral_epsilon)) ∘L spectral_epsilon := by
      rw [ε_J_eq_neg_J_ε E]
    _ = -(modular_j ∘L modular_j ∘L spectral_epsilon ∘L spectral_epsilon) := by
      simp [ContinuousLinearMap.comp_assoc]
    _ = -ContinuousLinearMap.id ℝ (DoubledSpace E) := by
      simp [J_involution E, ε_involution E, ContinuousLinearMap.comp_assoc]

/-! ### 4. Hodge Star = Legendre Transform: J·K·J = -K -/

/-- The Hodge star conjugate flips the sign of the chiral clock axis:
J·K·J = -K. This is the Legendre transform in the Hestenes-Krein geometry. -/
theorem hodge_legendre_flip (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    modular_j (E := E) ∘L clockAxis (E := E) ∘L modular_j (E := E) = -clockAxis (E := E) := by
  dsimp [clockAxis, complex_i]
  calc
    modular_j ∘L (modular_j ∘L spectral_epsilon) ∘L modular_j
        = (modular_j ∘L modular_j) ∘L spectral_epsilon ∘L modular_j := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = ContinuousLinearMap.id ℝ (DoubledSpace E) ∘L spectral_epsilon ∘L modular_j := by
      rw [J_involution E]
    _ = spectral_epsilon ∘L modular_j := by simp
    _ = -(modular_j ∘L spectral_epsilon) := ε_J_eq_neg_J_ε E

/-! ### 5. Hodge conjugation of a continuous operator -/

/-- Hodge conjugation by the modular swap. -/
def hodgeConjugate
    (S : DoubledSpace E →L[ℝ] DoubledSpace E) : DoubledSpace E →L[ℝ] DoubledSpace E :=
  modular_j.comp (S.comp modular_j)

/-- The modular swap is an isometry for the doubled Hilbert norm. -/
theorem modular_j_isometry : Isometry (modular_j (E := E)) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  congr 1
  change doubledHilbertBilin (modular_j (E := E) (x - y)) (modular_j (E := E) (x - y)) =
    doubledHilbertBilin (x - y) (x - y)
  exact (doubledCarrier (E := E)).pairing_J_invariant (x - y) (x - y)

/-- Hodge conjugation is an involution on continuous operators. -/
theorem hodgeConjugate_involutive
    (S : DoubledSpace E →L[ℝ] DoubledSpace E) :
    hodgeConjugate (hodgeConjugate S) = S := by
  calc
    hodgeConjugate (hodgeConjugate S) =
        (modular_j (E := E) ∘L modular_j (E := E)) ∘L S ∘L
          (modular_j (E := E) ∘L modular_j (E := E)) := by
      simp [hodgeConjugate, ContinuousLinearMap.comp_assoc]
    _ = S := by rw [J_involution E]; simp

/-- Hodge conjugation preserves and reflects the isometry property. -/
theorem isometry_hodgeConjugate_iff
    (S : DoubledSpace E →L[ℝ] DoubledSpace E) :
    Isometry (hodgeConjugate S) ↔ Isometry S := by
  constructor
  · intro h
    rw [← hodgeConjugate_involutive (E := E) S]
    simpa only [hodgeConjugate, ContinuousLinearMap.coe_comp, Function.comp_def] using
      (modular_j_isometry.comp h).comp modular_j_isometry
  · intro h
    simpa only [hodgeConjugate, ContinuousLinearMap.coe_comp, Function.comp_def] using
      (modular_j_isometry.comp h).comp modular_j_isometry

end InfoGeometry.Krein.DiracHodgeDoubledSpace
