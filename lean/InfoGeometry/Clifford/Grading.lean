import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Cartan.Involution
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Clifford Gradings and Cartan Involutions

This module implements the Z/2-grading of the information state space using the 
generic Cartan involution framework. Krein grading (geometric) is prioritized 
ahead of Clifford grading (spectral).

Mathematical Hierarchy:
1. A Cartan involution θ provides the fundamental space decomposition.
2. The Endomorphism Algebra is graded by the parity of operators relative to θ.
3. Clifford generators are odd elements in this graded algebra.

The implementation is purely algebraic in the continuous endomorphism ring, 
relying on the properties of involutive linear equivalences from the Cartan layer.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Krein

open InfoGeometry.Cartan

section KreinClifford

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Commutator bracket on doubled-space endomorphisms. -/
def clmComm (A B : DoubledSpace E →L[ℝ] DoubledSpace E) : DoubledSpace E →L[ℝ] DoubledSpace E :=
  A.comp B - B.comp A

lemma clmComm_eq_lie (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    clmComm A B = ⁅A, B⁆ := by
  ext v <;> simp [clmComm, Ring.lie_def]

/-- Jordan product on doubled-space endomorphisms. -/
noncomputable def jordanProd (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (A.comp B + B.comp A)

/-- Even operators commute with the geometric grading involution `J`. -/
def isEven (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  (modular_j (E := E)).comp A = A.comp (modular_j (E := E))

/-- Odd operators anticommute with the geometric grading involution `J`. -/
def isOdd (A : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  (modular_j (E := E)).comp A = -(A.comp (modular_j (E := E)))

/-- `+1` eigenspace predicate for the grading involution `J`. -/
def inGradePlus (v : DoubledSpace E) : Prop := modular_j (E := E) v = v

/-- `-1` eigenspace predicate for the grading involution `J`. -/
def inGradeMinus (v : DoubledSpace E) : Prop := modular_j (E := E) v = -v

/-! ### Projectors in the Continuous Endomorphism Ring -/

/-- Chirality/grade projector `(Id + J)/2`. -/
noncomputable def gradePlusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  (⅟ (2 : ℝ)) • ((ContinuousLinearMap.id ℝ (DoubledSpace E)) + modular_j (E := E))

/-- Chirality/grade projector `(Id - J)/2`. -/
noncomputable def gradeMinusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  (⅟ (2 : ℝ)) • ((ContinuousLinearMap.id ℝ (DoubledSpace E)) - modular_j (E := E))

/-- Coordinate-free alias for the `+` chirality component. -/
noncomputable abbrev gradePlusPart (v : DoubledSpace E) : DoubledSpace E :=
  gradePlusProj (E := E) v

/-- Coordinate-free alias for the `-` chirality component. -/
noncomputable abbrev gradeMinusPart (v : DoubledSpace E) : DoubledSpace E :=
  gradeMinusProj (E := E) v

@[simp] lemma gradePlusProj_apply (v : DoubledSpace E) :
    gradePlusProj (E := E) v = gradePlusPart (E := E) v := rfl

@[simp] lemma gradeMinusProj_apply (v : DoubledSpace E) :
    gradeMinusProj (E := E) v = gradeMinusPart (E := E) v := rfl

/-- Spectral projector `(Id + ε)/2`. -/
noncomputable def spectralPlusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  (⅟ (2 : ℝ)) • ((ContinuousLinearMap.id ℝ (DoubledSpace E)) + spectral_epsilon (E := E))

/-- Spectral projector `(Id - ε)/2`. -/
noncomputable def spectralMinusProj : DoubledSpace E →L[ℝ] DoubledSpace E :=
  (⅟ (2 : ℝ)) • ((ContinuousLinearMap.id ℝ (DoubledSpace E)) - spectral_epsilon (E := E))

/-! ### Algebraic Identities (Bridged to Cartan Foundation) -/

lemma gradePlusProj_idempotent :
    (gradePlusProj (E := E)).comp (gradePlusProj (E := E)) = gradePlusProj (E := E) := by
  apply ContinuousLinearMap.ext; intro v
  have h := LinearMap.congr_fun 
    (Pplus_idempotent (modular_jLE E).toLinearMap (modular_j_is_cartan E)) v
  simp only [gradePlusProj, Pplus, ContinuousLinearMap.comp_apply] at h ⊢
  exact h

lemma gradeMinusProj_idempotent :
    (gradeMinusProj (E := E)).comp (gradeMinusProj (E := E)) = gradeMinusProj (E := E) := by
  apply ContinuousLinearMap.ext; intro v
  have h := LinearMap.congr_fun 
    (Pminus_idempotent (modular_jLE E).toLinearMap (modular_j_is_cartan E)) v
  simp only [gradeMinusProj, Pminus, ContinuousLinearMap.comp_apply] at h ⊢
  exact h

lemma gradeProj_sum :
    gradePlusProj (E := E) + gradeMinusProj (E := E) = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext; intro v
  have h := LinearMap.congr_fun (Pplus_add_Pminus_eq_id (modular_jLE E).toLinearMap) v
  simp only [gradePlusProj, gradeMinusProj, Pplus, Pminus, ContinuousLinearMap.add_apply] at h ⊢
  exact h

lemma gradePlusProj_comp_gradeMinusProj :
    (gradePlusProj (E := E)).comp (gradeMinusProj (E := E)) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply DoubledSpace.ext <;>
    simp [gradePlusProj, gradeMinusProj, modular_j_apply, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm, smul_add, smul_sub,
      mul_assoc, mul_left_comm, mul_comm]

lemma gradeMinusProj_comp_gradePlusProj :
    (gradeMinusProj (E := E)).comp (gradePlusProj (E := E)) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply DoubledSpace.ext <;>
    simp [gradePlusProj, gradeMinusProj, modular_j_apply, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm, smul_add, smul_sub,
      mul_assoc, mul_left_comm, mul_comm]

lemma spectralPlusProj_idempotent :
    (spectralPlusProj (E := E)).comp (spectralPlusProj (E := E)) = spectralPlusProj (E := E) := by
  apply ContinuousLinearMap.ext; intro v
  have h := LinearMap.congr_fun 
    (Pplus_idempotent (spectral_epsilonLE E).toLinearMap (spectral_epsilon_is_cartan E)) v
  simp only [spectralPlusProj, Pplus, ContinuousLinearMap.comp_apply] at h ⊢
  exact h

lemma spectralMinusProj_idempotent :
    (spectralMinusProj (E := E)).comp (spectralMinusProj (E := E)) = spectralMinusProj (E := E) := by
  apply ContinuousLinearMap.ext; intro v
  have h := LinearMap.congr_fun 
    (Pminus_idempotent (spectral_epsilonLE E).toLinearMap (spectral_epsilon_is_cartan E)) v
  simp only [spectralMinusProj, Pminus, ContinuousLinearMap.comp_apply] at h ⊢
  exact h

lemma spectralProj_sum :
    spectralPlusProj (E := E) + spectralMinusProj (E := E) = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext; intro v
  have h := LinearMap.congr_fun (Pplus_add_Pminus_eq_id (spectral_epsilonLE E).toLinearMap) v
  simp only [spectralPlusProj, spectralMinusProj, Pplus, Pminus, ContinuousLinearMap.add_apply] at h ⊢
  exact h

/-- Canonical Krein-facing alias for spectral projector completeness: `P₊ + P₋ = I`. -/
@[simp] lemma krein_projector_completeness :
    spectralPlusProj (E := E) + spectralMinusProj (E := E)
      = ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  spectralProj_sum (E := E)

/-! ### Clifford Relations -/

lemma spectral_epsilon_isOdd : isOdd (E := E) (spectral_epsilon (E := E)) := by
  simpa [isOdd] using modular_j_spectral_epsilon_anticommute (E := E)

/-- CAR-style dictionary entry: creation-like projector (grade `+`). -/
noncomputable def creationLike : DoubledSpace E →L[ℝ] DoubledSpace E :=
  gradePlusProj (E := E)

/-- CAR-style dictionary entry: annihilation-like projector (grade `-`). -/
noncomputable def annihilationLike : DoubledSpace E →L[ℝ] DoubledSpace E :=
  gradeMinusProj (E := E)

lemma creation_annihilation_decomposition (v : DoubledSpace E) :
    v = creationLike (E := E) v + annihilationLike (E := E) v := by
  have h := congrArg (fun T : DoubledSpace E →L[ℝ] DoubledSpace E => T v) (gradeProj_sum (E := E))
  simpa [creationLike, annihilationLike, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply] using h.symm

lemma spectral_decomposition (v : DoubledSpace E) :
    v = spectralPlusProj (E := E) v + spectralMinusProj (E := E) v := by
  rw [← ContinuousLinearMap.add_apply]
  rw [spectralProj_sum (E := E)]
  rfl

/-- Canonical Krein-facing alias for pointwise spectral decomposition. -/
lemma krein_projector_decomposition (v : DoubledSpace E) :
    v = spectralPlusProj (E := E) v + spectralMinusProj (E := E) v :=
  spectral_decomposition (E := E) v

end KreinClifford

end InfoGeometry.Krein

-- Preserve exports for backward compatibility
export InfoGeometry.Krein
  (clmComm clmComm_eq_lie
   jordanProd
   isEven isOdd
   inGradePlus inGradeMinus
   gradePlusProj gradeMinusProj spectralPlusProj spectralMinusProj
   gradePlusPart gradeMinusPart
   gradePlusProj_apply gradeMinusProj_apply
   gradePlusProj_idempotent gradeMinusProj_idempotent
   gradePlusProj_comp_gradeMinusProj gradeMinusProj_comp_gradePlusProj
   gradeProj_sum
   spectralPlusProj_idempotent spectralMinusProj_idempotent
   spectralProj_sum
   krein_projector_completeness
   creationLike annihilationLike
   creation_annihilation_decomposition
   spectral_decomposition
   krein_projector_decomposition
   spectral_epsilon_isOdd)
