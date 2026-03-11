import InfoGeometry.Projective.Null
import InfoGeometry.Clifford.Grading

/-!
# Fock Space Representation of Information

This module provides a toy Fock-style interface on `DoubledSpace E`, linking:
- Clifford grading projectors (`creationLike`, `annihilationLike`)
- Symplectic/Krein pairings (canonical CCR-like brackets)
- The information vacuum state (ray of the origin)

Matches the naming conventions in the project's CAR-style dictionary.
-/

namespace InfoGeometry.Quantum

open InfoGeometry.Krein

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The creation operator: projectors onto the grade `+` subspace. -/
noncomputable def creationOp : DoubledSpace E →L[ℝ] DoubledSpace E :=
  creationLike (E := E)

/-- The annihilation operator: projectors onto the grade `-` subspace. -/
noncomputable def annihilationOp : DoubledSpace E →L[ℝ] DoubledSpace E :=
  annihilationLike (E := E)

/-- Bridge to the canonical Clifford projectors. -/
theorem creation_eq_plus_projector :
    creationOp (E := E) = gradePlusProj (E := E) := rfl

theorem annihilation_eq_minus_projector :
    annihilationOp (E := E) = gradeMinusProj (E := E) := rfl

/-- Orthogonality of grade projectors: `P₊ ∘ P₋ = 0`. -/
theorem creation_annihilation_orthogonal :
    (creationOp (E := E)).comp (annihilationOp (E := E)) = 0 := by
  rw [creation_eq_plus_projector, annihilation_eq_minus_projector]
  exact InfoGeometry.Krein.gradePlusProj_comp_gradeMinusProj (E := E)

/-- Completeness of the split: `P₊ + P₋ = Id`. -/
theorem creation_add_annihilation :
    creationOp (E := E) + annihilationOp (E := E)
      = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  rw [creation_eq_plus_projector, annihilation_eq_minus_projector]
  exact gradeProj_sum (E := E)

section SymplecticForm

variable [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Commutator of doubled-space maps. -/
noncomputable def commutator (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  A.comp B - B.comp A

/-- Weyl-style identity: `[I, J] = 2ε`. -/
theorem commutator_I_J :
    commutator (complex_i (E := E)) (modular_j (E := E))
      = 2 • (spectral_epsilon (E := E)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply (WithLp.ofLp_injective 2)
  apply Prod.ext
  · simp [commutator, complex_i, modular_j, spectral_epsilon, two_smul]
  · simp [commutator, complex_i, modular_j, spectral_epsilon, two_smul]

/-- The information vacuum is fixed by both grading subspaces. -/
def vacuum : ProjectiveState (E := E) :=
  projectivize (E := E) (0 : DoubledSpace E)

lemma vacuum_def :
    vacuum (E := E) = projectivize (E := E) (0 : DoubledSpace E) := rfl

end SymplecticForm

/-- The projective vacuum is the ray of the zero doubled vector. -/
theorem vacuum_is_zero_ray :
    vacuum (E := E) = projectivize (E := E) (0 : DoubledSpace E) :=
  vacuum_def (E := E)

end InfoGeometry.Quantum
