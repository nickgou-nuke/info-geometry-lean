import InfoGeometry.Projective.Null
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Grading
import InfoGeometry.Krein.Dilation

/-!
# Fock Space Representation of Information

This module provides a toy Fock-style interface on `DoubledSpace E`, linking:
- Clifford grading projectors (`creationLike`, `annihilationLike`)
- Symplectic/Krein pairings (canonical CCR-like brackets)
- The information vacuum state (ray of the origin)

Matches the naming conventions in the project's CAR-style dictionary.
-/

set_option linter.unusedSectionVars false

namespace InfoGeometry.Quantum

open InfoGeometry.Krein
open InfoGeometry.Projective

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

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

/-- Commutator of doubled-space maps. -/
noncomputable def commutator (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  A.comp B - B.comp A

/-- Compatibility alias for the first Clifford generator. -/
noncomputable abbrev cliffordGenE : DoubledSpace E →L[ℝ] DoubledSpace E :=
  modular_j (E := E)

/-- Compatibility alias for the second Clifford generator. -/
noncomputable abbrev cliffordGenF : DoubledSpace E →L[ℝ] DoubledSpace E :=
  spectral_epsilon (E := E)

/-- Weyl-style identity: `[I, J] = -2ε` in this sign convention. -/
theorem commutator_I_J :
    commutator (complex_i (E := E)) (modular_j (E := E))
      = (-2 : ℝ) • (spectral_epsilon (E := E)) := by
  simpa [commutator] using InfoGeometry.Krein.clmComm_complex_i_modular_j (E := E)

/-- Compatibility alias for `[J, ε] = 2I`. -/
theorem commutator_J_epsilon_eq_two_I :
    commutator (modular_j (E := E)) (spectral_epsilon (E := E))
      = (2 : ℝ) • (complex_i (E := E)) := by
  simpa [commutator] using InfoGeometry.Krein.clmComm_modular_j_spectral_epsilon (E := E)

/-- The annihilation channel kills the vacuum vector `0`. -/
theorem annihilation_kills_vacuum_vector :
    annihilationOp (E := E) 0 = 0 := by
  simp [annihilationOp]

/-- Data component extracted by the creation channel. -/
noncomputable def dataPart (v : DoubledSpace E) : DoubledSpace E :=
  creationOp (E := E) v

/-- Model component extracted by the annihilation channel. -/
noncomputable def modelPart (v : DoubledSpace E) : DoubledSpace E :=
  annihilationOp (E := E) v

/-- Every doubled state splits into data-plus-model channels. -/
theorem data_model_decomposition (v : DoubledSpace E) :
    v = dataPart (E := E) v + modelPart (E := E) v := by
  simpa [dataPart, modelPart, add_comm] using
    (congrArg (fun f => f v) (creation_add_annihilation (E := E))).symm

/-- Linear Bayesian data insertion step. -/
noncomputable def bayesianAddData
    (prior dataInnovation : DoubledSpace E) : DoubledSpace E :=
  prior + dataPart (E := E) dataInnovation

@[simp] theorem bayesianAddData_zero (prior : DoubledSpace E) :
    bayesianAddData (E := E) prior 0 = prior := by
  simp [bayesianAddData, dataPart]

/-- Canonical Bayesian update (compatibility alias). -/
noncomputable abbrev bayesianUpdate
    (prior dataInnovation : DoubledSpace E) : DoubledSpace E :=
  bayesianAddData (E := E) prior dataInnovation

/-- Compatibility identity for data-channel preservation form. -/
theorem bayesian_update_preserves_data_independence
    (prior dataInnovation : DoubledSpace E) :
    bayesianUpdate (E := E) prior dataInnovation
      = prior + dataPart (E := E) dataInnovation := rfl

/-- Induced symplectic pairing through the complex structure. -/
noncomputable def inducedSymplecticForm (ψ φ : DoubledSpace E) : ℝ :=
  hessian_indefinite_form (E := E) ψ (complex_i (E := E) φ)

/-- Compatibility rewriting lemma for the induced symplectic form. -/
theorem inducedSymplecticForm_eq_complex_pairing (ψ φ : DoubledSpace E) :
    inducedSymplecticForm (E := E) ψ φ
      = hessian_indefinite_form (E := E) ψ (complex_i (E := E) φ) := rfl

/-- The projective vacuum is the ray of the zero doubled vector. -/
theorem vacuum_is_zero_ray :
    InfoGeometry.Projective.vacuum (E := E) = projectivize (E := E) (0 : DoubledSpace E) := rfl

end InfoGeometry.Quantum
