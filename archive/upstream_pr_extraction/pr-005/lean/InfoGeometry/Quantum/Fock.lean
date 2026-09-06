import InfoGeometry.Projective.Null

/-!
# Fock Space Representation of Information

This module provides a toy Fock-style interface on `DoubledSpace E`, linking:
- Clifford grading projectors (`creationLike`, `annihilationLike`)
- projective vacuum (`vacuum`)
- data/model decomposition used in information updates.
-/

namespace InfoGeometry.Quantum

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

section FockAlgebra

/-- "Annihilation" operator: the grade `-` projector. -/
noncomputable def annihilationOp : DoubledSpace E →L[ℝ] DoubledSpace E :=
  annihilationLike (E := E)

/-- "Creation" operator: the grade `+` projector. -/
noncomputable def creationOp : DoubledSpace E →L[ℝ] DoubledSpace E :=
  creationLike (E := E)

/-- Clifford generator `J`. -/
noncomputable def cliffordGenE : DoubledSpace E →L[ℝ] DoubledSpace E :=
  modularJ (E := E)

/-- Clifford generator `ε`. -/
noncomputable def cliffordGenF : DoubledSpace E →L[ℝ] DoubledSpace E :=
  spectralEpsilon (E := E)

theorem creation_eq_plus_projector :
    creationOp (E := E) = gradePlusProj (E := E) := rfl

theorem annihilation_eq_minus_projector :
    annihilationOp (E := E) = gradeMinusProj (E := E) := rfl

/-- Orthogonality of grade projectors: `P₊ ∘ P₋ = 0`. -/
theorem creation_annihilation_orthogonal :
    (creationOp (E := E)).comp (annihilationOp (E := E)) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hminus :
      modularJ (E := E) (annihilationLike (E := E) v)
        = -annihilationLike (E := E) v :=
    annihilationLike_inGradeMinus (E := E) v
  have hminus' :
      modularJInvolution (E := E) (annihilationLike (E := E) v)
        = -annihilationLike (E := E) v := by
    simpa [modularJInvolution] using hminus
  unfold creationOp annihilationOp
  simp [ContinuousLinearMap.comp_apply]
  rw [creationLike_apply]
  unfold gradePlusPart
  unfold InfoGeometry.Core.Projector.plus
  rw [hminus']
  simp

/-- Completeness of the split: `P₊ + P₋ = Id`. -/
theorem creation_add_annihilation :
    creationOp (E := E) + annihilationOp (E := E)
      = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext
  intro v
  simpa [creationOp, annihilationOp] using
    (creation_annihilation_decomposition (E := E) v).symm

end FockAlgebra

section SymplecticGenerator

/-- Commutator bracket on doubled-space endomorphisms. -/
def commutator
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) :
    DoubledSpace E →L[ℝ] DoubledSpace E :=
  A.comp B - B.comp A

/-- The commutator of `J` and `ε` generates `2I`. -/
theorem commutator_J_epsilon_eq_two_I :
    commutator (modularJ (E := E)) (spectralEpsilon (E := E))
      = (2 : ℝ) • complexI (E := E) := by
  ext v <;> simp [commutator, complexI, modularJ, spectralEpsilon, two_smul, sub_eq_add_neg]

end SymplecticGenerator

section VacuumPhysics

/-- The annihilation operator sends the vacuum vector `0` to `0`. -/
theorem annihilation_kills_vacuum_vector :
    annihilationOp (E := E) 0 = 0 :=
  (annihilationOp (E := E)).map_zero

/-- Data component extracted by the creation projector. -/
noncomputable def dataPart (v : DoubledSpace E) : DoubledSpace E :=
  creationOp (E := E) v

/-- Model component extracted by the annihilation projector. -/
noncomputable def modelPart (v : DoubledSpace E) : DoubledSpace E :=
  annihilationOp (E := E) v

/-- Canonical split `v = v_data + v_model`. -/
theorem data_model_decomposition (v : DoubledSpace E) :
    v = dataPart (E := E) v + modelPart (E := E) v := by
  simpa [dataPart, modelPart, creationOp, annihilationOp] using
    creation_annihilation_decomposition (E := E) v

/-- Informational "Bayesian add-data" update on doubled states. -/
noncomputable def bayesianAddData
    (currentState : DoubledSpace E) (newData : DoubledSpace E) : DoubledSpace E :=
  currentState + creationOp (E := E) newData

theorem bayesianAddData_zero (newData : DoubledSpace E) :
    bayesianAddData (E := E) 0 newData = dataPart (E := E) newData := by
  simp [bayesianAddData, dataPart]

/-- Alias: Bayesian update as adding the created data component. -/
noncomputable def bayesianUpdate
    (prior : DoubledSpace E) (dataInnovation : DoubledSpace E) : DoubledSpace E :=
  bayesianAddData (E := E) prior dataInnovation

/-- Updating by a pure model (`grade -`) perturbation leaves the data projection unchanged. -/
theorem bayesian_update_preserves_data_independence
    (state noise : DoubledSpace E) :
    creationOp (E := E) (bayesianUpdate (E := E) state (annihilationOp (E := E) noise))
      = creationOp (E := E) state := by
  unfold bayesianUpdate bayesianAddData
  have hzero :
      creationOp (E := E) (annihilationOp (E := E) noise) = 0 := by
    have hcomp := creation_annihilation_orthogonal (E := E)
    exact congrArg (fun T => T noise) hcomp
  calc
    creationOp (E := E) (state + creationOp (E := E) (annihilationOp (E := E) noise))
        = creationOp (E := E) (state + 0) := by
            rw [hzero]
    _ = creationOp (E := E) state := by simp

end VacuumPhysics

section SymplecticForm

variable [InnerProductSpace ℝ E]

/-- Symplectic form induced by the `J/ε` commutator. -/
noncomputable def inducedSymplecticForm (u v : DoubledSpace E) : ℝ :=
  hessianIndefiniteForm (E := E) u
    (((2 : ℝ)⁻¹) • (commutator (modularJ (E := E)) (spectralEpsilon (E := E)) v))

/-- The induced commutator form is exactly the `I`-twisted neutral pairing. -/
theorem inducedSymplecticForm_eq_complex_pairing (u v : DoubledSpace E) :
    inducedSymplecticForm (E := E) u v
      = hessianIndefiniteForm (E := E) u (complexI (E := E) v) := by
  unfold inducedSymplecticForm
  rw [commutator_J_epsilon_eq_two_I]
  simp [smul_smul]

end SymplecticForm

/-- The projective vacuum is the ray of the zero doubled vector. -/
theorem vacuum_is_zero_ray :
    vacuum (E := E) = projectivize (E := E) (0 : DoubledSpace E) :=
  vacuum_def (E := E)

end InfoGeometry.Quantum
