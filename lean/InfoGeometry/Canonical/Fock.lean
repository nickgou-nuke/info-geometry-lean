import InfoGeometry.Quantum.Fock

/-!
# InfoGeometry.Canonical.Fock

Canonical facade for doubled-space Fock operators and Bayesian update laws.
-/

namespace InfoGeometry.Canonical.Fock

export InfoGeometry.Quantum (
  annihilationOp
  creationOp
  cliffordGenE
  cliffordGenF
  creation_eq_plus_projector
  annihilation_eq_minus_projector
  creation_annihilation_orthogonal
  creation_add_annihilation
  commutator
  commutator_J_epsilon_eq_two_I
  annihilation_kills_vacuum_vector
  dataPart
  modelPart
  data_model_decomposition
  bayesianAddData
  bayesianAddData_zero
  bayesianUpdate
  bayesian_update_preserves_data_independence
  inducedSymplecticForm
  inducedSymplecticForm_eq_complex_pairing
  vacuum_is_zero_ray
)

open InfoGeometry.Quantum
open InfoGeometry.Krein

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Theorem `bayesianUpdate_eq_creationExcitation`. -/
theorem bayesianUpdate_eq_creationExcitation
    (prior dataInnovation : DoubledSpace E) :
    bayesianUpdate (E := E) prior dataInnovation = prior + creationOp (E := E) dataInnovation := rfl

/-- Theorem `dataPart_eq_creation`. -/
theorem dataPart_eq_creation (v : DoubledSpace E) :
    dataPart (E := E) v = creationOp (E := E) v := rfl

/-- Theorem `modelPart_eq_annihilation`. -/
theorem modelPart_eq_annihilation (v : DoubledSpace E) :
    modelPart (E := E) v = annihilationOp (E := E) v := rfl

end InfoGeometry.Canonical.Fock
