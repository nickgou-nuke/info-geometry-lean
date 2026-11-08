import InfoGeometry.Physics.FierzIdentities
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.ChiralCausalCone

/-!
# Finite normalized matrix trace and Fierz soldering

This module studies the normalized trace `τ(a)=½ Tr(a)` on `M₂(ℂ)` and its
interaction with the chiral Pauli/projector identities.

Fierz identity as soldering form maps operators to vectors/spinors:
  ½(I⊗I + σ₃⊗σ₃) + σ⁺⊗σ⁻ + σ⁻⊗σ⁺ = Swap

The proved identities include `τ(I)=1`, `τ(σ₃)=0`, equal normalized traces of
the two chiral projectors, commutator trace zero, anticommutator trace one, and
`τ(σ₃²)=1`.
-/

noncomputable section

namespace GNSModularObservables

open InfoGeometry.Physics.ChiralCausalCone
/-! ## 1. normalized matrix trace τ = ½Tr on M₂(ℂ) -/

/-- The normalized trace on M₂(ℂ): τ(a) = ½·Tr(a).
This is the unique normalized tracial state, corresponding to
the maximally mixed vacuum |Ω⟩ with equal occupation of both
chiral states. -/
def normalizedTrace (A : M2C) : ℂ := (Matrix.trace A) / 2

/-- The trace of σ₃ vanishes: τ(σ₃) = 0.
This is the normalized trace of the diagonal Pauli matrix. -/
theorem normalizedTrace_sigma3 : normalizedTrace σ3c = 0 := by
  simp [normalizedTrace, Matrix.trace_fin_two, σ3c]

/-- The trace of the identity: τ(I) = 1.  The normalized matrix trace sends the identity to one. -/
theorem normalizedTrace_identity : normalizedTrace (1 : M2C) = 1 := by
  simp [normalizedTrace, Matrix.trace_fin_two]

/-- Chiral projector expectations: τ(N₊) = τ(N₋) = ½.
The two rank-one diagonal projectors have equal normalized trace. -/
theorem normalizedTrace_chiral_projectors :
    normalizedTrace PPlus = 1/2 ∧ normalizedTrace PMinus = 1/2 ∧
    normalizedTrace (PPlus + PMinus) = 1 := by
  have hP : PPlus = !![1, 0; 0, 0] := PPlus_matrix
  have hM : PMinus = !![0, 0; 0, 1] := PMinus_matrix
  rw [hP, hM]
  simp [normalizedTrace, Matrix.trace_fin_two]

/-- The commutator trace vanishes: τ([σ⁺,σ⁻]) = τ(σ₃) = 0.
This is the trace consequence of the chiral commutator identity. -/
theorem normalizedTrace_commutator_vanishes :
    normalizedTrace (σPlus * σMinus - σMinus * σPlus) = 0 := by
  rw [comm_σPlus_σMinus]
  exact normalizedTrace_sigma3

/-- The anticommutator trace: τ({σ⁺,σ⁻}) = τ(I) = 1.
This is the trace consequence of the chiral anticommutator identity. -/
theorem normalizedTrace_anticommutator_complete :
    normalizedTrace (σPlus * σMinus + σMinus * σPlus) = 1 := by
  rw [anti_σPlus_σMinus]
  exact normalizedTrace_identity

/-! ## 3. Fierz identity = soldering form: operators → spinors -/

/-- The Fierz completeness relation:
  ½(I⊗I + σ₃⊗σ₃) + σ⁺⊗σ⁻ + σ⁻⊗σ⁺ = Swap

This identity maps the 2×2 matrix algebra onto the 4-dim
spinor space ℂ²⊗ℂ².  It is the algebraic soldering form that
translates operators (the "bits") to vectors/spinors (the "it").

The four terms correspond to the 4 Cuntz generators:
  I⊗I   ↔ S₀ (identity/singlet channel)
  σ₃⊗σ₃ ↔ S₃ (chirality channel)
  σ⁺⊗σ⁻ ↔ S₁ (raising/particle channel)
  σ⁻⊗σ⁺ ↔ S₂ (lowering/hole channel) -/
theorem fierz_soldering_maps_operators_to_spinors :
    (1/2 : ℂ) • (Matrix.kroneckerMap (fun (a b : ℂ) => a * b) (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      Matrix.kroneckerMap (fun (a b : ℂ) => a * b) σ3c σ3c) +
    Matrix.kroneckerMap (fun (a b : ℂ) => a * b) σPlus σMinus +
    Matrix.kroneckerMap (fun (a b : ℂ) => a * b) σMinus σPlus = InfoGeometry.Physics.FierzIdentities.Swap := InfoGeometry.Physics.FierzIdentities.chiral_fierz_identity

/-! ## 4. Physical observables — what the normalized trace measures -/

/-- The charge variance: τ(Q²) = τ(σ₃²) = τ(I) = 1.
This is the normalized trace of the square of the diagonal Pauli matrix. -/
theorem normalizedTrace_sigma3_sq :
    normalizedTrace (σ3c * σ3c) = 1 := by
  rw [σ3c_sq]
  exact normalizedTrace_identity

/-- The chiral projectors are orthogonal: τ(N₊·N₋) = 0.
This follows from orthogonality of the two projectors. -/
theorem chiral_projectors_orthogonal_in_trace :
    normalizedTrace (PPlus * PMinus) = 0 := by
  rw [PPlus_PMinus_orthogonal]
  simp [normalizedTrace]

/-! ## 5. Synthesis — normalized trace identities -/

theorem finite_normalized_trace_synthesis :
    -- Vacuum normalized: τ(I) = 1
    normalizedTrace (1 : M2C) = 1 ∧
    -- Symmetric vacuum: τ(σ₃) = 0
    normalizedTrace σ3c = 0 ∧
    -- Chiral projectors: τ(N₊) = τ(N₋) = ½
    normalizedTrace PPlus = 1/2 ∧ normalizedTrace PMinus = 1/2 ∧
    -- Completeness: τ(N₊+N₋) = τ(I) = 1
    normalizedTrace (PPlus + PMinus) = 1 ∧
    -- The chiral commutator has normalized trace zero.
    normalizedTrace (σPlus * σMinus - σMinus * σPlus) = 0 ∧
    -- Anticommutator complete: CAR algebra
    normalizedTrace (σPlus * σMinus + σMinus * σPlus) = 1 ∧
    -- Charge variance = 1 bit
    normalizedTrace (σ3c * σ3c) = 1 ∧
    -- Projectors orthogonal
    normalizedTrace (PPlus * PMinus) = 0 :=
  ⟨normalizedTrace_identity,
   normalizedTrace_sigma3,
   (normalizedTrace_chiral_projectors).1,
   (normalizedTrace_chiral_projectors).2.1,
   (normalizedTrace_chiral_projectors).2.2,
   normalizedTrace_commutator_vanishes,
   normalizedTrace_anticommutator_complete,
   normalizedTrace_sigma3_sq,
   chiral_projectors_orthogonal_in_trace⟩

end GNSModularObservables

end noncomputable section
