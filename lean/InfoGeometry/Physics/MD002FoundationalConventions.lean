import InfoGeometry.Physics.MD001MatrixQuantumGeometry

/-!
# Repaired MD 002: foundational finite matrix conventions

Source: `github-nick:nickgou-nuke/MD`, file `002.md`.

Chapter 2 is a definitions-and-conventions chapter.  It mixes elementary finite
matrix identities with reference-only continuum material (curved spacetime,
connections, Clifford/gamma matrices, information geometry, probability, and
calculus).  This file formalizes the finite core that is actually used by the
matrix-quantum-geometry spine:

* standard Pauli basis algebra, reused from `UnifiedMatrixBasis`;
* normalized Pauli/spacetime matrix convention with an abstract scalar `c`
  satisfying `c*c = 1/2` (the algebraic role of `1/sqrt 2`);
* determinant interval convention `ds² = -2 det(dX)` for the normalized matrix;
* normalized Hilbert--Schmidt trace readouts;
* finite Jordan and Lie/commutator products on the concrete `2 × 2` carrier;
* quaternion-complex-structure relations from the existing finite basis owner.

No theorem about smooth manifolds, tetrads, spin connections, gamma-matrix PDEs,
Kähler-Einstein geometry, QFI/Bures equivalence, stochastic calculus, or
curvature dynamics is asserted here.
-/

noncomputable section

namespace MD002FoundationalConventions

open Matrix
open InfoGeometry.Physics.MD001MatrixQuantumGeometry

/-- Algebraic normalization scalar for `1 / sqrt 2`. -/
def IsPauliNormalization (c : ℂ) : Prop :=
  c * c = (1 / 2 : ℂ)

/-- Normalized Pauli-basis spacetime matrix, with scalar `c = 1 / sqrt 2` abstracted. -/
def normalizedPauliSpacetimeMatrix (c dt dx dy dz : ℂ) : MatrixQuantumCarrier :=
  c • pauliSpacetimeMatrix dt dx dy dz

/-- Determinant readout for the normalized Pauli matrix before imposing `c*c = 1/2`. -/
theorem normalizedPauliSpacetimeMatrix_det (c dt dx dy dz : ℂ) :
    Matrix.det (normalizedPauliSpacetimeMatrix c dt dx dy dz) =
      c * c * (dt * dt - (dx * dx + dy * dy + dz * dz)) := by
  unfold normalizedPauliSpacetimeMatrix
  rw [Matrix.det_smul]
  simp [Fintype.card_fin, pow_two, pauliSpacetimeMatrix_det]

/-- Chapter 2 convention: for normalized `dX`, `-2 det(dX)` is the `(-,+,+,+)` interval. -/
theorem normalized_interval_eq_minkowski_minus_plus_plus_plus
    (c dt dx dy dz : ℂ) (hc : IsPauliNormalization c) :
    (-2 : ℂ) * Matrix.det (normalizedPauliSpacetimeMatrix c dt dx dy dz) =
      -(dt * dt) + (dx * dx + dy * dy + dz * dz) := by
  rw [normalizedPauliSpacetimeMatrix_det]
  rw [hc]
  ring

/-- Normalized trace readout for the identity Pauli axis. -/
theorem normalized_hilbertSchmidt_identity_self
    (c : ℂ) (hc : IsPauliNormalization c) :
    UnifiedMatrixBasis.hilbertSchmidt (c • UnifiedMatrixBasis.I₂)
      (c • UnifiedMatrixBasis.I₂) = (1 / 2 : ℂ) := by
  unfold UnifiedMatrixBasis.hilbertSchmidt
  simp [UnifiedMatrixBasis.I₂, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hc]
  norm_num

/-- Normalized trace readout for the first Pauli spatial axis. -/
theorem normalized_hilbertSchmidt_sigma1_self
    (c : ℂ) (hc : IsPauliNormalization c) :
    UnifiedMatrixBasis.hilbertSchmidt (c • UnifiedMatrixBasis.σ₁)
      (c • UnifiedMatrixBasis.σ₁) = (1 / 2 : ℂ) := by
  unfold UnifiedMatrixBasis.hilbertSchmidt
  simp [UnifiedMatrixBasis.σ₁, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hc]
  norm_num

/-- The finite Jordan product from Chapter 2. -/
def jordanProduct (A B : MatrixQuantumCarrier) : MatrixQuantumCarrier :=
  (1 / 2 : ℂ) • (A * B + B * A)

/-- The finite Lie product / commutator from Chapter 2. -/
def lieProduct (A B : MatrixQuantumCarrier) : MatrixQuantumCarrier :=
  A * B - B * A

/-- The Jordan product is symmetric. -/
theorem jordanProduct_comm (A B : MatrixQuantumCarrier) :
    jordanProduct A B = jordanProduct B A := by
  unfold jordanProduct
  abel_nf

/-- The Lie product is antisymmetric. -/
theorem lieProduct_antisymm (A B : MatrixQuantumCarrier) :
    lieProduct B A = - lieProduct A B := by
  unfold lieProduct
  abel_nf

/-- Existing finite complex-structure matrices satisfy the quaternion relations. -/
theorem md002_quaternion_complex_structure_packet :
    UnifiedMatrixBasis.complexI * UnifiedMatrixBasis.complexI =
        -(1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    UnifiedMatrixBasis.complexJ * UnifiedMatrixBasis.complexJ =
        -(1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    UnifiedMatrixBasis.complexK * UnifiedMatrixBasis.complexK =
        -(1 : Matrix (Fin 4) (Fin 4) ℝ) ∧
    UnifiedMatrixBasis.complexI * UnifiedMatrixBasis.complexJ = UnifiedMatrixBasis.complexK ∧
    UnifiedMatrixBasis.complexJ * UnifiedMatrixBasis.complexK = UnifiedMatrixBasis.complexI ∧
    UnifiedMatrixBasis.complexK * UnifiedMatrixBasis.complexI = UnifiedMatrixBasis.complexJ :=
  UnifiedMatrixBasis.quaternion_relations

/-- Repaired theorem-safe Chapter 2 packet. -/
theorem repaired_MD002_foundational_conventions_packet
    (c dt dx dy dz : ℂ) (hc : IsPauliNormalization c)
    (A B : MatrixQuantumCarrier) :
    Matrix.det (normalizedPauliSpacetimeMatrix c dt dx dy dz) =
        c * c * (dt * dt - (dx * dx + dy * dy + dz * dz)) ∧
    (-2 : ℂ) * Matrix.det (normalizedPauliSpacetimeMatrix c dt dx dy dz) =
        -(dt * dt) + (dx * dx + dy * dy + dz * dz) ∧
    UnifiedMatrixBasis.hilbertSchmidt (c • UnifiedMatrixBasis.I₂)
        (c • UnifiedMatrixBasis.I₂) = (1 / 2 : ℂ) ∧
    jordanProduct A B = jordanProduct B A ∧
    lieProduct B A = - lieProduct A B ∧
    UnifiedMatrixBasis.complexI * UnifiedMatrixBasis.complexJ = UnifiedMatrixBasis.complexK := by
  exact ⟨normalizedPauliSpacetimeMatrix_det c dt dx dy dz,
    normalized_interval_eq_minkowski_minus_plus_plus_plus c dt dx dy dz hc,
    normalized_hilbertSchmidt_identity_self c hc,
    jordanProduct_comm A B,
    lieProduct_antisymm A B,
    md002_quaternion_complex_structure_packet.2.2.2.1⟩

end MD002FoundationalConventions

end noncomputable section
