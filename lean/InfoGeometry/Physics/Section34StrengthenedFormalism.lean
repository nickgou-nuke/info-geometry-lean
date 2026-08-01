import InfoGeometry.Physics.Section33PauliBiquaternionCompletion
import InfoGeometry.Physics.Section31UnifiedMatrixDynamics

/-!
# Section 34 repaired: strengthened finite formalism

The source tries to strengthen the previous quaternionic-emergent-spacetime
claims by adding variational Einstein equations, entanglement/connection
formulae, a matrix-biquaternion isomorphism, and Lorentz transformations.

This repaired owner keeps the theorem-safe finite core only:

* the covariant derivative of a density matrix is the explicit matrix formula
  `∂ρ + [Γ,ρ]`;
* the algebraic stress-shadow
  `Tr(ρ_μρ_ν) - 1/2 g_{μν} kinetic + g_{μν}V` is symmetric when `g` is
  symmetric;
* the source's displayed matrix-biquaternion basis is repaired as a concrete
  Pauli matrix table.  Its ordering is not the same as Section 30's quaternion
  convention: here `i ↦ Iσ₂`, `j ↦ Iσ₁`, `k ↦ Iσ₃`, which does satisfy
  `i²=j²=k²=-1` and `ij=k`, `jk=i`, `ki=j`.

The continuum action variation, Einstein equations, entanglement-to-connection
reconstruction, Lorentz boost exponentials, holographic area laws, and
phenomenological predictions remain closure debt; they are not asserted here.
-/

noncomputable section

namespace InfoGeometry.Physics.Section34StrengthenedFormalism

open Matrix Complex
open BigOperators
open InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite
open InfoGeometry.Physics.Section31UnifiedMatrixDynamics

abbrev SpacetimeIndex := Fin 4

/-! ## Finite density covariant derivative and stress shadow -/

/-- Finite density covariant derivative `∇ρ = ∂ρ + [Γ,ρ]`. -/
def covariantDensityDerivative (dRho Gamma rho : Mat2) : Mat2 :=
  dRho + Section31UnifiedMatrixDynamics.commutator Gamma rho

/-- With zero connection, the finite covariant derivative is the partial derivative. -/
theorem covariantDensityDerivative_zero_connection (dRho rho : Mat2) :
    covariantDensityDerivative dRho 0 rho = dRho := by
  simp [covariantDensityDerivative, Section31UnifiedMatrixDynamics.commutator]

/-- With zero partial derivative, the finite covariant derivative is commutator action. -/
theorem covariantDensityDerivative_zero_partial (Gamma rho : Mat2) :
    covariantDensityDerivative 0 Gamma rho =
      Section31UnifiedMatrixDynamics.commutator Gamma rho := by
  simp [covariantDensityDerivative]

/-- Trace cyclicity for the concrete `2 × 2` matrix carrier. -/
theorem trace_mul_comm_mat2 (A B : Mat2) :
    trace (A * B) = trace (B * A) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Kinetic scalar shadow `g^{ab} Tr(ρ_a ρ_b)` at the finite matrix level. -/
def kineticTrace (g : SpacetimeIndex → SpacetimeIndex → ℂ)
    (rhoD : SpacetimeIndex → Mat2) : ℂ :=
  ∑ a, ∑ b, g a b * trace (rhoD a * rhoD b)

/-- Finite repaired stress-energy shadow from density derivatives. -/
def densityStressShadow (g : SpacetimeIndex → SpacetimeIndex → ℂ)
    (rhoD : SpacetimeIndex → Mat2) (V : ℂ) (mu nu : SpacetimeIndex) : ℂ :=
  trace (rhoD mu * rhoD nu) -
    (1 / 2 : ℂ) * g mu nu * kineticTrace g rhoD + g mu nu * V

/-- The finite stress shadow is symmetric when the metric coefficient table is symmetric. -/
theorem densityStressShadow_symmetric
    (g : SpacetimeIndex → SpacetimeIndex → ℂ)
    (rhoD : SpacetimeIndex → Mat2) (V : ℂ)
    (hg : ∀ a b, g a b = g b a) (mu nu : SpacetimeIndex) :
    densityStressShadow g rhoD V mu nu = densityStressShadow g rhoD V nu mu := by
  simp [densityStressShadow, hg mu nu]
  rw [trace_mul_comm_mat2]

/-! ## Source-compatible matrix-biquaternion table -/

/-- Source Section 34 image of the biquaternion unit `1`. -/
def bqOne : Mat2 :=
  1

/-- Source Section 34 image of quaternion `i`: `Iσ₂ = [[0,1],[-1,0]]`. -/
def bqI : Mat2 :=
  Complex.I • σ2

/-- Source Section 34 image of quaternion `j`: `Iσ₁ = [[0,I],[I,0]]`. -/
def bqJ : Mat2 :=
  Complex.I • σ1

/-- Source Section 34 image of quaternion `k`: `Iσ₃ = [[I,0],[0,-I]]`. -/
def bqK : Mat2 :=
  Complex.I • σ3

/-- The displayed source matrix for `i` is exactly `Iσ₂`. -/
theorem bqI_entries :
    bqI = !![(0 : ℂ), 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bqI, σ2]

/-- The displayed source matrix for `j` is exactly `Iσ₁`. -/
theorem bqJ_entries :
    bqJ = !![(0 : ℂ), Complex.I; Complex.I, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bqJ, σ1]

/-- The displayed source matrix for `k` is exactly `Iσ₃`. -/
theorem bqK_entries :
    bqK = !![Complex.I, 0; 0, -Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bqK, σ3]

/-- `i²=-1` in the source-compatible matrix table. -/
theorem bqI_sq : bqI * bqI = -1 := by
  unfold bqI
  rw [smul_mul_smul, sigma2_sq, Complex.I_mul_I]
  simp

/-- `j²=-1` in the source-compatible matrix table. -/
theorem bqJ_sq : bqJ * bqJ = -1 := by
  unfold bqJ
  rw [smul_mul_smul, sigma1_sq, Complex.I_mul_I]
  simp

/-- `k²=-1` in the source-compatible matrix table. -/
theorem bqK_sq : bqK * bqK = -1 := by
  unfold bqK
  rw [smul_mul_smul, sigma3_sq, Complex.I_mul_I]
  simp

/-- `ij=k` in the source-compatible matrix table. -/
theorem bqI_mul_bqJ : bqI * bqJ = bqK := by
  unfold bqI bqJ bqK
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ1, σ2, σ3, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- `jk=i` in the source-compatible matrix table. -/
theorem bqJ_mul_bqK : bqJ * bqK = bqI := by
  unfold bqI bqJ bqK
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ1, σ2, σ3, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- `ki=j` in the source-compatible matrix table. -/
theorem bqK_mul_bqI : bqK * bqI = bqJ := by
  unfold bqI bqJ bqK
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ1, σ2, σ3, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- The source-compatible finite table has quaternion volume product `ijk=-1`. -/
theorem bqI_mul_bqJ_mul_bqK : bqI * bqJ * bqK = -1 := by
  rw [bqI_mul_bqJ, bqK_sq]

/-- Repaired Section 34 finite packet: stress symmetry and matrix-biquaternion table. -/
theorem repaired_section34_strengthened_formalism_packet
    (g : SpacetimeIndex → SpacetimeIndex → ℂ)
    (rhoD : SpacetimeIndex → Mat2) (V : ℂ)
    (hg : ∀ a b, g a b = g b a) :
    (∀ mu nu, densityStressShadow g rhoD V mu nu =
      densityStressShadow g rhoD V nu mu) ∧
    bqI * bqI = -1 ∧ bqJ * bqJ = -1 ∧ bqK * bqK = -1 ∧
    bqI * bqJ = bqK ∧ bqJ * bqK = bqI ∧ bqK * bqI = bqJ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro mu nu
    exact densityStressShadow_symmetric g rhoD V hg mu nu
  · exact bqI_sq
  · exact bqJ_sq
  · exact bqK_sq
  · exact bqI_mul_bqJ
  · exact bqJ_mul_bqK
  · exact bqK_mul_bqI

end InfoGeometry.Physics.Section34StrengthenedFormalism

end noncomputable section
