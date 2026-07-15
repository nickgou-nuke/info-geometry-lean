import InfoGeometry.Topology.EckmannDiscreteHodge

/-!
# Discrete Hodge Stabilizer Code Surface

Finite theorem layer identifying the degree-one stabilizer Hamiltonian with the
Eckmann/Hodge Laplacian

```text
  L₁ = d₁ᵀ d₁ + d₀ d₀ᵀ
```

and proving the code-space protection readout:

* harmonic one-forms are annihilated by the vertex and face stabilizer checks;
* harmonic one-forms are orthogonal to exact and coexact local error sectors.

This module is finite-dimensional and matrix-level.  It does not assert a
toric-code model, a Pauli operator representation, an analytic Hodge
decomposition theorem, or a continuum/anyon theorem.

#### BUCKET 1: CLOSED FINITE THEOREMS
The degree-one stabilizer Hamiltonian is definitionally the Eckmann/Hodge
Laplacian; its quadratic form is the sum of face and vertex stabilizer
energies; its kernel is exactly the closed/coclosed degree-one code space;
and harmonic code states are orthogonal to exact and coexact local error
sectors.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
The exact/coexact local-error sectors are orthogonal under the explicit
cochain-complex premise `d₁ d₀ = 0`.

#### BUCKET 3: OPEN CLOSURE DEBT
None.  Non-finite analytic Hodge theory, Pauli stabilizer representations,
and continuum quantum-field claims are intentionally outside this file.
-/

open Matrix

namespace DiscreteHodgeStabilizer

noncomputable section

open EckmannDiscreteHodge

variable {n0 n1 n2 : ℕ}

/-- The degree-one stabilizer/Hodge Hamiltonian. -/
def stabilizerHamiltonian1
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ) :
    Matrix (Fin n1) (Fin n1) ℝ :=
  eckmannLaplacian1 d0 d1

/-- Face-check energy `‖d₁x‖²`, the curl/flux stabilizer term. -/
def faceStabilizerEnergy
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : Fin n1 → ℝ) : ℝ :=
  eckmannDot (d1.mulVec x) (d1.mulVec x)

/-- Vertex-check energy `‖d₀ᵀx‖²`, the divergence/charge stabilizer term. -/
def vertexStabilizerEnergy
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (x : Fin n1 → ℝ) : ℝ :=
  eckmannDot (d0.transpose.mulVec x) (d0.transpose.mulVec x)

/-- The local stabilizer energy on one-forms. -/
def stabilizerEnergy1
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : Fin n1 → ℝ) : ℝ :=
  faceStabilizerEnergy d1 x + vertexStabilizerEnergy d0 x

/-- Exact one-forms: local gradient/phase-error sector. -/
def IsExactOneForm
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (x : Fin n1 → ℝ) : Prop :=
  ∃ φ : Fin n0 → ℝ, d0.mulVec φ = x

/-- Coexact one-forms: local curl/current-error sector. -/
def IsCoexactOneForm
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : Fin n1 → ℝ) : Prop :=
  ∃ ψ : Fin n2 → ℝ, d1.transpose.mulVec ψ = x

/-- Harmonic one-forms: stabilizer code space at degree one. -/
def IsHarmonicCodeState
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : Fin n1 → ℝ) : Prop :=
  eckmannHarmonic1 d0 d1 x

theorem stabilizerHamiltonian1_eq_hodgeLaplacian1
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ) :
    stabilizerHamiltonian1 d0 d1 = eckmannLaplacian1 d0 d1 :=
  rfl

/--
The stabilizer Hamiltonian quadratic form is exactly the sum of the face and
vertex stabilizer energies.
-/
theorem stabilizerEnergy1_eq_hamiltonian_quadratic
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : Fin n1 → ℝ) :
    stabilizerEnergy1 d0 d1 x =
      eckmannDot x ((stabilizerHamiltonian1 d0 d1).mulVec x) := by
  rw [stabilizerEnergy1, faceStabilizerEnergy, vertexStabilizerEnergy,
    stabilizerHamiltonian1, eckmannLaplacian1_quadratic]

/--
The degree-one stabilizer Hamiltonian has the same kernel as the closed and
coclosed harmonic conditions.
-/
theorem stabilizerHamiltonian1_kernel_iff_harmonic
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : Fin n1 → ℝ) :
    (stabilizerHamiltonian1 d0 d1).mulVec x = 0 ↔
      IsHarmonicCodeState d0 d1 x := by
  exact eckmannLaplacian1_mulVec_eq_zero_iff_harmonic d0 d1 x

/-- The closed/coclosed code-space conditions are the Hamiltonian kernel. -/
theorem harmonic_iff_stabilizerHamiltonian1_kernel
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (x : Fin n1 → ℝ) :
    IsHarmonicCodeState d0 d1 x ↔
      (stabilizerHamiltonian1 d0 d1).mulVec x = 0 := by
  exact (stabilizerHamiltonian1_kernel_iff_harmonic d0 d1 x).symm

/-- Harmonic code states are annihilated by the face and vertex checks. -/
theorem harmonicCodeState_annihilated_by_stabilizers
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    {u : Fin n1 → ℝ}
    (hu : IsHarmonicCodeState d0 d1 u) :
    d1.mulVec u = 0 ∧ d0.transpose.mulVec u = 0 :=
  hu

/-- Harmonic code states are orthogonal to exact local error forms. -/
theorem harmonic_orthogonal_exact
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    {u e : Fin n1 → ℝ}
    (hu : IsHarmonicCodeState d0 d1 u)
    (he : IsExactOneForm d0 e) :
    eckmannDot u e = 0 := by
  rcases he with ⟨φ, hφ⟩
  calc
    eckmannDot u e = eckmannDot u (d0.mulVec φ) := by rw [← hφ]
    _ = eckmannDot (d0.mulVec φ) u := by rw [eckmannDot_comm]
    _ = eckmannDot φ (d0.transpose.mulVec u) := by
      rw [eckmannDot_mulVec_transpose]
    _ = eckmannDot φ 0 := by rw [hu.2]
    _ = 0 := eckmannDot_zero_right φ

/-- Harmonic code states are orthogonal to coexact local error forms. -/
theorem harmonic_orthogonal_coexact
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    {u c : Fin n1 → ℝ}
    (hu : IsHarmonicCodeState d0 d1 u)
    (hc : IsCoexactOneForm d1 c) :
    eckmannDot u c = 0 := by
  rcases hc with ⟨ψ, hψ⟩
  calc
    eckmannDot u c = eckmannDot u (d1.transpose.mulVec ψ) := by rw [← hψ]
    _ = eckmannDot (d1.mulVec u) ψ := by
      rw [eckmannDot_mulVec_transpose]
    _ = eckmannDot 0 ψ := by rw [hu.1]
    _ = 0 := eckmannDot_zero_left ψ

/-- Exact local errors and coexact local errors are orthogonal in a cochain complex. -/
theorem exact_orthogonal_coexact
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (hComplex : eckmannDegreeOneCochainComplex d0 d1)
    {e c : Fin n1 → ℝ}
    (he : IsExactOneForm d0 e)
    (hc : IsCoexactOneForm d1 c) :
    eckmannDot e c = 0 := by
  rcases he with ⟨φ, hφ⟩
  rcases hc with ⟨ψ, hψ⟩
  rw [← hφ, ← hψ]
  exact eckmann_coboundary_orthogonal_coexact d0 d1 hComplex φ ψ

/--
Core stabilizer-protection readout: the harmonic/code sector is orthogonal to
both local exact and local coexact error sectors.
-/
theorem hodge_orthogonal_protection
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    {u e c : Fin n1 → ℝ}
    (hu : IsHarmonicCodeState d0 d1 u)
    (he : IsExactOneForm d0 e)
    (hc : IsCoexactOneForm d1 c) :
    eckmannDot u e = 0 ∧ eckmannDot u c = 0 :=
  ⟨harmonic_orthogonal_exact d0 d1 hu he,
    harmonic_orthogonal_coexact d0 d1 hu hc⟩

end

end DiscreteHodgeStabilizer
