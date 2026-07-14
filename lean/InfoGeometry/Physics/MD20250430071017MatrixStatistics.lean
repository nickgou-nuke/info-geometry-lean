import InfoGeometry.Physics.Section38StressEnergyDomainSeparation

/-!
# Repaired MD 20250430071017: finite matrix-valued statistics

Source: `github-nick:nickgou-nuke/MD`, file
`!!!!!!!!!!!!!!20250430071017.md`.

The source is a broad manuscript covering differential geometry, Kähler
geometry, Pauli matrix four-vector representation, exponential families,
quantum state geometry, general relativity, partition functions, and a research
program for emergent spacetime from matrix-valued local statistics.

Most of that text is either standard background, external citation, or open
research debt.  This file extracts the finite theorem-safe bridge that is both
central to the manuscript and already supported by this repository:

* a local configuration is a concrete `2 × 2` complex matrix;
* its sufficient statistics are the four Pauli coefficients;
* every local matrix is recovered from these coefficients by the existing
  Section 33 Pauli-completion theorem;
* finite weighted means of Pauli coefficients are defined;
* finite weighted covariance of these matrix-valued statistics is symmetric;
* a constant local statistic has zero covariance when the weights sum to one.

No smooth-manifold theorem, Einstein equation, Kähler-integrability theorem,
path-integral construction, emergent-spacetime theorem, Lorentzian-signature
emergence theorem, or physical arrow-of-time theorem is asserted.
-/

noncomputable section

namespace MD20250430071017MatrixStatistics

open Matrix Complex BigOperators
open InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite
open InfoGeometry.Physics.Section33PauliBiquaternionCompletion

/-- Local matrix configuration domain from the manuscript: concrete `2 × 2` matrices. -/
abbrev LocalMatrixConfig := Mat2

/-- Four Pauli-coordinate readouts of a local matrix configuration. -/
def pauliCoeffAt (A : LocalMatrixConfig) (k : Fin 4) : ℂ :=
  match k with
  | 0 => pauliCoeff0 A
  | 1 => pauliCoeff1 A
  | 2 => pauliCoeff2 A
  | 3 => pauliCoeff3 A

/-- Pauli recomposition recovers a local matrix configuration. -/
theorem localMatrix_recompose (A : LocalMatrixConfig) :
    pauliRecompose A = A :=
  pauli_recompose_eq_self A

/-- Finite weighted mean of a Pauli-coordinate statistic. -/
def weightedMeanCoeff {ι : Type} [Fintype ι]
    (w : ι → ℂ) (q : ι → LocalMatrixConfig) (k : Fin 4) : ℂ :=
  ∑ i, w i * pauliCoeffAt (q i) k

/-- Centered Pauli-coordinate statistic. -/
def centeredCoeff {ι : Type} [Fintype ι]
    (w : ι → ℂ) (q : ι → LocalMatrixConfig) (i : ι) (k : Fin 4) : ℂ :=
  pauliCoeffAt (q i) k - weightedMeanCoeff w q k

/-- Finite weighted covariance of two Pauli-coordinate statistics. -/
def covarianceCoeff {ι : Type} [Fintype ι]
    (w : ι → ℂ) (q : ι → LocalMatrixConfig) (a b : Fin 4) : ℂ :=
  ∑ i, w i * centeredCoeff w q i a * centeredCoeff w q i b

/-- The finite covariance matrix of Pauli sufficient statistics is symmetric. -/
theorem covarianceCoeff_symmetric {ι : Type} [Fintype ι]
    (w : ι → ℂ) (q : ι → LocalMatrixConfig) (a b : Fin 4) :
    covarianceCoeff w q a b = covarianceCoeff w q b a := by
  unfold covarianceCoeff
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Constant local statistics have zero centered coefficient when weights sum to one. -/
theorem centeredCoeff_zero_of_constant {ι : Type} [Fintype ι]
    (w : ι → ℂ) (A : LocalMatrixConfig) (hwsum : ∑ i, w i = 1)
    (i : ι) (k : Fin 4) :
    centeredCoeff w (fun _ : ι => A) i k = 0 := by
  simp [centeredCoeff, weightedMeanCoeff]
  rw [← Finset.sum_mul]
  rw [hwsum]
  ring

/-- Constant local matrix statistics have zero finite covariance. -/
theorem covarianceCoeff_zero_of_constant {ι : Type} [Fintype ι]
    (w : ι → ℂ) (A : LocalMatrixConfig) (hwsum : ∑ i, w i = 1)
    (a b : Fin 4) :
    covarianceCoeff w (fun _ : ι => A) a b = 0 := by
  simp [covarianceCoeff, centeredCoeff_zero_of_constant (w := w) (A := A) hwsum]

/-- Repaired finite packet for the MD matrix-statistics manuscript. -/
theorem repaired_MD20250430071017_matrix_statistics_packet {ι : Type} [Fintype ι]
    (w : ι → ℂ) (q : ι → LocalMatrixConfig) (A : LocalMatrixConfig)
    (hwsum : ∑ i, w i = 1) :
    (∀ i, pauliRecompose (q i) = q i) ∧
    (∀ a b, covarianceCoeff w q a b = covarianceCoeff w q b a) ∧
    (∀ a b, covarianceCoeff w (fun _ : ι => A) a b = 0) := by
  exact ⟨fun i => localMatrix_recompose (q i),
    fun a b => covarianceCoeff_symmetric w q a b,
    fun a b => covarianceCoeff_zero_of_constant w A hwsum a b⟩

end MD20250430071017MatrixStatistics

end noncomputable section
