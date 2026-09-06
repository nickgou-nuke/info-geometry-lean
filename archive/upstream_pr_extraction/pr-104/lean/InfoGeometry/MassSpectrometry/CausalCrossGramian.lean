import Mathlib
import InfoGeometry.MassSpectrometry.DirectedOperatorDoubling
import InfoGeometry.MassSpectrometry.MellinMassEncoding
import InfoGeometry.MassSpectrometry.ValuedFragmentationDAG

/-!
# Causal cross-Gramian and cone-restricted kernels

This module supplies the directed matrix source missing from an auto-Gramian.
For two feature slices `Z₁` and `Z₂`, the cross-Gramian `Z₁ Z₂ᵀ` need not be
symmetric. Causality is imposed separately by rank, mass, or log-mass masks.

The finite KAN-style kernel below is only a parameterization interface: it is a
finite superposition of univariate inner/outer functions on log-mass
coordinates. No Kolmogorov-Arnold representation theorem or spline
approximation theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry


open Matrix
open scoped BigOperators

/-- Cross-Gramian between two feature slices. -/
def crossGramOperator {n₁ n₂ d : ℕ}
    (Z₁ : Matrix (Fin n₁) (Fin d) ℝ)
    (Z₂ : Matrix (Fin n₂) (Fin d) ℝ) :
    Matrix (Fin n₁) (Fin n₂) ℝ :=
  Z₁ * Z₂.transpose

/-- Transposition reverses the order of the two feature slices. -/
theorem crossGramOperator_transpose {n₁ n₂ d : ℕ}
    (Z₁ : Matrix (Fin n₁) (Fin d) ℝ)
    (Z₂ : Matrix (Fin n₂) (Fin d) ℝ) :
    (crossGramOperator Z₁ Z₂).transpose = crossGramOperator Z₂ Z₁ := by
  simp [crossGramOperator, Matrix.transpose_mul]

/-- Auto-Gramians are the diagonal slice of the cross-Gramian construction. -/
theorem crossGramOperator_self_eq_gramOperator {n d : ℕ}
    (Z : Matrix (Fin n) (Fin d) ℝ) :
    crossGramOperator Z Z = gramOperator Z := by
  rfl

/-- Hence the cross-Gramian reduces to the already-proved symmetric Gram owner
when both feature slices coincide. -/
theorem antisymmetricPart_crossGram_self_eq_zero {n d : ℕ}
    (Z : Matrix (Fin n) (Fin d) ℝ) :
    antisymmetricPart (crossGramOperator Z Z) = 0 := by
  simpa [crossGramOperator_self_eq_gramOperator] using
    antisymmetricPart_gramOperator_eq_zero Z

/-- A square cross-Gramian can genuinely have a nonzero antisymmetric part. -/
theorem crossGram_can_have_nonzero_antisymmetricPart :
    ∃ Z₁ Z₂ : Matrix (Fin 2) (Fin 2) ℝ,
      antisymmetricPart (crossGramOperator Z₁ Z₂) ≠ 0 := by
  let Z₁ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
  let Z₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
  refine ⟨Z₁, Z₂, ?_⟩
  intro h
  have hij := congr_fun (congr_fun h (0 : Fin 2)) (1 : Fin 2)
  norm_num [antisymmetricPart, crossGramOperator, Z₁, Z₂,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.vecHead, Matrix.vecCons] at hij

/-! ## Log-mass causal cone -/

/-- A parent/child log-mass pair is forward causal when the child does not
exceed the parent in log mass. -/
def InForwardLogMassCone (τParent τChild : ℝ) : Prop :=
  τChild ≤ τParent

/-- Positive masses preserve their order under the logarithm. -/
theorem inForwardLogMassCone_of_mass_le
    {mParent mChild : ℝ} (hc : 0 < mChild)
    (h : mChild ≤ mParent) :
    InForwardLogMassCone (Real.log mParent) (Real.log mChild) := by
  exact Real.log_le_log hc h

/-- Hard causal mask on a rectangular transfer matrix. -/
def logMassConeMask {n₁ n₂ : ℕ}
    (τ₁ : Fin n₁ → ℝ) (τ₂ : Fin n₂ → ℝ)
    (K : Matrix (Fin n₁) (Fin n₂) ℝ) :
    Matrix (Fin n₁) (Fin n₂) ℝ := by
  classical
  exact fun i j => if InForwardLogMassCone (τ₁ i) (τ₂ j) then K i j else 0

/-- Every nonzero masked transfer lies in the forward log-mass cone. -/
theorem logMassConeMask_support
    {n₁ n₂ : ℕ} (τ₁ : Fin n₁ → ℝ) (τ₂ : Fin n₂ → ℝ)
    (K : Matrix (Fin n₁) (Fin n₂) ℝ) {i : Fin n₁} {j : Fin n₂}
    (h : logMassConeMask τ₁ τ₂ K i j ≠ 0) :
    InForwardLogMassCone (τ₁ i) (τ₂ j) := by
  by_contra hcone
  have hz : logMassConeMask τ₁ τ₂ K i j = 0 := by
    simp [logMassConeMask, hcone]
  exact h hz

/-! ## Finite KAN-style causal parameterization -/

/-- Finite superposition of univariate inner/outer maps on log-mass
coordinates. This is an executable parameterization type, not a universal
representation theorem. -/
structure FiniteKANCausalKernel (q : ℕ) where
  parentInner : Fin q → ℝ → ℝ
  childInner : Fin q → ℝ → ℝ
  outer : Fin q → ℝ → ℝ

namespace FiniteKANCausalKernel

/-- Unmasked finite KAN-style pair potential. -/
def raw {q : ℕ} (Φ : FiniteKANCausalKernel q)
    (τParent τChild : ℝ) : ℝ :=
  ∑ k, Φ.outer k (Φ.parentInner k τParent + Φ.childInner k τChild)

/-- Cone-restricted finite KAN-style causal potential. -/
def causal {q : ℕ} (Φ : FiniteKANCausalKernel q)
    (τParent τChild : ℝ) : ℝ :=
    by
      classical
      exact if InForwardLogMassCone τParent τChild then Φ.raw τParent τChild else 0

/-- The causal parameterization vanishes outside the forward cone. -/
theorem causal_eq_zero_of_not_cone {q : ℕ} (Φ : FiniteKANCausalKernel q)
    {τParent τChild : ℝ} (h : ¬ InForwardLogMassCone τParent τChild) :
    Φ.causal τParent τChild = 0 := by
  simp [causal, h]

/-- Any nonzero KAN-style causal weight is supported in the causal cone. -/
theorem cone_of_causal_ne_zero {q : ℕ} (Φ : FiniteKANCausalKernel q)
    {τParent τChild : ℝ} (h : Φ.causal τParent τChild ≠ 0) :
    InForwardLogMassCone τParent τChild := by
  by_contra hcone
  exact h (Φ.causal_eq_zero_of_not_cone hcone)

end FiniteKANCausalKernel

end InfoGeometry.MassSpectrometry
