import InfoGeometry.Categorical.FibonacciBraiding
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.FibonacciBraidedTowerCone
import InfoGeometry.Fibonacci.FibAnyonThm1

/-!
# Fibonacci Fusion Category Data

Kernel-checked finite data for the Fibonacci fusion-category lane.

This file deliberately does **not** declare a `BraidedCategory` instance. A
mathlib `BraidedCategory` instance needs an actual category, tensor product,
associator, braiding natural isomorphisms, and pentagon/hexagon coherence
proofs. The finite data below are the honest inputs toward that construction:

* the two simple labels `𝟙` and `τ`;
* the fusion multiplicities for `τ ⊗ τ = 𝟙 ⊕ τ`;
* the regular fusion matrix `N_τ`;
* the golden-ratio Perron-Frobenius eigenvector of `N_τ`;
* a theorem-only readout of the existing owner theorems for the finite `F`,
  `R`, and `B = F R F` matrices.

No theorem here replaces `InfoGeometry.Categorical.FibonacciBraiding`; this file
only organizes its inputs.
-/

namespace InfoGeometry.Categorical.FibonacciFusionCategoryData

open Matrix
open Set
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Categorical.FibonacciBraiding

/-! ## Simple labels and fusion multiplicities -/

/-- The two simple labels of the skeletal Fibonacci fusion rule. -/
inductive FibSimple : Type
  | unit
  | tau
  deriving DecidableEq, Repr

namespace FibSimple

/-- Fusion multiplicity `N_ab^c` for the skeletal Fibonacci fusion rule. -/
def fusionMultiplicity : FibSimple → FibSimple → FibSimple → ℕ
  | unit, unit, unit => 1
  | unit, tau, tau => 1
  | tau, unit, tau => 1
  | tau, tau, unit => 1
  | tau, tau, tau => 1
  | _, _, _ => 0

@[simp] theorem fusion_unit_unit :
    fusionMultiplicity unit unit unit = 1 := rfl

@[simp] theorem fusion_unit_tau :
    fusionMultiplicity unit tau tau = 1 := rfl

@[simp] theorem fusion_tau_unit :
    fusionMultiplicity tau unit tau = 1 := rfl

@[simp] theorem fusion_tau_tau_unit :
    fusionMultiplicity tau tau unit = 1 := rfl

@[simp] theorem fusion_tau_tau_tau :
    fusionMultiplicity tau tau tau = 1 := rfl

/-- `𝟙` appears in `τ ⊗ τ`. -/
theorem unit_mem_tau_tensor_tau :
    fusionMultiplicity tau tau unit = 1 :=
  rfl

/-- `τ` appears in `τ ⊗ τ`. -/
theorem tau_mem_tau_tensor_tau :
    fusionMultiplicity tau tau tau = 1 :=
  rfl

end FibSimple

/-! ## Regular fusion matrices -/

/-- The regular fusion matrix for the tensor unit. -/
def N_unit : Matrix (Fin 2) (Fin 2) ℕ :=
  1

/-- The regular fusion matrix for `τ`, with basis ordered as `(𝟙, τ)`. -/
def N_tau : Matrix (Fin 2) (Fin 2) ℕ :=
  !![0, 1; 1, 1]

/-- Matrix form of the fusion-ring relation `τ² = 𝟙 + τ`. -/
theorem N_tau_sq_eq_N_unit_add_N_tau :
    N_tau * N_tau = N_unit + N_tau := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N_tau, N_unit, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Golden-ratio scaling -/

/-- The real matrix underlying `N_τ`. -/
noncomputable def N_tau_real : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 1]

/-- The positive golden ratio from the existing Fibonacci archive theorem. -/
noncomputable abbrev goldenRatio : ℝ :=
  InfoGeometry.Fibonacci.FibAnyonThm1.φ

/-- Perron-Frobenius eigenvector for the Fibonacci fusion matrix. -/
noncomputable def goldenEigenvector : Fin 2 → ℝ :=
  ![1, goldenRatio]

/--
The finite fusion matrix scales the positive eigenvector by the golden ratio.
This is the kernel-checked algebraic core of the quantum-dimension readout.
-/
theorem N_tau_real_mulVec_goldenEigenvector :
    N_tau_real.mulVec goldenEigenvector = goldenRatio • goldenEigenvector := by
  ext i
  fin_cases i
  · simp [N_tau_real, goldenEigenvector, goldenRatio, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  · simp [N_tau_real, goldenEigenvector, goldenRatio, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    nlinarith [InfoGeometry.Fibonacci.FibAnyonThm1.golden_identity]

/-! ## Finite braiding theorem-only readout -/

/--
Owner-backed readout for the finite Fibonacci braiding data:
`F² = 1`, `det F = -1`, `B = F R F`, and the supplied Artin relation.

The Artin equality is intentionally an explicit matrix hypothesis. This avoids
claiming an analytic hexagon/phase proof before the cyclotomic computation is
formalized in Lean.
-/
theorem finite_braiding_input_readout
    (q : Units ℂ) (τ s : ℂ)
    (s_sq : s ^ 2 = τ)
    (tau_sq_add_tau : τ ^ 2 + τ = 1)
    (artin :
      fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q =
        fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s) :
    fibonacciFusionMatrix τ s * fibonacciFusionMatrix τ s = 1 ∧
      (fibonacciFusionMatrix τ s).det = -1 ∧
      fibonacciBMatrix q τ s =
        fibonacciFusionMatrix τ s * fibonacciRMatrix q * fibonacciFusionMatrix τ s ∧
      fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q =
        fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s := by
  exact ⟨
    F_sq τ s s_sq tau_sq_add_tau,
    det_F τ s s_sq tau_sq_add_tau,
    B_eq_FRF q τ s,
    artin⟩

/-! ## Zorn/inductive-support readout -/

/--
The order-theoretic maximal-support statement used by the tower construction,
re-exported here as the Zorn/inductive-poset component of the same formalization
lane.
-/
theorem zorn_inductive_support_readout
    (family : Set (Set ℕ))
    (chain_sUnion_mem : ∀ c ⊆ family, IsChain (· ⊆ ·) c → ⋃₀ c ∈ family)
    (nonempty : family.Nonempty) :
    ∃ M ∈ family, ∀ X ∈ family, M ⊆ X → X = M :=
  InfoGeometry.Categorical.FibonacciBraidedTowerCone.zorn_maximal_support
    family chain_sUnion_mem nonempty

end InfoGeometry.Categorical.FibonacciFusionCategoryData
