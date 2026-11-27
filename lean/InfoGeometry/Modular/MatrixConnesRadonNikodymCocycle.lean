/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ComplexMatrixModularFlowAndCStarPolar
import InfoGeometry.OperatorAlgebra.ConstructiveConnesCocycle

/-!
# Constructive Noncommuting Connes Radon–Nikodym Cocycle on M_n(ℂ) (`F4a`)

For any two Hermitian generators `H_φ, H_ψ : Matrix (Fin n) (Fin n) ℂ` (not
assumed to commute), this module constructs the genuine noncommuting Connes
2×2 matrix amplification (`M₂(M_n(ℂ))`), extracts `(Dψ : Dφ)_t` from the `(2,1)`
block of the balanced modular flow `σ_t^θ(e₂₁)`, proves the cocycle law,
intertwining law, and chain rule, and provides an explicit noncommuting `2 × 2`
witness (`H_diag2` and `H_pauliX`).

Downstream consumers of `PedersenTakesakiRNInterface.lean` remain untouched.
-/

noncomputable section

namespace InfoGeometry.Modular.MatrixConnesRadonNikodymCocycle

open Matrix Complex
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

open InfoGeometry.Canonical.ComplexMatrixModularFlowAndCStarPolar
open InfoGeometry.Modular.ConnesCocycle
open InfoGeometry.OperatorAlgebra.OperatorThermodynamics
open InfoGeometry.OperatorAlgebra.ConstructiveConnesCocycle

/-! =========================================================================
    1. OpenGauss T16 Witness & Scalar Helper
    ========================================================================= -/

/-- Explicit noncommuting `2 × 2` complex matrix witness. -/
theorem mat2_complex_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  InfoGeometry.Modular.ComplexMatrixTomitaDuality.mat2_complex_noncomm_witness

private lemma scalar_neg_add_swap (s t : ℝ) : -(s + t) = -t + -s := by
  ring

/-! =========================================================================
    2. Connes 2×2 Matrix Amplification & Block-Diagonal Exponential
    ========================================================================= -/

section Amplification

variable {n : ℕ}

/-- Connes balanced 2×2 amplification generator `diag(H_φ, H_ψ)` on `M₂(M_n(ℂ))`. -/
def balancedGenerator (Hφ Hψ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks Hφ 0 0 Hψ

theorem balancedGenerator_isHermitian (Hφ Hψ : Matrix (Fin n) (Fin n) ℂ)
    (hφ : Hφ.IsHermitian) (hψ : Hψ.IsHermitian) :
    (balancedGenerator Hφ Hψ).IsHermitian := by
  change (Matrix.fromBlocks Hφ 0 0 Hψ)ᴴ = Matrix.fromBlocks Hφ 0 0 Hψ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, hφ.eq, hψ.eq]

/-- Block-diagonal algebra homomorphism `M_n(ℂ) × M_n(ℂ) →ₐ[ℂ] M_{2n}(ℂ)`. -/
def blockDiagAlgHom (n : ℕ) :
    (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) →ₐ[ℂ]
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ where
  toFun := fun p => Matrix.fromBlocks p.1 0 0 p.2
  map_one' := Matrix.fromBlocks_one
  map_mul' := fun p q => by
    change Matrix.fromBlocks (p.1 * q.1) 0 0 (p.2 * q.2) =
      Matrix.fromBlocks p.1 0 0 p.2 * Matrix.fromBlocks q.1 0 0 q.2
    rw [Matrix.fromBlocks_multiply]
    simp
  map_zero' := Matrix.fromBlocks_zero
  map_add' := fun p q => by
    change Matrix.fromBlocks (p.1 + q.1) 0 0 (p.2 + q.2) =
      Matrix.fromBlocks p.1 0 0 p.2 + Matrix.fromBlocks q.1 0 0 q.2
    ext (i | i) (j | j) <;> simp
  commutes' := fun c => by
    change Matrix.fromBlocks (algebraMap ℂ _ c) 0 0 (algebraMap ℂ _ c) =
      algebraMap ℂ _ c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]

theorem exp_prod_pair {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] (a : A) (b : B) :
    NormedSpace.exp (a, b) = (NormedSpace.exp a, NormedSpace.exp b) := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  letI : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℂ B
  letI : NormedAlgebra ℚ (A × B) := NormedAlgebra.restrictScalars ℚ ℂ (A × B)
  exact Prod.ext
    (NormedSpace.map_exp (AlgHom.fst ℂ A B) continuous_fst (a, b))
    (NormedSpace.map_exp (AlgHom.snd ℂ A B) continuous_snd (a, b))

theorem exp_fromBlocks_diag (A B : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (Matrix.fromBlocks A 0 0 B) =
      Matrix.fromBlocks (NormedSpace.exp A) 0 0 (NormedSpace.exp B) := by
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  letI : NormedAlgebra ℚ (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hcont : Continuous (blockDiagAlgHom n) :=
    (blockDiagAlgHom n).toLinearMap.continuous_of_finiteDimensional
  have hmap := NormedSpace.map_exp (blockDiagAlgHom n) hcont (A, B)
  rw [exp_prod_pair] at hmap
  exact hmap.symm

theorem uExp_balancedGenerator (Hφ Hψ : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • balancedGenerator Hφ Hψ) =
      Matrix.fromBlocks (uExp Hφ t) 0 0 (uExp Hψ t) := by
  have hsmul :
      (Complex.I * (t : ℂ)) • balancedGenerator Hφ Hψ =
        Matrix.fromBlocks ((Complex.I * (t : ℂ)) • Hφ) 0 0 ((Complex.I * (t : ℂ)) • Hψ) := by
    unfold balancedGenerator
    ext (i | i) (j | j) <;> simp
  rw [hsmul, exp_fromBlocks_diag]
  rfl

/-- Lower-left `e₂₁` matrix unit in `M₂(M_n(ℂ))`. -/
def e21Block (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks 0 0 1 0

/-- Connes Radon–Nikodym cocycle `u_t = (Dψ : Dφ)_t = exp(i t H_ψ) exp(-i t H_φ)` on `M_n(ℂ)`. -/
def connesCocycleMatrix (Hψ Hφ : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  uExp Hψ t * uExp Hφ (-t)

/-- Balanced-flow derivation: the `(2, 1)` block of `σ_t^θ(e₂₁)` is `connesCocycleMatrix Hψ Hφ t`. -/
theorem balancedFlow_e21_eq_cocycle (Hφ Hψ : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • balancedGenerator Hφ Hψ) * e21Block n *
        NormedSpace.exp ((Complex.I * ((-t : ℝ) : ℂ)) • balancedGenerator Hφ Hψ) =
      Matrix.fromBlocks 0 0 (connesCocycleMatrix Hψ Hφ t) 0 := by
  rw [uExp_balancedGenerator, uExp_balancedGenerator]
  unfold e21Block connesCocycleMatrix
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one]

/-! =========================================================================
    3. Cocycle Law, Flow Twisting, Chain Rule, and Existing Interfaces
    ========================================================================= -/

theorem connesCocycleMatrix_zero (Hψ Hφ : Matrix (Fin n) (Fin n) ℂ) :
    connesCocycleMatrix Hψ Hφ 0 = 1 := by
  unfold connesCocycleMatrix
  simp [uExp_zero]

theorem connesCocycleMatrix_conjTranspose (Hψ Hφ : Matrix (Fin n) (Fin n) ℂ)
    (hψ : Hψ.IsHermitian) (hφ : Hφ.IsHermitian) (t : ℝ) :
    (connesCocycleMatrix Hψ Hφ t)ᴴ = uExp Hφ t * uExp Hψ (-t) := by
  unfold connesCocycleMatrix
  rw [Matrix.conjTranspose_mul, uExp_conjTranspose Hφ hφ (-t),
    uExp_conjTranspose Hψ hψ t, neg_neg]

theorem connesCocycleMatrix_cocycle_id (Hψ Hφ : Matrix (Fin n) (Fin n) ℂ)
    (hφ : Hφ.IsHermitian) (s t : ℝ) :
    connesCocycleMatrix Hψ Hφ (s + t) =
      connesCocycleMatrix Hψ Hφ s *
        matrixModularFlow Hφ hφ s (connesCocycleMatrix Hψ Hφ t) := by
  unfold connesCocycleMatrix
  rw [matrixModularFlow_apply, uExp_add Hψ s t, scalar_neg_add_swap s t, uExp_add Hφ (-t) (-s)]
  calc
    (uExp Hψ s * uExp Hψ t) * (uExp Hφ (-t) * uExp Hφ (-s))
        = uExp Hψ s * (uExp Hφ (-s) * uExp Hφ s) * (uExp Hψ t * uExp Hφ (-t)) * uExp Hφ (-s) := by
      rw [← uExp_add Hφ (-s) s, neg_add_cancel, uExp_zero, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = (uExp Hψ s * uExp Hφ (-s)) * (uExp Hφ s * (uExp Hψ t * uExp Hφ (-t)) * uExp Hφ (-s)) := by
      simp only [Matrix.mul_assoc]

/-- Constructive `ConnesCocycle.ConnesOneCocycle` for any two Hermitian generators. -/
def matrixConnesOneCocycle (Hψ Hφ : Matrix (Fin n) (Fin n) ℂ)
    (hψ : Hψ.IsHermitian) (hφ : Hφ.IsHermitian) :
    ConnesOneCocycle (matrixModularFlow Hφ hφ) where
  u := connesCocycleMatrix Hψ Hφ
  cocycle_id := connesCocycleMatrix_cocycle_id Hψ Hφ hφ
  cocycle_zero := connesCocycleMatrix_zero Hψ Hφ
  unitary_left := fun t => by
    change connesCocycleMatrix Hψ Hφ t * (connesCocycleMatrix Hψ Hφ t)ᴴ = 1
    rw [connesCocycleMatrix_conjTranspose Hψ Hφ hψ hφ t]
    unfold connesCocycleMatrix
    calc
      (uExp Hψ t * uExp Hφ (-t)) * (uExp Hφ t * uExp Hψ (-t))
          = uExp Hψ t * (uExp Hφ (-t) * uExp Hφ t) * uExp Hψ (-t) := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [← uExp_add, neg_add_cancel, uExp_zero, Matrix.mul_one, ← uExp_add,
          add_neg_cancel, uExp_zero]
  unitary_right := fun t => by
    change (connesCocycleMatrix Hψ Hφ t)ᴴ * connesCocycleMatrix Hψ Hφ t = 1
    rw [connesCocycleMatrix_conjTranspose Hψ Hφ hψ hφ t]
    unfold connesCocycleMatrix
    calc
      (uExp Hφ t * uExp Hψ (-t)) * (uExp Hψ t * uExp Hφ (-t))
          = uExp Hφ t * (uExp Hψ (-t) * uExp Hψ t) * uExp Hφ (-t) := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [← uExp_add, neg_add_cancel, uExp_zero, Matrix.mul_one, ← uExp_add,
          add_neg_cancel, uExp_zero]

/-- Exact cocycle intertwining theorem: `σ_t^ψ(X) = u_t * σ_t^φ(X) * u_tᴴ`. -/
theorem matrixConnes_perturbedFlow_eq (Hψ Hφ : Matrix (Fin n) (Fin n) ℂ)
    (hψ : Hψ.IsHermitian) (hφ : Hφ.IsHermitian) (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    perturbedFlow (matrixConnesOneCocycle Hψ Hφ hψ hφ) t X =
      matrixModularFlow Hψ hψ t X := by
  dsimp [perturbedFlow, matrixConnesOneCocycle, matrixModularFlow]
  change connesCocycleMatrix Hψ Hφ t * (uExp Hφ t * X * uExp Hφ (-t)) *
      (connesCocycleMatrix Hψ Hφ t)ᴴ = uExp Hψ t * X * uExp Hψ (-t)
  rw [connesCocycleMatrix_conjTranspose Hψ Hφ hψ hφ t]
  unfold connesCocycleMatrix
  calc
    (uExp Hψ t * uExp Hφ (-t)) * (uExp Hφ t * X * uExp Hφ (-t)) * (uExp Hφ t * uExp Hψ (-t))
        = uExp Hψ t * ((uExp Hφ (-t) * uExp Hφ t) * X * (uExp Hφ (-t) * uExp Hφ t)) * uExp Hψ (-t) := by
      simp only [Matrix.mul_assoc]
    _ = uExp Hψ t * X * uExp Hψ (-t) := by
      rw [← uExp_add, neg_add_cancel, uExp_zero, Matrix.one_mul, Matrix.mul_one]

/-- Noncommuting Connes cocycle chain rule `(Dχ : Dφ)_t = (Dχ : Dψ)_t * (Dψ : Dφ)_t`. -/
theorem connesCocycleMatrix_chain_rule (Hχ Hψ Hφ : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    connesCocycleMatrix Hχ Hφ t =
      connesCocycleMatrix Hχ Hψ t * connesCocycleMatrix Hψ Hφ t := by
  unfold connesCocycleMatrix
  calc
    uExp Hχ t * uExp Hφ (-t)
        = uExp Hχ t * (uExp Hψ (-t) * uExp Hψ t) * uExp Hφ (-t) := by
      rw [← uExp_add, neg_add_cancel, uExp_zero, Matrix.mul_one]
    _ = (uExp Hχ t * uExp Hψ (-t)) * (uExp Hψ t * uExp Hφ (-t)) := by
      simp only [Matrix.mul_assoc]

/-- Constructive `ConstructiveConnesCocycle.ConnesCocycleData` on `M_n(ℂ)`. -/
def matrixConnesCocycleData (Hψ Hφ : Matrix (Fin n) (Fin n) ℂ)
    (hψ : Hψ.IsHermitian) (hφ : Hφ.IsHermitian) :
    ConnesCocycleData (Matrix (Fin n) (Fin n) ℂ)
      (matrixOperatorFlow Hψ hψ) (matrixOperatorFlow Hφ hφ) where
  u := connesCocycleMatrix Hψ Hφ

theorem matrixConnesCocycleData_isConnesCocycle (Hψ Hφ : Matrix (Fin n) (Fin n) ℂ)
    (hψ : Hψ.IsHermitian) (hφ : Hφ.IsHermitian) :
    IsConnesCocycle (matrixConnesCocycleData Hψ Hφ hψ hφ) :=
  connesCocycleMatrix_cocycle_id Hψ Hφ hφ

theorem matrixConnesCocycleData_intertwines (Hψ Hφ : Matrix (Fin n) (Fin n) ℂ)
    (hψ : Hψ.IsHermitian) (hφ : Hφ.IsHermitian) :
    Intertwines (matrixConnesCocycleData Hψ Hφ hψ hφ) := by
  intro t X
  change matrixModularFlow Hψ hψ t X * connesCocycleMatrix Hψ Hφ t =
    connesCocycleMatrix Hψ Hφ t * matrixModularFlow Hφ hφ t X
  rw [matrixModularFlow_apply, matrixModularFlow_apply]
  unfold connesCocycleMatrix
  calc
    (uExp Hψ t * X * uExp Hψ (-t)) * (uExp Hψ t * uExp Hφ (-t))
        = uExp Hψ t * X * (uExp Hψ (-t) * uExp Hψ t) * uExp Hφ (-t) := by
      simp only [Matrix.mul_assoc]
    _ = uExp Hψ t * X * uExp Hφ (-t) := by
      rw [← uExp_add, neg_add_cancel, uExp_zero, Matrix.mul_one]
    _ = uExp Hψ t * (uExp Hφ (-t) * uExp Hφ t) * X * uExp Hφ (-t) := by
      rw [← uExp_add, neg_add_cancel, uExp_zero, Matrix.mul_one]
    _ = (uExp Hψ t * uExp Hφ (-t)) * (uExp Hφ t * X * uExp Hφ (-t)) := by
      simp only [Matrix.mul_assoc]

/-! =========================================================================
    4. Explicit Noncommuting 2 × 2 Witness (H_diag2 and H_pauliX)
    ========================================================================= -/

/-- Diagonal `2 × 2` Hermitian generator `diag(0, 1)`. -/
def H_diag2 : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![0, 0], ![0, 1]]

/-- Off-diagonal Pauli-X `2 × 2` Hermitian generator. -/
def H_pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![0, 1], ![1, 0]]

theorem H_diag2_isHermitian : H_diag2.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H_diag2]

theorem H_pauliX_isHermitian : H_pauliX.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H_pauliX]

/-- Explicit witness that the two modular generators do not commute. -/
theorem H_diag2_H_pauliX_noncommute : H_diag2 * H_pauliX ≠ H_pauliX * H_diag2 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  have hL : (H_diag2 * H_pauliX) 0 1 = 0 := by
    simp [H_diag2, H_pauliX, Matrix.mul_apply, Fin.sum_univ_two]
  have hR : (H_pauliX * H_diag2) 0 1 = 1 := by
    simp [H_diag2, H_pauliX, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hL, hR] at h01
  exact zero_ne_one h01

/-- Explicit noncommuting 2×2 Connes 1-cocycle instance. -/
def pauliDiagConnesCocycle :
    ConnesOneCocycle (matrixModularFlow H_diag2 H_diag2_isHermitian) :=
  matrixConnesOneCocycle H_pauliX H_diag2 H_pauliX_isHermitian H_diag2_isHermitian

end Amplification

end InfoGeometry.Modular.MatrixConnesRadonNikodymCocycle
