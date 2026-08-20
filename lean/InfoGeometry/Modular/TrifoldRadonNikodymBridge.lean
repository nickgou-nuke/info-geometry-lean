import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

/-!
# Graded Trifold Decomposition and Logarithmic Radon–Nikodym Derivations

This module formalizes:
1. The exact trifold decomposition of block-diagonal modular surprisals:
   `K = α • I + β • Γ + K₀`
   where `Tr(K₀) = 0` and `STr(K₀) = 0`.
2. The inner modular derivation `ad_K(X) = [K, X]` and the logarithmic Radon–Nikodym
   homomorphism `dlog_D(uv) = dlog_D(u) + dlog_D(v)`.

All proofs are complete in native Mathlib with zero `sorry`s.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

open Matrix
open BigOperators

namespace InfoGeometry.Modular

/-!
=============================================================================
PART 1: The Graded Trifold Decomposition on Doubled Block Spaces
=============================================================================
-/

section TrifoldDecomposition

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

local notation "BlockMat" => Matrix (ι ⊕ ι) (ι ⊕ ι) R
local notation "SubMat" => Matrix ι ι R

/-- The Identity matrix on the doubled space: I₂ₙ = [[1, 0], [0, 1]]. -/
def identityDoubled : BlockMat :=
  fromBlocks (1 : SubMat) 0 0 (1 : SubMat)

/-- The Involutive Grading Operator: Γ = [[1, 0], [0, -1]]. -/
def Gamma : BlockMat :=
  fromBlocks (1 : SubMat) 0 0 (-1 : SubMat)

/-- The Supertrace of a block matrix: STr(M) = Tr(Γ * M). -/
def superTrace (M : BlockMat) : R :=
  Matrix.trace (Gamma * M)

/-- A block-diagonal modular operator K = [[A, 0], [0, B]]. -/
def blockDiag (A B : SubMat) : BlockMat :=
  fromBlocks A 0 0 B

/-! ### Basic Block Trace Lemmas -/

@[simp]
theorem trace_fromBlocks_diag (A B : SubMat) :
    Matrix.trace (fromBlocks A (0 : SubMat) (0 : SubMat) B) =
      Matrix.trace A + Matrix.trace B := by
  simp [Matrix.trace, Fintype.sum_sum_type]

@[simp]
theorem trace_identityDoubled :
    Matrix.trace (identityDoubled : BlockMat) =
      (2 : R) * (Fintype.card ι : R) := by
  dsimp [identityDoubled]
  rw [trace_fromBlocks_diag, Matrix.trace_one]
  ring

@[simp]
theorem trace_Gamma :
    Matrix.trace (Gamma : BlockMat) = 0 := by
  dsimp [Gamma]
  rw [trace_fromBlocks_diag, Matrix.trace_one, Matrix.trace_neg, Matrix.trace_one]
  ring

@[simp]
theorem superTrace_identityDoubled :
    superTrace (identityDoubled : BlockMat) = 0 := by
  dsimp [superTrace, identityDoubled, Gamma]
  have h_mul : fromBlocks (1 : SubMat) 0 0 (-1 : SubMat) * fromBlocks (1 : SubMat) 0 0 (1 : SubMat) =
      fromBlocks (1 : SubMat) 0 0 (-1 : SubMat) := by
    rw [fromBlocks_multiply]
    simp
  rw [h_mul, trace_fromBlocks_diag, Matrix.trace_one, Matrix.trace_neg, Matrix.trace_one]
  ring

@[simp]
theorem trace_blockDiag (A B : SubMat) :
    Matrix.trace (blockDiag A B) = Matrix.trace A + Matrix.trace B := by
  dsimp [blockDiag]
  exact trace_fromBlocks_diag A B

@[simp]
theorem superTrace_blockDiag (A B : SubMat) :
    superTrace (blockDiag A B) = Matrix.trace A - Matrix.trace B := by
  dsimp [superTrace, Gamma, blockDiag]
  have h_mul : fromBlocks (1 : SubMat) 0 0 (-1 : SubMat) * fromBlocks A 0 0 B =
      fromBlocks A 0 0 (-B) := by
    rw [fromBlocks_multiply]
    simp
  rw [h_mul, trace_fromBlocks_diag, Matrix.trace_neg]
  ring

/-! ### The Trifold Scalings and the Residual Shape Operator K₀ -/

/-- The Common Weyl Mode: α = Tr(K) / 2n -/
def alphaCommon (two_n_inv : R) (A B : SubMat) : R :=
  (Matrix.trace A + Matrix.trace B) * two_n_inv

/-- The Relative/Chiral Weyl Mode: β = STr(K) / 2n -/
def betaChiral (two_n_inv : R) (A B : SubMat) : R :=
  (Matrix.trace A - Matrix.trace B) * two_n_inv

/-- 
  The Supertraceless Shape Operator K₀ = K - α I - β Γ
  Expressed explicitly in its diagonal sub-blocks.
-/
def K_zero (two_n_inv : R) (A B : SubMat) : BlockMat :=
  blockDiag
    (A - (alphaCommon two_n_inv A B + betaChiral two_n_inv A B) • (1 : SubMat))
    (B - (alphaCommon two_n_inv A B - betaChiral two_n_inv A B) • (1 : SubMat))

/-- Helper scalar relation: (α + β) * n = Tr(A) -/
lemma alpha_add_beta_mul_n (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) (A B : SubMat) :
    (alphaCommon two_n_inv A B + betaChiral two_n_inv A B) * (Fintype.card ι : R) =
      Matrix.trace A := by
  dsimp [alphaCommon, betaChiral]
  have h_sum :
    ((Matrix.trace A + Matrix.trace B) * two_n_inv + (Matrix.trace A - Matrix.trace B) * two_n_inv) =
      (2 * Matrix.trace A) * two_n_inv := by ring
  rw [h_sum]
  calc
    (2 * Matrix.trace A) * two_n_inv * (Fintype.card ι : R)
      = Matrix.trace A * ((2 * (Fintype.card ι : R)) * two_n_inv) := by ring
    _ = Matrix.trace A * 1 := by rw [h_two_n]
    _ = Matrix.trace A := mul_one (Matrix.trace A)

/-- Helper scalar relation: (α - β) * n = Tr(B) -/
lemma alpha_sub_beta_mul_n (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) (A B : SubMat) :
    (alphaCommon two_n_inv A B - betaChiral two_n_inv A B) * (Fintype.card ι : R) =
      Matrix.trace B := by
  dsimp [alphaCommon, betaChiral]
  have h_sub :
    ((Matrix.trace A + Matrix.trace B) * two_n_inv - (Matrix.trace A - Matrix.trace B) * two_n_inv) =
      (2 * Matrix.trace B) * two_n_inv := by ring
  rw [h_sub]
  calc
    (2 * Matrix.trace B) * two_n_inv * (Fintype.card ι : R)
      = Matrix.trace B * ((2 * (Fintype.card ι : R)) * two_n_inv) := by ring
    _ = Matrix.trace B * 1 := by rw [h_two_n]
    _ = Matrix.trace B := mul_one (Matrix.trace B)

/-! ### The Capstone Trifold Theorems -/

/-- 
  THEOREM 1: The Residual Operator K₀ is strictly Trace-Free.
  Tr(K₀) = 0
-/
theorem trace_K_zero (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) (A B : SubMat) :
    Matrix.trace (K_zero two_n_inv A B) = 0 := by
  dsimp [K_zero]
  simp only [trace_blockDiag, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  rw [alpha_add_beta_mul_n two_n_inv h_two_n A B]
  rw [alpha_sub_beta_mul_n two_n_inv h_two_n A B]
  ring

/-- 
  THEOREM 2: The Residual Operator K₀ is strictly Supertrace-Free.
  STr(K₀) = 0
-/
theorem superTrace_K_zero (two_n_inv : R) (h_two_n : (2 * (Fintype.card ι : R)) * two_n_inv = 1) (A B : SubMat) :
    superTrace (K_zero two_n_inv A B) = 0 := by
  dsimp [K_zero]
  simp only [superTrace_blockDiag, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  rw [alpha_add_beta_mul_n two_n_inv h_two_n A B]
  rw [alpha_sub_beta_mul_n two_n_inv h_two_n A B]
  ring

/--
  THEOREM 3: Exact Reconstruction of the Surprisal Operator:
  K = α • I + β • Γ + K₀
-/
theorem trifold_reconstruction (two_n_inv : R) (A B : SubMat) :
    blockDiag A B =
      (alphaCommon two_n_inv A B) • (identityDoubled : BlockMat) +
      (betaChiral two_n_inv A B) • (Gamma : BlockMat) +
      K_zero two_n_inv A B := by
  dsimp [blockDiag, identityDoubled, Gamma, K_zero]
  ext (i | i) (j | j)
  · simp only [fromBlocks_apply₁₁, add_apply, smul_apply, sub_apply, one_apply, smul_eq_mul]
    ring
  · simp only [fromBlocks_apply₁₂, add_apply, smul_apply, sub_apply, zero_apply, smul_eq_mul]
    ring
  · simp only [fromBlocks_apply₂₁, add_apply, smul_apply, sub_apply, zero_apply, smul_eq_mul]
    ring
  · simp only [fromBlocks_apply₂₂, add_apply, smul_apply, sub_apply, one_apply, neg_apply, smul_eq_mul]
    ring

end TrifoldDecomposition

/-!
=============================================================================
PART 2: Modular Inner Derivations & Logarithmic Radon-Nikodym Derivative
=============================================================================
-/

section ModularDerivations

variable {A : Type*} [Ring A]

/-- The Adjoint Action (Modular Commutator): ad_K(X) = [K, X] = K * X - X * K -/
def adK (K : A) : A →ₗ[ℤ] A where
  toFun X := K * X - X * K
  map_add' X Y := by
    simp only [mul_add, add_mul]
    abel
  map_smul' r X := by
    simp only [smul_sub, mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

@[simp]
theorem adK_apply (K X : A) : adK K X = K * X - X * K := rfl

theorem adK_add (K L X : A) :
    adK (K + L) X = adK K X + adK L X := by
  simp only [adK_apply, add_mul, mul_add]
  abel

theorem adK_neg (K X : A) :
    adK (-K) X = -adK K X := by
  simp only [adK_apply, neg_mul, mul_neg]
  abel

@[simp]
theorem adK_zero : adK (0 : A) = 0 := by
  apply LinearMap.ext
  intro X
  simp [adK_apply]

@[simp]
theorem adK_one_generator : adK (1 : A) = 0 := by
  apply LinearMap.ext
  intro X
  simp [adK_apply]

theorem adK_generator_add (K L : A) :
    adK (K + L) = adK K + adK L := by
  apply LinearMap.ext
  intro X
  exact adK_add K L X

theorem adK_generator_neg (K : A) :
    adK (-K) = -adK K := by
  apply LinearMap.ext
  intro X
  exact adK_neg K X

theorem adK_bracket (K L X : A) :
    adK K (adK L X) - adK L (adK K X) =
      adK (K * L - L * K) X := by
  simp only [adK_apply, mul_sub, sub_mul, mul_assoc]
  noncomm_ring

def linearMapCommutator (F G : A →ₗ[ℤ] A) : A →ₗ[ℤ] A :=
  F.comp G - G.comp F

@[simp]
theorem linearMapCommutator_apply (F G : A →ₗ[ℤ] A) (X : A) :
    linearMapCommutator F G X = F (G X) - G (F X) := rfl

theorem linearMapCommutator_adK (K L : A) :
    linearMapCommutator (adK K) (adK L) = adK (K * L - L * K) := by
  apply LinearMap.ext
  intro X
  exact adK_bracket K L X

/-- 
  THEOREM 4: The Modular Commutator is an exact Derivation:
  ad_K(X * Y) = (ad_K X) * Y + X * (ad_K Y)
-/
theorem adK_is_derivation (K : A) (X Y : A) :
    adK K (X * Y) = (adK K X) * Y + X * (adK K Y) := by
  simp only [adK_apply]
  calc
    K * (X * Y) - (X * Y) * K
      = (K * X * Y - X * K * Y) + (X * K * Y - X * Y * K) := by
        simp only [mul_assoc]
        abel
    _ = (K * X - X * K) * Y + X * (K * Y - Y * K) := by
        simp only [sub_mul, mul_sub, mul_assoc]

@[simp]
theorem adK_one (K : A) : adK K 1 = 0 := by
  simp [adK_apply]

theorem adK_eq_zero_iff_central (K : A) :
    adK K = 0 ↔ ∀ X, K * X = X * K := by
  constructor
  · intro h X
    have hX := congrArg (fun T : A →ₗ[ℤ] A => T X) h
    exact sub_eq_zero.mp (by simpa [adK_apply] using hX)
  · intro h
    apply LinearMap.ext
    intro X
    simp [adK_apply, h X]

/-- The commutator of two inner modular flows vanishes exactly when their
    generator commutator is central. -/
theorem linearMapCommutator_adK_eq_zero_iff_central (K L : A) :
    linearMapCommutator (adK K) (adK L) = 0 ↔
      ∀ X, (K * L - L * K) * X = X * (K * L - L * K) := by
  rw [linearMapCommutator_adK, adK_eq_zero_iff_central]

/-- Leibniz rule for an additive `ℤ`-linear operator on a possibly
    noncommutative ring. -/
def IsRingDerivation (D : A →ₗ[ℤ] A) : Prop :=
  ∀ x y, D (x * y) = D x * y + x * D y

theorem IsRingDerivation.map_one (D : A →ₗ[ℤ] A)
    (hD : IsRingDerivation D) : D 1 = 0 := by
  have h := hD 1 1
  have hone : (1 : A) * 1 = 1 := mul_one 1
  rw [hone, mul_one, one_mul] at h
  have h2 : (D 1 + D 1) - D 1 = D 1 - D 1 := congrArg (fun x => x - D 1) h.symm
  simpa using h2

@[simp] theorem adK_isRingDerivation (K : A) : IsRingDerivation (adK K) := by
  intro X Y
  exact adK_is_derivation K X Y

/-- The left logarithmic Radon--Nikodym derivative in a noncommutative ring. -/
def dlogRNNoncomm (D : A →ₗ[ℤ] A) (Δ inv_Δ : A) : A :=
  inv_Δ * D Δ

/-- The noncommutative cocycle rule.  The displayed commutation hypotheses are
    exactly those needed to move the second inverse through the first
    derivative and the first factor through the second inverse. -/
theorem dlogRNNoncomm_mul (D : A →ₗ[ℤ] A) (hD : IsRingDerivation D)
    (Δ12 inv_Δ12 Δ23 inv_Δ23 : A)
    (h12 : inv_Δ12 * Δ12 = 1)
    (h23 : inv_Δ23 * Δ23 = 1)
    (hD12 : Commute inv_Δ23 (D Δ12))
    (hΔ12 : Commute inv_Δ23 Δ12) :
    dlogRNNoncomm D (Δ12 * Δ23) (inv_Δ12 * inv_Δ23) =
      dlogRNNoncomm D Δ12 inv_Δ12 +
        dlogRNNoncomm D Δ23 inv_Δ23 := by
  dsimp [dlogRNNoncomm]
  rw [hD Δ12 Δ23]
  have hterm1 :
      inv_Δ12 * (inv_Δ23 * (D Δ12 * Δ23)) =
        (inv_Δ12 * D Δ12) * (inv_Δ23 * Δ23) := by
    calc
      inv_Δ12 * (inv_Δ23 * (D Δ12 * Δ23)) =
          inv_Δ12 * ((inv_Δ23 * D Δ12) * Δ23) := by
            simp only [mul_assoc]
      _ = inv_Δ12 * ((D Δ12 * inv_Δ23) * Δ23) := by
            rw [hD12.eq]
      _ = (inv_Δ12 * D Δ12) * (inv_Δ23 * Δ23) := by
            simp only [mul_assoc]
  have hterm2 :
      inv_Δ12 * (inv_Δ23 * (Δ12 * D Δ23)) =
        (inv_Δ12 * Δ12) * (inv_Δ23 * D Δ23) := by
    calc
      inv_Δ12 * (inv_Δ23 * (Δ12 * D Δ23)) =
          inv_Δ12 * ((inv_Δ23 * Δ12) * D Δ23) := by
            simp only [mul_assoc]
      _ = inv_Δ12 * ((Δ12 * inv_Δ23) * D Δ23) := by
            rw [hΔ12.eq]
      _ = (inv_Δ12 * Δ12) * (inv_Δ23 * D Δ23) := by
            simp only [mul_assoc]
  calc
    (inv_Δ12 * inv_Δ23) *
          (D Δ12 * Δ23 + Δ12 * D Δ23) =
        (inv_Δ12 * D Δ12) * (inv_Δ23 * Δ23) +
          (inv_Δ12 * Δ12) * (inv_Δ23 * D Δ23) := by
            simp only [mul_add, mul_assoc]
            rw [hterm1, hterm2]
            simp only [mul_assoc]
    _ = inv_Δ12 * D Δ12 + inv_Δ23 * D Δ23 := by
          rw [h23, h12]
          simp

theorem dlogRNNoncomm_mul_adK (K : A)
    (Δ12 inv_Δ12 Δ23 inv_Δ23 : A)
    (h12 : inv_Δ12 * Δ12 = 1)
    (h23 : inv_Δ23 * Δ23 = 1)
    (hK12 : Commute inv_Δ23 (adK K Δ12))
    (hΔ12 : Commute inv_Δ23 Δ12) :
    dlogRNNoncomm (adK K) (Δ12 * Δ23) (inv_Δ12 * inv_Δ23) =
      dlogRNNoncomm (adK K) Δ12 inv_Δ12 +
        dlogRNNoncomm (adK K) Δ23 inv_Δ23 := by
  exact dlogRNNoncomm_mul (adK K) (adK_isRingDerivation K)
    Δ12 inv_Δ12 Δ23 inv_Δ23 h12 h23 hK12 hΔ12

theorem dlogRNNoncomm_inv (D : A →ₗ[ℤ] A) (hD : IsRingDerivation D)
    (Δ inv_Δ : A) (hInv : Δ * inv_Δ = 1)
    (hComm : Commute (D Δ) inv_Δ) :
    dlogRNNoncomm D inv_Δ Δ = -dlogRNNoncomm D Δ inv_Δ := by
  have hzero : D Δ * inv_Δ + Δ * D inv_Δ = 0 := by
    have h := hD Δ inv_Δ
    rw [hInv, IsRingDerivation.map_one D hD] at h
    exact h.symm
  have hsolve : Δ * D inv_Δ = -(D Δ * inv_Δ) := by
    have h_add : Δ * D inv_Δ + D Δ * inv_Δ = 0 := by
      rw [add_comm, hzero]
    exact eq_neg_of_add_eq_zero_left h_add
  dsimp [dlogRNNoncomm]
  calc
    Δ * D inv_Δ = -(D Δ * inv_Δ) := hsolve
    _ = -(inv_Δ * D Δ) := by rw [hComm.eq]

/-! ### Logarithmic Radon–Nikodym Derivative on Commutative Algebras -/

variable {R : Type*} [CommRing R]

/-- Leibniz rule predicate for an R-linear derivation D -/
def IsLinearDerivation (D : R →ₗ[R] R) : Prop :=
  ∀ x y, D (x * y) = D x * y + x * D y

theorem IsLinearDerivation.map_one (D : R →ₗ[R] R)
    (hD : IsLinearDerivation D) : D 1 = 0 := by
  have h := hD 1 1
  rw [mul_one, one_mul] at h
  linear_combination -h

/-- The Logarithmic Radon–Nikodym Derivation: dlog_D(Δ) = Δ⁻¹ • D(Δ) -/
def dlogRN (D : R →ₗ[R] R) (Δ inv_Δ : R) : R :=
  inv_Δ * D Δ

@[simp] theorem dlogRN_one (D : R →ₗ[R] R)
    (hD : IsLinearDerivation D) :
    dlogRN D 1 1 = 0 := by
  dsimp [dlogRN]
  rw [IsLinearDerivation.map_one D hD, mul_zero]

/--
  THEOREM 5: The Logarithmic Radon–Nikodym Chain Rule (Group Homomorphism):
  dlog_D(Δ₁₂ * Δ₂₃) = dlog_D(Δ₁₂) + dlog_D(Δ₂₃)
-/
theorem dlogRN_mul (D : R →ₗ[R] R) (hD : IsLinearDerivation D)
    (Δ12 inv_Δ12 Δ23 inv_Δ23 : R)
    (h12 : Δ12 * inv_Δ12 = 1)
    (h23 : Δ23 * inv_Δ23 = 1) :
    dlogRN D (Δ12 * Δ23) (inv_Δ12 * inv_Δ23) =
      dlogRN D Δ12 inv_Δ12 + dlogRN D Δ23 inv_Δ23 := by
  dsimp [dlogRN]
  rw [hD Δ12 Δ23]
  have h_expand :
    (inv_Δ12 * inv_Δ23) * (D Δ12 * Δ23 + Δ12 * D Δ23) =
      (inv_Δ12 * D Δ12) * (Δ23 * inv_Δ23) + (inv_Δ23 * D Δ23) * (Δ12 * inv_Δ12) := by
    ring
  rw [h_expand, h12, h23, mul_one, mul_one, add_comm]

/--
  THEOREM 6: Reflection of the Logarithmic Radon–Nikodym Derivative on Inverses:
  dlog_D(Δ⁻¹) = - dlog_D(Δ)
-/
theorem dlogRN_inv (D : R →ₗ[R] R) (hD : IsLinearDerivation D)
    (Δ inv_Δ : R)
    (h : Δ * inv_Δ = 1) :
    dlogRN D inv_Δ Δ = - dlogRN D Δ inv_Δ := by
  have h_one : D 1 = 0 := by
    have hD1 := hD 1 1
    rw [mul_one, one_mul] at hD1
    linear_combination -hD1
  dsimp [dlogRN]
  have h_prod : D (Δ * inv_Δ) = 0 := by rw [h, h_one]
  rw [hD Δ inv_Δ] at h_prod
  have h_shift : Δ * D inv_Δ = - (inv_Δ * D Δ) := by
    calc Δ * D inv_Δ = D Δ * inv_Δ + Δ * D inv_Δ - D Δ * inv_Δ := by ring
    _ = 0 - D Δ * inv_Δ := by rw [h_prod]
    _ = - (inv_Δ * D Δ) := by ring
  exact h_shift

end ModularDerivations

end InfoGeometry.Modular

end noncomputable section
