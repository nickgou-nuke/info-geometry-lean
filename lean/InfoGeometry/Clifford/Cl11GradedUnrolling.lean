/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11GradedTensorMorita
import InfoGeometry.Algebra.MatrixNoncommutativity
import Mathlib.Tactic.Module

/-!
# Explicit graded unrolling in the original split-Clifford basis

The ordered basis is `(1, η, K, Ω)`, with `η = ι (1,0)`, `Ω = ι (0,1)`
and `K = η * Ω`. Thus `η, Ω` are odd and `1, K` are even. We undo the
existing owner's Walsh change of basis and expose its four-block inverse.

All coefficients live in one arbitrary real algebra. Coefficient arrays carry
a linear structure here; their pointwise product is not the Clifford product.
Multiplicativity belongs to the native graded tensor algebra equivalence.
-/

noncomputable section

open scoped Matrix Matrix.Module TensorProduct

namespace InfoGeometry.Clifford.Cl11GradedUnrolling

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Clifford.Cl11GradedTensorMorita
open InfoGeometry.OperatorAlgebra.PeirceHadamardNative

universe u
variable {A : Type u} [Ring A] [Algebra ℝ A]

@[instance_reducible]
private def invertibleTwo : Invertible (2 : A) where
  invOf := algebraMap ℝ A (1 / 2)
  invOf_mul_self := by
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (algebraMap ℝ A) (show (1 / 2 : ℝ) * 2 = 1 by norm_num)
  mul_invOf_self := by
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (algebraMap ℝ A) (show (2 : ℝ) * (1 / 2) = 1 by norm_num)

attribute [local instance] invertibleTwo

private theorem mul_invOf_two (a : A) :
    a * ⅟ (2 : A) = (1 / 2 : ℝ) • a := by
  change a * algebraMap ℝ A (1 / 2) = _
  rw [← Algebra.commutes]
  exact (Algebra.smul_def _ _).symm

/-- The existing Walsh unit acts on full operator-valued matrices. -/
def coefficientWalsh : Matrix (Fin 2) (Fin 2) A ≃ₐ[ℝ]
    Matrix (Fin 2) (Fin 2) A where
  toFun M := (walshUnit : (Matrix (Fin 2) (Fin 2) A)ˣ).val * M * (walshUnit⁻¹).val
  invFun M := (walshUnit⁻¹ : (Matrix (Fin 2) (Fin 2) A)ˣ).val * M * walshUnit.val
  left_inv M := by simp [mul_assoc]
  right_inv M := by simp [mul_assoc]
  map_mul' M N := by simp [mul_assoc]
  map_add' M N := by simp [mul_add, add_mul]
  commutes' r := by
    rw [← Algebra.commutes r (walshUnit : (Matrix (Fin 2) (Fin 2) A)ˣ).val,
      mul_assoc]
    simp

theorem coefficientWalsh_apply (M : Matrix (Fin 2) (Fin 2) A) :
    coefficientWalsh M =
      !![(1 / 2 : ℝ) • ((M 0 0 + M 0 1) + (M 1 0 + M 1 1)),
         (1 / 2 : ℝ) • ((M 0 0 - M 0 1) + (M 1 0 - M 1 1));
         (1 / 2 : ℝ) • ((M 0 0 + M 0 1) - (M 1 0 + M 1 1)),
         (1 / 2 : ℝ) • ((M 0 0 - M 0 1) - (M 1 0 - M 1 1))] := by
  change (walshUnit : (Matrix (Fin 2) (Fin 2) A)ˣ).val * M * (walshUnit⁻¹).val = _
  rw [walshUnit_similarity]
  simp only [mul_invOf_two]

theorem coefficientWalsh_involutive : Function.Involutive (coefficientWalsh (A := A)) := by
  intro M
  rw [coefficientWalsh_apply, coefficientWalsh_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> module

/-- Ordinary four coefficients, in the order `(1, η, K, Ω)`. -/
def coefficients (M : Matrix (Fin 2) (Fin 2) A) : Fin 4 → A :=
  ![(1 / 2 : ℝ) • (M 0 0 + M 1 1),
    (1 / 2 : ℝ) • (M 0 0 - M 1 1),
    (1 / 2 : ℝ) • (M 0 1 + M 1 0),
    (1 / 2 : ℝ) • (M 0 1 - M 1 0)]

/-- Reconstruct the four matrix entries before applying a parity correction. -/
def synthesize (c : Fin 4 → A) : Matrix (Fin 2) (Fin 2) A :=
  !![c 0 + c 1, c 2 + c 3; c 2 - c 3, c 0 - c 1]

@[simp] theorem synthesize_coefficients (M : Matrix (Fin 2) (Fin 2) A) :
    synthesize (coefficients M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [synthesize, coefficients] <;> module

@[simp] theorem coefficients_synthesize (c : Fin 4 → A) :
    coefficients (synthesize c) = c := by
  funext i
  fin_cases i <;> simp [synthesize, coefficients] <;> module

/-- A linear coordinate equivalence; no pointwise algebra structure is asserted. -/
def coefficientEquiv : Matrix (Fin 2) (Fin 2) A ≃ₗ[ℝ] (Fin 4 → A) where
  toFun := coefficients
  invFun := synthesize
  left_inv := synthesize_coefficients
  right_inv := coefficients_synthesize
  map_add' M N := by ext i; fin_cases i <;> simp [coefficients] <;> module
  map_smul' r M := by ext i; fin_cases i <;> simp [coefficients] <;> module

variable (θ : A ≃ₐ[ℝ] A)

def evenPart (a : A) : A := (1 / 2 : ℝ) • (a + θ a)

def oddPart (a : A) : A := (1 / 2 : ℝ) • (a - θ a)

theorem evenPart_add_oddPart (a : A) : evenPart θ a + oddPart θ a = a := by
  dsimp [evenPart, oddPart]
  module

/-- Only the odd parts exchange labels: `1 ↔ K` and `η ↔ Ω`. -/
def correction (c : Fin 4 → A) : Fin 4 → A :=
  ![evenPart θ (c 0) + oddPart θ (c 2),
    evenPart θ (c 1) + oddPart θ (c 3),
    evenPart θ (c 2) + oddPart θ (c 0),
    evenPart θ (c 3) + oddPart θ (c 1)]

theorem correction_involutive (hθ : Function.Involutive θ) :
    Function.Involutive (correction θ) := by
  have hpair (a b : A) :
      evenPart θ (evenPart θ a + oddPart θ b) +
        oddPart θ (evenPart θ b + oddPart θ a) = a := by
    dsimp only [evenPart, oddPart]
    simp only [map_smul, map_add, map_sub, hθ a, hθ b]
    module
  intro c
  funext i
  fin_cases i
  · exact hpair (c 0) (c 2)
  · exact hpair (c 1) (c 3)
  · exact hpair (c 2) (c 0)
  · exact hpair (c 3) (c 1)

def correctionEquiv (hθ : Function.Involutive θ) : (Fin 4 → A) ≃ₗ[ℝ] (Fin 4 → A) where
  toFun := correction θ
  invFun := correction θ
  left_inv := correction_involutive θ hθ
  right_inv := correction_involutive θ hθ
  map_add' c d := by
    ext i
    fin_cases i <;> simp [correction, evenPart, oddPart] <;> module
  map_smul' r c := by
    ext i
    fin_cases i <;> simp [correction, evenPart, oddPart, map_smul] <;> module

/-- The four corrected blocks from the intake, as an invertible coordinate map. -/
def gradedCoefficientEquiv (hθ : Function.Involutive θ) :
    Matrix (Fin 2) (Fin 2) A ≃ₗ[ℝ] (Fin 4 → A) :=
  coefficientEquiv.trans (correctionEquiv θ hθ)

variable (𝒜 : ZMod 2 → Submodule ℝ A) [GradedAlgebra 𝒜]
variable (hEven : ∀ {a : A}, a ∈ 𝒜 0 → θ a = a)
variable (hOdd : ∀ {a : A}, a ∈ 𝒜 1 → θ a = -a)

/-- The native graded algebra equivalence, in the original `η, Ω, K` basis. -/
def tensorMatrixEquivOriginal :
    (CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) A :=
  (tensorMatrixEquiv 𝒜 θ hEven hOdd).trans coefficientWalsh

/-- Expand coefficients in the actual graded tensor carrier. -/
def tensorExpansion (c : Fin 4 → A) : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜 :=
  ((1 : CliffordAlgebra q11) ᵍ⊗ₜ c 0) +
    (CliffordAlgebra.ι q11 (1, 0) ᵍ⊗ₜ c 1) +
    (J1_cl ᵍ⊗ₜ c 2) +
    (CliffordAlgebra.ι q11 (0, 1) ᵍ⊗ₜ c 3)

theorem tensorMatrixEquivOriginal_one (a : A) :
    tensorMatrixEquivOriginal θ 𝒜 hEven hOdd ((1 : CliffordAlgebra q11) ᵍ⊗ₜ a) =
      !![evenPart θ a, oddPart θ a; oddPart θ a, evenPart θ a] := by
  change coefficientWalsh (tensorToMatrix 𝒜 θ hEven hOdd (1 ᵍ⊗ₜ a)) = _
  rw [tensorToMatrix_tmul_matrix, map_one, coefficientWalsh_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenPart, oddPart]
  module

theorem tensorMatrixEquivOriginal_eta (a : A) :
    tensorMatrixEquivOriginal θ 𝒜 hEven hOdd
      (CliffordAlgebra.ι q11 (1, 0) ᵍ⊗ₜ a) =
      !![evenPart θ a, oddPart θ a; -oddPart θ a, -evenPart θ a] := by
  change coefficientWalsh (tensorToMatrix 𝒜 θ hEven hOdd (_ ᵍ⊗ₜ a)) = _
  rw [tensorToMatrix_tmul_matrix, cl11StandardEquiv_iota_pos, coefficientWalsh_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenPart, oddPart, J1] <;> module

theorem tensorMatrixEquivOriginal_K (a : A) :
    tensorMatrixEquivOriginal θ 𝒜 hEven hOdd (J1_cl ᵍ⊗ₜ a) =
      !![oddPart θ a, evenPart θ a; evenPart θ a, oddPart θ a] := by
  change coefficientWalsh (tensorToMatrix 𝒜 θ hEven hOdd (_ ᵍ⊗ₜ a)) = _
  rw [tensorToMatrix_tmul_matrix, cl11StandardEquiv_J1_cl, coefficientWalsh_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenPart, oddPart, Eplus]
  module

theorem tensorMatrixEquivOriginal_omega (a : A) :
    tensorMatrixEquivOriginal θ 𝒜 hEven hOdd
      (CliffordAlgebra.ι q11 (0, 1) ᵍ⊗ₜ a) =
      !![oddPart θ a, evenPart θ a; -evenPart θ a, -oddPart θ a] := by
  change coefficientWalsh (tensorToMatrix 𝒜 θ hEven hOdd (_ ᵍ⊗ₜ a)) = _
  rw [tensorToMatrix_tmul_matrix, cl11StandardEquiv_iota_neg, coefficientWalsh_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenPart, oddPart, Eminus] <;> module

/-- The entire left Clifford factor has its original, unstandardized matrix
representation. This is proved by the native Clifford universal property. -/
theorem tensorMatrixEquivOriginal_left (x : CliffordAlgebra q11) :
    tensorMatrixEquivOriginal θ 𝒜 hEven hOdd (x ᵍ⊗ₜ (1 : A)) =
      (cl11EquivMat x).map (algebraMap ℝ A) := by
  have h :
      (tensorMatrixEquivOriginal θ 𝒜 hEven hOdd).toAlgHom.comp
          (GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd q11) 𝒜) =
        (Algebra.ofId ℝ A).mapMatrix.comp cl11EquivMat.toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by ext <;> simp
    have hι : CliffordAlgebra.ι q11 v =
        v.1 • CliffordAlgebra.ι q11 (1, 0) +
          v.2 • CliffordAlgebra.ι q11 (0, 1) := by
      rw [← map_smul, ← map_smul, ← map_add, ← hv]
    change tensorMatrixEquivOriginal θ 𝒜 hEven hOdd
        (GradedTensorProduct.includeLeft (CliffordAlgebra.evenOdd q11) 𝒜
          (CliffordAlgebra.ι q11 v)) =
      (Algebra.ofId ℝ A).mapMatrix (cl11EquivMat (CliffordAlgebra.ι q11 v))
    rw [hι]
    simp only [map_add, map_smul, GradedTensorProduct.includeLeft_apply,
      tensorMatrixEquivOriginal_eta, tensorMatrixEquivOriginal_omega,
      cl11EquivMat_iota_pos, cl11EquivMat_iota_neg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [evenPart, oddPart, Eplus, Eminus, Algebra.algebraMap_eq_smul_one] <;> module
  exact AlgHom.congr_fun h x

/-- The generic simple-tensor formula retains the order of multiplication.
The displayed tail matrix is `I * a_even + K * a_odd`. -/
theorem tensorMatrixEquivOriginal_tmul (x : CliffordAlgebra q11) (a : A) :
    tensorMatrixEquivOriginal θ 𝒜 hEven hOdd (x ᵍ⊗ₜ a) =
      (cl11EquivMat x).map (algebraMap ℝ A) *
        !![evenPart θ a, oddPart θ a; oddPart θ a, evenPart θ a] := by
  rw [← GradedTensorProduct.tmul_one_mul_one_tmul, map_mul,
    tensorMatrixEquivOriginal_left, tensorMatrixEquivOriginal_one]

/-- Entry form of the simple-tensor readback, with central real scalar action
and no commutation of tail coefficients. -/
theorem tensorMatrixEquivOriginal_tmul_entries (x : CliffordAlgebra q11) (a : A) :
    tensorMatrixEquivOriginal θ 𝒜 hEven hOdd (x ᵍ⊗ₜ a) =
      !![cl11EquivMat x 0 0 • evenPart θ a + cl11EquivMat x 0 1 • oddPart θ a,
         cl11EquivMat x 0 0 • oddPart θ a + cl11EquivMat x 0 1 • evenPart θ a;
         cl11EquivMat x 1 0 • evenPart θ a + cl11EquivMat x 1 1 • oddPart θ a,
         cl11EquivMat x 1 0 • oddPart θ a + cl11EquivMat x 1 1 • evenPart θ a] := by
  rw [tensorMatrixEquivOriginal_tmul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def]

private theorem coefficientWalsh_grade (M : Matrix (Fin 2) (Fin 2) A) :
    coefficientWalsh
        (InfoGeometry.OperatorAlgebra.GradedMatrixMorita.matrixGrade θ.toRingEquiv M) =
      !![θ (coefficientWalsh M 1 1), θ (coefficientWalsh M 1 0);
         θ (coefficientWalsh M 0 1), θ (coefficientWalsh M 0 0)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coefficientWalsh_apply,
      InfoGeometry.OperatorAlgebra.GradedMatrixMorita.matrixGrade_apply,
      map_smul] <;> module

/-- Factorwise canonical parity becomes coefficient parity combined with
row-and-column swap, on every native graded tensor element. -/
theorem tensorMatrixEquivOriginal_parity
    (z : CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] 𝒜) :
    tensorMatrixEquivOriginal θ 𝒜 hEven hOdd (tensorParity 𝒜 θ hEven hOdd z) =
      !![θ (tensorMatrixEquivOriginal θ 𝒜 hEven hOdd z 1 1),
         θ (tensorMatrixEquivOriginal θ 𝒜 hEven hOdd z 1 0);
         θ (tensorMatrixEquivOriginal θ 𝒜 hEven hOdd z 0 1),
         θ (tensorMatrixEquivOriginal θ 𝒜 hEven hOdd z 0 0)] := by
  change coefficientWalsh
      (tensorToMatrix 𝒜 θ hEven hOdd (tensorParityLinear 𝒜 θ z)) = _
  rw [tensorParity_compatible, coefficientWalsh_grade]
  rfl

/-- Native graded reconstruction implements exactly the four parity exchanges. -/
theorem tensorExpansion_readback (c : Fin 4 → A) :
    tensorMatrixEquivOriginal θ 𝒜 hEven hOdd (tensorExpansion 𝒜 c) =
      synthesize (correction θ c) := by
  simp only [tensorExpansion, map_add, tensorMatrixEquivOriginal_one,
    tensorMatrixEquivOriginal_eta, tensorMatrixEquivOriginal_K,
    tensorMatrixEquivOriginal_omega]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [synthesize, correction] <;> abel

/-- The explicit inverse applies the correction to the ordinary four blocks. -/
theorem tensorMatrixEquivOriginal_symm_apply (M : Matrix (Fin 2) (Fin 2) A) :
    (tensorMatrixEquivOriginal θ 𝒜 hEven hOdd).symm M =
      tensorExpansion 𝒜 (correction θ (coefficients M)) := by
  apply (tensorMatrixEquivOriginal θ 𝒜 hEven hOdd).injective
  rw [AlgEquiv.apply_symm_apply, tensorExpansion_readback,
    correction_involutive θ (coefficientParity_involutive 𝒜 θ hEven hOdd),
    synthesize_coefficients]

include hEven hOdd in
/-- The explicit inverse retains multiplication in the native graded algebra. -/
theorem explicitUnroll_mul (M N : Matrix (Fin 2) (Fin 2) A) :
    tensorExpansion 𝒜 (correction θ (coefficients (M * N))) =
      tensorExpansion 𝒜 (correction θ (coefficients M)) *
        tensorExpansion 𝒜 (correction θ (coefficients N)) := by
  simp only [← tensorMatrixEquivOriginal_symm_apply θ 𝒜 hEven hOdd, map_mul]

end InfoGeometry.Clifford.Cl11GradedUnrolling
