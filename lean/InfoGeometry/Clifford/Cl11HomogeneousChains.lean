/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11RecursiveUnrolling
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.BigOperators.Fin

/-!
# Native Clifford chains and suffix parity

The chain is formed in the native Clifford quotient through `consNative`.
For homogeneous factors, its matrix image is an ordinary ordered Kronecker
chain after right-multiplying each factor by `K` once for each odd suffix.
The terminal coefficient algebra appears once and is never assumed commutative.

The coefficient-factorization criterion concerns the corrected Clifford word
coordinates. It does not identify pointwise multiplication of coefficient
arrays with Clifford multiplication, or ordinary Kronecker rank with graded
tensor rank. Empty chains and zero terminal coefficients are included.
-/

noncomputable section

open scoped Matrix Matrix.Module TensorProduct BigOperators

namespace InfoGeometry.Clifford.Cl11HomogeneousChains

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedTensorMorita
open InfoGeometry.Clifford.Cl11GradedUnrolling
open InfoGeometry.Clifford.Cl11RecursiveUnrolling

/-- A chain of actual real Clifford atoms, with site zero on the left. -/
def nativeChain : (n : ℕ) → (Fin n → CliffordAlgebra q11) → Clsplit n
  | 0, _ => 1
  | n + 1, a => consNative n (a 0) (nativeChain n (Fin.tail a))

/-- XOR of the specified site parities. -/
def totalParity : (n : ℕ) → (Fin n → Bool) → Bool
  | 0, _ => false
  | n + 1, p => Bool.xor (p 0) (totalParity n (Fin.tail p))

/-- The parity of all strictly later sites, in the chain's actual order. -/
def suffixParity : (n : ℕ) → (Fin n → Bool) → Fin n → Bool
  | 0, _ => fun i => Fin.elim0 i
  | n + 1, p =>
      Fin.cons (totalParity n (Fin.tail p)) (suffixParity n (Fin.tail p))

@[simp] theorem nativeChain_zero (a : Fin 0 → CliffordAlgebra q11) :
    nativeChain 0 a = 1 := rfl

theorem consNative_add_head (n : ℕ) (a b : CliffordAlgebra q11) (x : Clsplit n) :
    consNative n (a + b) x = consNative n a x + consNative n b x := by
  simp only [consNative_apply, GradedTensorProduct.tmul, TensorProduct.add_tmul, map_add]

theorem consNative_smul_head (n : ℕ) (r : ℝ) (a : CliffordAlgebra q11)
    (x : Clsplit n) :
    consNative n (r • a) x = r • consNative n a x := by
  simp only [consNative_apply, GradedTensorProduct.tmul, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, map_smul]

@[simp] theorem consNative_neg_head (n : ℕ) (a : CliffordAlgebra q11)
    (x : Clsplit n) :
    consNative n (-a) x = -consNative n a x := by
  simp only [consNative_apply, GradedTensorProduct.tmul, TensorProduct.neg_tmul, map_neg]

@[simp] theorem consNative_zero_head (n : ℕ) (x : Clsplit n) :
    consNative n (0 : CliffordAlgebra q11) x = 0 := by
  simp [consNative_apply, GradedTensorProduct.tmul]

@[simp] theorem nativeChain_zero_head (n : ℕ) (a : Fin n → CliffordAlgebra q11) :
    nativeChain (n + 1) (Fin.cons 0 a) = 0 := by
  simp [nativeChain]

theorem nativeParity_consNative (n : ℕ) (a : CliffordAlgebra q11) (x : Clsplit n) :
    nativeParity (n + 1) (consNative n a x) =
      consNative n (CliffordAlgebra.involute a) (nativeParity n x) := by
  apply (headTensorEquiv n).injective
  rw [headTensorEquiv_involute]
  simp only [consNative_apply, AlgEquiv.apply_symm_apply, tensorParity_tmul]

/-- Homogeneity is checked against the actual native Clifford involution. -/
theorem nativeChain_homogeneous (n : ℕ) (a : Fin n → CliffordAlgebra q11)
    (p : Fin n → Bool)
    (h : ∀ i, CliffordAlgebra.involute (a i) = if p i then -(a i) else a i) :
    nativeParity n (nativeChain n a) =
      if totalParity n p then -nativeChain n a else nativeChain n a := by
  induction n generalizing a p with
  | zero => simp [nativeChain, totalParity]
  | succ n ih =>
      have ht := ih (Fin.tail a) (Fin.tail p) (fun i => h i.succ)
      rw [nativeChain, nativeParity_consNative, h 0, ht]
      cases hp : p 0 <;> cases hs : totalParity n (Fin.tail p) <;>
        simp [nativeChain, totalParity, hp, hs]

/-- Ordinary Kronecker prepend with the head bit first. -/
def prependMatrix (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ) (T : RealMatrix n) :
    RealMatrix (n + 1) :=
  flatten ℝ n (fun i j => A i j • T)

@[simp] theorem prependMatrix_apply (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (T : RealMatrix n) (i j : Bits (n + 1)) :
    prependMatrix n A T i j = A (i 0) (j 0) * T (Fin.tail i) (Fin.tail j) := rfl

/-- This prepend is exactly Mathlib's ordinary Kronecker product, reindexed. -/
theorem prependMatrix_eq_kronecker (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ)
    (T : RealMatrix n) :
    prependMatrix n A T =
      Matrix.reindexAlgEquiv ℝ ℝ (Fin.consEquiv fun _ : Fin (n + 1) => Fin 2)
        (Matrix.kronecker A T) := by
  ext i j
  rfl

/-- Ordered ordinary Kronecker synthesis, including its scalar empty stage. -/
def ordinaryChain : (n : ℕ) →
    (Fin n → Matrix (Fin 2) (Fin 2) ℝ) → RealMatrix n
  | 0, _ => 1
  | n + 1, a => prependMatrix n (a 0) (ordinaryChain n (Fin.tail a))

theorem ordinaryChain_apply (n : ℕ) (a : Fin n → Matrix (Fin 2) (Fin 2) ℝ)
    (i j : Bits n) :
    ordinaryChain n a i j = ∏ k, a k (i k) (j k) := by
  induction n generalizing a i j with
  | zero => simp [ordinaryChain, Subsingleton.elim i j]
  | succ n ih =>
      rw [ordinaryChain, prependMatrix_apply, ih, Fin.prod_univ_succ]
      rfl

@[simp] theorem atomMatrix_K : cl11EquivMat J1_cl = J1 := by
  simp [J1_cl, map_mul, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg,
    Eplus_mul_Eminus]

/-- An odd tail right-multiplies the head by `K`; the order is part of the claim. -/
theorem nativeStepEquiv_consNative_homogeneous (n : ℕ) (a : CliffordAlgebra q11)
    (x : Clsplit n) (p : Bool)
    (hx : nativeParity n x = if p then -x else x) :
    nativeStepEquiv n (consNative n a x) =
      fun i j => cl11EquivMat (a * J1_cl ^ p.toNat) i j • x := by
  rw [nativeStepEquiv_consNative, tensorMatrixEquivOriginal_tmul_entries]
  cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [evenPart, oddPart, hx, map_mul, Matrix.mul_apply,
      Fin.sum_univ_two, J1] <;> module

theorem leftMatrixEquiv_consNative_homogeneous (n : ℕ) (a : CliffordAlgebra q11)
    (x : Clsplit n) (p : Bool)
    (hx : nativeParity n x = if p then -x else x) :
    leftMatrixEquiv (n + 1) (consNative n a x) =
      prependMatrix n (cl11EquivMat (a * J1_cl ^ p.toNat)) (leftMatrixEquiv n x) := by
  rw [leftMatrixEquiv_succ, nativeStepEquiv_consNative_homogeneous n a x p hx]
  apply congrArg (flatten ℝ n)
  funext i j
  exact map_smul (leftMatrixEquiv n) _ _

/-- The all-stage suffix-parity formula for native homogeneous Clifford chains.
No nonzero hypothesis is required, so zero homogeneous factors are included. -/
theorem nativeChain_matrix_suffixParity (n : ℕ) (a : Fin n → CliffordAlgebra q11)
    (p : Fin n → Bool)
    (h : ∀ i, CliffordAlgebra.involute (a i) = if p i then -(a i) else a i) :
    leftMatrixEquiv n (nativeChain n a) =
      ordinaryChain n
        (fun i => cl11EquivMat (a i * J1_cl ^ (suffixParity n p i).toNat)) := by
  induction n generalizing a p with
  | zero => simp [nativeChain, ordinaryChain]
  | succ n ih =>
      calc
        leftMatrixEquiv (n + 1) (nativeChain (n + 1) a) =
            prependMatrix n
              (cl11EquivMat (a 0 * J1_cl ^ (totalParity n (Fin.tail p)).toNat))
              (leftMatrixEquiv n (nativeChain n (Fin.tail a))) :=
          leftMatrixEquiv_consNative_homogeneous n (a 0)
            (nativeChain n (Fin.tail a)) (totalParity n (Fin.tail p))
            (nativeChain_homogeneous n (Fin.tail a) (Fin.tail p) (fun i => h i.succ))
        _ = _ := by
          rw [ih (Fin.tail a) (Fin.tail p) (fun i => h i.succ)]
          rfl

theorem nativeChain_matrix_entry (n : ℕ) (a : Fin n → CliffordAlgebra q11)
    (p : Fin n → Bool)
    (h : ∀ i, CliffordAlgebra.involute (a i) = if p i then -(a i) else a i)
    (i j : Bits n) :
    leftMatrixEquiv n (nativeChain n a) i j =
      ∏ k, cl11EquivMat (a k * J1_cl ^ (suffixParity n p k).toNat) (i k) (j k) := by
  rw [nativeChain_matrix_suffixParity n a p h, ordinaryChain_apply]

/-! ## Closed-form inverse on homogeneous ordinary chains -/

/-- The correcting volume is even under the native Clifford involution. -/
@[simp] theorem atomInvolute_K : CliffordAlgebra.involute J1_cl = J1_cl := by
  simp [J1_cl, map_mul, CliffordAlgebra.involute_ι]

/-- The same right correction undoes itself; no factors are reordered. -/
@[simp] theorem atom_right_K_twice (a : CliffordAlgebra q11) (p : Bool) :
    (a * J1_cl ^ p.toNat) * J1_cl ^ p.toNat = a := by
  cases p <;> simp [mul_assoc, InfoGeometry.Clifford.Cl11GradedMorita.J1_cl_sq]

/-- Multiplication by the even volume preserves the atom's specified parity. -/
theorem atom_right_K_homogeneous (a : CliffordAlgebra q11) (p s : Bool)
    (h : CliffordAlgebra.involute a = if p then -a else a) :
    CliffordAlgebra.involute (a * J1_cl ^ s.toNat) =
      if p then -(a * J1_cl ^ s.toNat) else a * J1_cl ^ s.toNat := by
  rw [map_mul, map_pow, atomInvolute_K, h]
  cases p <;> simp

/-- The closed-form homogeneous inverse has the same suffix correction as
the forward readback. This is proved through the actual Clifford algebra
equivalence, and includes the empty chain and zero homogeneous atoms. -/
theorem unrollNative_ordinaryChain_suffixParity (n : ℕ)
    (a : Fin n → CliffordAlgebra q11) (p : Fin n → Bool)
    (h : ∀ i, CliffordAlgebra.involute (a i) = if p i then -(a i) else a i) :
    unrollNative n (ordinaryChain n (fun i => cl11EquivMat (a i))) =
      nativeChain n (fun i => a i * J1_cl ^ (suffixParity n p i).toNat) := by
  apply (leftMatrixEquiv n).injective
  rw [reconstruct_unrollNative,
    nativeChain_matrix_suffixParity n
      (fun i => a i * J1_cl ^ (suffixParity n p i).toNat) p
      (fun i => atom_right_K_homogeneous (a i) (p i) (suffixParity n p i) (h i))]
  simp only [atom_right_K_twice]

/-! ## Exact simple-chain criterion in corrected Clifford word coordinates -/

/-- Real coordinates of one actual Clifford atom, in order `(1, η, K, Ω)`. -/
def atomCoordinates : CliffordAlgebra q11 ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  cl11EquivMat.toLinearEquiv.trans coefficientEquiv

theorem atom_expansion (a : CliffordAlgebra q11) :
    a = atomCoordinates a 0 • (1 : CliffordAlgebra q11) +
      atomCoordinates a 1 • CliffordAlgebra.ι q11 (1, 0) +
      atomCoordinates a 2 • J1_cl +
      atomCoordinates a 3 • CliffordAlgebra.ι q11 (0, 1) := by
  apply cl11EquivMat.injective
  simp only [map_add, map_smul, map_one, cl11EquivMat_iota_pos,
    cl11EquivMat_iota_neg, atomMatrix_K]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atomCoordinates, coefficientEquiv, coefficients, Eplus, Eminus, J1] <;> ring

theorem consNative_atom_expansion (n : ℕ) (a : CliffordAlgebra q11) (x : Clsplit n) :
    consNative n a x =
      atomCoordinates a 0 • consNative n (1 : CliffordAlgebra q11) x +
      atomCoordinates a 1 • consNative n (CliffordAlgebra.ι q11 (1, 0)) x +
      atomCoordinates a 2 • consNative n J1_cl x +
      atomCoordinates a 3 • consNative n (CliffordAlgebra.ι q11 (0, 1)) x := by
  calc
    consNative n a x = consNative n
        (atomCoordinates a 0 • (1 : CliffordAlgebra q11) +
          atomCoordinates a 1 • CliffordAlgebra.ι q11 (1, 0) +
          atomCoordinates a 2 • J1_cl +
          atomCoordinates a 3 • CliffordAlgebra.ι q11 (0, 1)) x :=
      congrArg (fun y => consNative n y x) (atom_expansion a)
    _ = _ := by simp only [consNative_add_head, consNative_smul_head]

universe u
variable (B : Type u) [Ring B] [Algebra ℝ B]

/-- The same homogeneous readback retains exactly one arbitrary terminal
coefficient, without any commutativity assumption on its algebra. -/
theorem coefficientChain_matrix_suffixParity (n : ℕ)
    (a : Fin n → CliffordAlgebra q11) (p : Fin n → Bool)
    (h : ∀ i, CliffordAlgebra.involute (a i) = if p i then -(a i) else a i) (b : B) :
    leftCoefficientEquiv B n (nativeChain n a ⊗ₜ[ℝ] b) =
      coefficientReadback B n b
        (ordinaryChain n
          (fun i => cl11EquivMat (a i * J1_cl ^ (suffixParity n p i).toNat))) := by
  rw [leftCoefficientEquiv_tmul, nativeChain_matrix_suffixParity n a p h]

/-- Closed-form homogeneous inversion with one unchanged terminal coefficient.
The algebra B may be noncommutative, and the empty stage retains exactly b. -/
theorem unrollCoefficients_ordinaryChain_suffixParity (n : ℕ)
    (a : Fin n → CliffordAlgebra q11) (p : Fin n → Bool)
    (h : ∀ i, CliffordAlgebra.involute (a i) = if p i then -(a i) else a i) (b : B) :
    unrollCoefficients B n
        (coefficientReadback B n b (ordinaryChain n (fun i => cl11EquivMat (a i)))) =
      nativeChain n (fun i => a i * J1_cl ^ (suffixParity n p i).toNat) ⊗ₜ[ℝ] b := by
  apply (leftCoefficientEquiv B n).injective
  rw [reconstruct_unrollCoefficients, leftCoefficientEquiv_tmul,
    ← unrollNative_ordinaryChain_suffixParity n a p h, reconstruct_unrollNative]

/-- A simple coefficient tensor with exactly one terminal `B` leg. -/
def pureCoefficients (n : ℕ) (a : Fin n → CliffordAlgebra q11) (b : B) : Words n → B :=
  fun w => (∏ i, atomCoordinates (a i) (w i)) • b

@[simp] theorem pureCoefficients_zero_stage (a : Fin 0 → CliffordAlgebra q11) (b : B)
    (w : Words 0) : pureCoefficients B 0 a b w = b := by
  simp [pureCoefficients]

@[simp] theorem pureCoefficients_zero_terminal (n : ℕ)
    (a : Fin n → CliffordAlgebra q11) : pureCoefficients B n a 0 = 0 := by
  funext w
  simp [pureCoefficients]

theorem pureCoefficients_cons (n : ℕ) (a : Fin (n + 1) → CliffordAlgebra q11)
    (b : B) (k : Fin 4) :
    (fun w => pureCoefficients B (n + 1) a b (Fin.cons k w)) =
      atomCoordinates (a 0) k • pureCoefficients B n (Fin.tail a) b := by
  funext w
  simp only [pureCoefficients, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Pi.smul_apply, mul_smul]
  rfl

/-- Corrected word synthesis reconstructs an actual native simple chain. -/
theorem wordReconstruct_pureCoefficients (n : ℕ) (a : Fin n → CliffordAlgebra q11)
    (b : B) :
    wordReconstruct B n (pureCoefficients B n a b) = nativeChain n a ⊗ₜ[ℝ] b := by
  induction n generalizing a with
  | zero => simp [wordReconstruct_zero, nativeChain]
  | succ n ih =>
      rw [wordReconstruct_succ]
      simp only [pureCoefficients_cons, map_smul, ih, consTensor_tmul]
      conv_rhs =>
        rw [nativeChain,
          consNative_atom_expansion n (a 0) (nativeChain n (Fin.tail a))]
      simp only [TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.tmul_smul]

/-- A native simple-chain representation is equivalent to outer-product word
coefficients. This applies to every length, including zero, and includes the
zero tensor through its terminal coefficient. -/
theorem wordReconstruct_pure_chain_iff (n : ℕ) (c : Words n → B) :
    (∃ (a : Fin n → CliffordAlgebra q11) (b : B),
      wordReconstruct B n c = nativeChain n a ⊗ₜ[ℝ] b) ↔
    (∃ (v : Fin n → Fin 4 → ℝ) (b : B),
      ∀ w, c w = (∏ i, v i (w i)) • b) := by
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨fun i => atomCoordinates (a i), b, ?_⟩
    have hc : c = pureCoefficients B n a b :=
      (wordReconstruct B n).injective (h.trans (wordReconstruct_pureCoefficients B n a b).symm)
    intro w
    exact congrFun hc w
  · rintro ⟨v, b, h⟩
    let a : Fin n → CliffordAlgebra q11 := fun i => atomCoordinates.symm (v i)
    refine ⟨a, b, ?_⟩
    have hc : c = pureCoefficients B n a b := by
      funext w
      simpa [pureCoefficients, a] using h w
    rw [hc, wordReconstruct_pureCoefficients]

/-- The same exact criterion, starting from the input matrix and its canonical
graded unrolling rather than from a separately supplied coefficient tensor. -/
theorem unrollCoefficients_pure_chain_iff (n : ℕ) (M : CoefficientMatrix B n) :
    (∃ (a : Fin n → CliffordAlgebra q11) (b : B),
      unrollCoefficients B n M = nativeChain n a ⊗ₜ[ℝ] b) ↔
    (∃ (v : Fin n → Fin 4 → ℝ) (b : B),
      ∀ w, wordCoefficientEquiv B n M w = (∏ i, v i (w i)) • b) := by
  rw [← wordReconstruct_coefficients B n M]
  exact wordReconstruct_pure_chain_iff B n (wordCoefficientEquiv B n M)

end InfoGeometry.Clifford.Cl11HomogeneousChains
