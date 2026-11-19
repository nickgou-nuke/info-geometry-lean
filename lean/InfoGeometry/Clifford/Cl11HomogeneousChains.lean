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
noncomputable def nativeChain : (n : ℕ) → (Fin n → CliffordAlgebra q11) → Clsplit n
  | 0, _ => 1
  | n + 1, a => consNative n (a 0) (nativeChain n (Fin.tail a))

/-- XOR of the specified site parities. -/
def totalParity : (n : ℕ) → (Fin n → Bool) → Bool :=
  Nat.rec (motive := fun n => (Fin n → Bool) → Bool)
    (fun _ => false)
    (fun _ ih p => Bool.xor (p 0) (ih (Fin.tail p)))

/-- The parity of all strictly later sites, in the chain's actual order. -/
def suffixParity : (n : ℕ) → (Fin n → Bool) → Fin n → Bool :=
  Nat.rec (motive := fun n => (Fin n → Bool) → Fin n → Bool)
    (fun _ i => Fin.elim0 i)
    (fun n ih p => Fin.cons (totalParity n (Fin.tail p)) (ih (Fin.tail p)))

@[simp] theorem nativeChain_zero (a : Fin 0 → CliffordAlgebra q11) :
    nativeChain 0 a = 1 := rfl

/-- Fixing the tail leaves the actual native head insertion as a linear map. -/
private def headConsLinear (n : ℕ) (x : Clsplit n) :
    CliffordAlgebra q11 →ₗ[ℝ] Clsplit (n + 1) :=
  (headTensorEquiv n).symm.toLinearMap.comp
    ((GradedTensorProduct.of ℝ (CliffordAlgebra.evenOdd q11)
      (CliffordAlgebra.evenOdd (Qsplit n))).toLinearMap.comp
        ((TensorProduct.mk ℝ (CliffordAlgebra q11) (Clsplit n)).flip x))

theorem consNative_add_head (n : ℕ) (a b : CliffordAlgebra q11) (x : Clsplit n) :
    consNative n (a + b) x = consNative n a x + consNative n b x := by
  exact map_add (headConsLinear n x) a b

theorem consNative_smul_head (n : ℕ) (r : ℝ) (a : CliffordAlgebra q11)
    (x : Clsplit n) :
    consNative n (r • a) x = r • consNative n a x := by
  exact map_smul (headConsLinear n x) r a

@[simp] theorem consNative_neg_head (n : ℕ) (a : CliffordAlgebra q11)
    (x : Clsplit n) :
    consNative n (-a) x = -consNative n a x := by
  exact map_neg (headConsLinear n x) a

@[simp] theorem consNative_zero_head (n : ℕ) (x : Clsplit n) :
    consNative n (0 : CliffordAlgebra q11) x = 0 := by
  exact map_zero (headConsLinear n x)

@[simp] theorem nativeChain_zero_head (n : ℕ) (a : Fin n → CliffordAlgebra q11) :
    nativeChain (n + 1) (Fin.cons 0 a) = 0 := by
  change consNative n (0 : CliffordAlgebra q11) (nativeChain n a) = 0
  exact consNative_zero_head n (nativeChain n a)

theorem nativeParity_consNative (n : ℕ) (a : CliffordAlgebra q11) (x : Clsplit n) :
    nativeParity (n + 1) (consNative n a x) =
      consNative n (CliffordAlgebra.involute a) (nativeParity n x) := by
  change nativeParity (n + 1)
      ((headTensorEquiv n).symm (a ᵍ⊗ₜ x)) =
    (headTensorEquiv n).symm
      (CliffordAlgebra.involute a ᵍ⊗ₜ nativeParity n x)
  apply (headTensorEquiv n).injective
  exact
    (headTensorEquiv_involute n
      ((headTensorEquiv n).symm (a ᵍ⊗ₜ x))).trans
      ((congrArg
        (tensorParity (CliffordAlgebra.evenOdd (Qsplit n)) (nativeParity n)
          (nativeParity_even n) (nativeParity_odd n))
        ((headTensorEquiv n).apply_symm_apply (a ᵍ⊗ₜ x))).trans
        ((tensorParity_tmul (CliffordAlgebra.evenOdd (Qsplit n))
          (nativeParity n) (nativeParity_even n) (nativeParity_odd n)
          a x).trans
          ((headTensorEquiv n).apply_symm_apply
            (CliffordAlgebra.involute a ᵍ⊗ₜ nativeParity n x)).symm))

/-- Homogeneity is checked against the actual native Clifford involution. -/
theorem nativeChain_homogeneous (n : ℕ) (a : Fin n → CliffordAlgebra q11)
    (p : Fin n → Bool)
    (h : ∀ i, CliffordAlgebra.involute (a i) = if p i then -(a i) else a i) :
    nativeParity n (nativeChain n a) =
      if totalParity n p then -nativeChain n a else nativeChain n a := by
  induction n with
  | zero => simp [nativeChain, totalParity]
  | succ n ih =>
      have ht := ih (Fin.tail a) (Fin.tail p) (fun i => h i.succ)
      have hpar : totalParity (n + 1) p =
          Bool.xor (p 0) (totalParity n (Fin.tail p)) := rfl
      rw [nativeChain, nativeParity_consNative, h 0, ht, hpar]
      cases hp : p 0 <;> cases hs : totalParity n (Fin.tail p) <;>
        simp
      · exact consNative_neg_head n (a 0) (nativeChain n (Fin.tail a))
      · exact (congrArg (fun z => -z)
          (consNative_neg_head n (a 0) (nativeChain n (Fin.tail a)))).trans (neg_neg _)

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
noncomputable def ordinaryChain : (n : ℕ) →
    (Fin n → Matrix (Fin 2) (Fin 2) ℝ) → RealMatrix n
  | 0, _ => 1
  | n + 1, a => prependMatrix n (a 0) (ordinaryChain n (Fin.tail a))

theorem ordinaryChain_apply (n : ℕ) (a : Fin n → Matrix (Fin 2) (Fin 2) ℝ)
    (i j : Bits n) :
    ordinaryChain n a i j = ∏ k, a k (i k) (j k) := by
  induction n with
  | zero =>
      have hij : i = j := Subsingleton.elim _ _
      subst j
      change (1 : RealMatrix 0) i i = _
      exact (Matrix.one_apply_eq i).trans (Fin.prod_univ_zero _).symm
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
  induction n with
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
    consNative n a x = headConsLinear n x
        (atomCoordinates a 0 • (1 : CliffordAlgebra q11) +
          atomCoordinates a 1 • CliffordAlgebra.ι q11 (1, 0) +
          atomCoordinates a 2 • J1_cl +
          atomCoordinates a 3 • CliffordAlgebra.ι q11 (0, 1)) :=
      congrArg (headConsLinear n x) (atom_expansion a)
    _ = _ := by simp only [map_add, map_smul]; rfl

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
  induction n with
  | zero =>
      exact (wordReconstruct_zero B (pureCoefficients B 0 a b)).trans
        (congrArg (fun y => (1 : Clsplit 0) ⊗ₜ[ℝ] y)
          (pureCoefficients_zero_stage B a b default))
  | succ n ih =>
      rw [wordReconstruct_succ]
      simp only [pureCoefficients_cons, map_smul, ih]
      rw [consTensor_tmul B n (1 : CliffordAlgebra q11) (nativeChain n (Fin.tail a)) b,
        consTensor_tmul B n (CliffordAlgebra.ι q11 (1, 0))
          (nativeChain n (Fin.tail a)) b,
        consTensor_tmul B n J1_cl (nativeChain n (Fin.tail a)) b,
        consTensor_tmul B n (CliffordAlgebra.ι q11 (0, 1))
          (nativeChain n (Fin.tail a)) b]
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

section SingleSiteChainsAndPrefixParity

/-- Null creation atom `(ι(1,0) + ι(0,1)) / 2` in `Cl(1,1)` (`nullPlus^2 = 0`). -/
noncomputable def nullPlus : CliffordAlgebra q11 :=
  CliffordAlgebra.ι q11 (1 / 2, 1 / 2)

/-- Null annihilation atom `(ι(1,0) - ι(0,1)) / 2` in `Cl(1,1)` (`nullMinus^2 = 0`). -/
noncomputable def nullMinus : CliffordAlgebra q11 :=
  CliffordAlgebra.ι q11 (1 / 2, -1 / 2)

theorem nullPlus_sq : nullPlus * nullPlus = 0 := by
  dsimp [nullPlus]
  rw [CliffordAlgebra.ι_sq_scalar]
  have hq : q11 (1 / 2, 1 / 2) = 0 := by simp [q11_apply]
  rw [hq, map_zero]

theorem nullMinus_sq : nullMinus * nullMinus = 0 := by
  dsimp [nullMinus]
  rw [CliffordAlgebra.ι_sq_scalar]
  have hq : q11 (1 / 2, -1 / 2) = 0 := by simp [q11_apply]; ring
  rw [hq, map_zero]

theorem nullPlus_mul_nullMinus_add :
    nullPlus * nullMinus + nullMinus * nullPlus = 1 := by
  apply cl11EquivMat.injective
  have hp : nullPlus =
      (1 / 2 : ℝ) • CliffordAlgebra.ι q11 (1, 0) +
        (1 / 2 : ℝ) • CliffordAlgebra.ι q11 (0, 1) := by
    dsimp [nullPlus]
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1; ext <;> norm_num
  have hm : nullMinus =
      (1 / 2 : ℝ) • CliffordAlgebra.ι q11 (1, 0) +
        (-1 / 2 : ℝ) • CliffordAlgebra.ι q11 (0, 1) := by
    dsimp [nullMinus]
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1; ext <;> norm_num
  rw [map_add, map_mul, map_mul, map_one, hp, hm]
  simp only [map_add, map_smul, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eplus, Eminus] <;> norm_num

@[simp] theorem involute_nullPlus :
    CliffordAlgebra.involute nullPlus = -nullPlus :=
  CliffordAlgebra.involute_ι _

@[simp] theorem involute_nullMinus :
    CliffordAlgebra.involute nullMinus = -nullMinus :=
  CliffordAlgebra.involute_ι _

/-- Single-site native chain inserting `c : Cl(1,1)` at site `k : Fin n` and `1` elsewhere. -/
noncomputable def singleSiteChain (n : ℕ) (k : Fin n) (c : CliffordAlgebra q11) :
    Clsplit n :=
  nativeChain n (Function.update (fun _ => (1 : CliffordAlgebra q11)) k c)

@[simp] theorem nativeChain_ones (n : ℕ) :
    nativeChain n (fun _ => (1 : CliffordAlgebra q11)) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change consNative n 1 (nativeChain n (fun _ => (1 : CliffordAlgebra q11))) = 1
      rw [ih]
      exact map_one (headTensorEquiv n).symm

theorem singleSiteChain_zero (n : ℕ) (c : CliffordAlgebra q11) :
    singleSiteChain (n + 1) 0 c = consNative n c (1 : Clsplit n) := by
  dsimp [singleSiteChain]
  have htail : Fin.tail (Function.update (fun _ : Fin (n + 1) => (1 : CliffordAlgebra q11)) 0 c) =
      fun _ => (1 : CliffordAlgebra q11) := by
    funext i
    simp [Fin.tail, Function.update]
  change consNative n
      (Function.update (fun _ : Fin (n + 1) => (1 : CliffordAlgebra q11)) 0 c 0)
      (nativeChain n (Fin.tail
        (Function.update (fun _ : Fin (n + 1) => (1 : CliffordAlgebra q11)) 0 c))) = _
  rw [htail, nativeChain_ones, Function.update_self]

theorem singleSiteChain_succ (n : ℕ) (k : Fin n) (c : CliffordAlgebra q11) :
    singleSiteChain (n + 1) k.succ c = consNative n 1 (singleSiteChain n k c) := by
  dsimp [singleSiteChain]
  have h0 : Function.update (fun _ : Fin (n + 1) => (1 : CliffordAlgebra q11)) k.succ c 0 = 1 :=
    Function.update_of_ne (Fin.succ_ne_zero k).symm c (fun _ : Fin (n + 1) => (1 : CliffordAlgebra q11))
  have htail :
      Fin.tail (Function.update (fun _ : Fin (n + 1) => (1 : CliffordAlgebra q11)) k.succ c) =
        Function.update (fun _ : Fin n => (1 : CliffordAlgebra q11)) k c := by
    funext i
    by_cases hi : i = k
    · subst hi; simp [Fin.tail, Function.update]
    · simp [Fin.tail, Function.update, hi]
  change consNative n
      (Function.update (fun _ : Fin (n + 1) => (1 : CliffordAlgebra q11)) k.succ c 0)
      (nativeChain n (Fin.tail
        (Function.update (fun _ : Fin (n + 1) => (1 : CliffordAlgebra q11)) k.succ c))) = _
  rw [h0, htail]

theorem singleSiteChain_homogeneous (n : ℕ) (k : Fin n) (c : CliffordAlgebra q11) (q : Bool)
    (hc : CliffordAlgebra.involute c = if q then -c else c) :
    nativeParity n (singleSiteChain n k c) =
      if q then -singleSiteChain n k c else singleSiteChain n k c := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      refine Fin.cases ?_ (fun k' => ?_) k
      · rw [singleSiteChain_zero, nativeParity_consNative, hc, map_one]
        cases q
        · simp
        · simp only [↓reduceIte]
          exact consNative_neg_head n c 1
      · rw [singleSiteChain_succ, nativeParity_consNative, map_one, ih k']
        cases q
        · simp
        · simp only [↓reduceIte]
          change (headTensorEquiv n).symm ((1 : CliffordAlgebra q11) ᵍ⊗ₜ (-singleSiteChain n k' c)) =
            -((headTensorEquiv n).symm ((1 : CliffordAlgebra q11) ᵍ⊗ₜ singleSiteChain n k' c))
          rw [← map_neg]
          congr 1
          simp [GradedTensorProduct.tmul, TensorProduct.tmul_neg]

private theorem totalParity_update_single_eq (n : ℕ) (k : Fin n) :
    totalParity n (Function.update (fun _ : Fin n => false) k true) = true := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      refine Fin.cases ?_ (fun k' => ?_) k
      · have htail : Fin.tail (Function.update (fun _ : Fin (n + 1) => false) 0 true) =
            fun _ => false := by
          funext i; simp [Fin.tail, Function.update]
        have hfalse : ∀ m, totalParity m (fun _ => false) = false := by
          intro m; induction m with
          | zero => rfl
          | succ m ihm => change Bool.xor false (totalParity m (fun _ => false)) = false; rw [ihm]; rfl
        change Bool.xor (Function.update (fun _ : Fin (n + 1) => false) 0 true 0)
            (totalParity n (Fin.tail (Function.update (fun _ : Fin (n + 1) => false) 0 true))) = true
        rw [htail, hfalse, Function.update_self]
        rfl
      · have h0 : Function.update (fun _ : Fin (n + 1) => false) k'.succ true 0 = false :=
          Function.update_of_ne (Fin.succ_ne_zero k').symm true (fun _ => false)
        have htail : Fin.tail (Function.update (fun _ : Fin (n + 1) => false) k'.succ true) =
            Function.update (fun _ : Fin n => false) k' true := by
          funext i
          by_cases hi : i = k'
          · subst hi; simp [Fin.tail, Function.update]
          · simp [Fin.tail, Function.update, hi]
        change Bool.xor (Function.update (fun _ : Fin (n + 1) => false) k'.succ true 0)
            (totalParity n (Fin.tail (Function.update (fun _ : Fin (n + 1) => false) k'.succ true))) = true
        rw [h0, htail, ih k']
        rfl

private theorem suffixParity_update_single (n : ℕ) (k j : Fin n) :
    suffixParity n (Function.update (fun _ : Fin n => false) k true) j = decide (j < k) := by
  have hfalse_tot : ∀ r, totalParity r (fun _ => false) = false := by
    intro r; induction r with
    | zero => rfl
    | succ r ihr =>
        change Bool.xor false (totalParity r (fun _ => false)) = false
        rw [ihr]; rfl
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      refine Fin.cases ?_ (fun k' => ?_) k <;> refine Fin.cases ?_ (fun j' => ?_) j
      · change totalParity n (Fin.tail (fun _ : Fin (n + 1) => false)) = _
        have ht : Fin.tail (fun _ : Fin (n + 1) => false) = fun _ : Fin n => false := rfl
        rw [ht, hfalse_tot n]
        simp
      · have htail : Fin.tail (Function.update (fun _ : Fin (n + 1) => false) 0 true) =
            fun _ => false := by
          funext i; simp [Fin.tail, Function.update]
        have hfalse : ∀ m i, suffixParity m (fun _ => false) i = false := by
          intro m; induction m with
          | zero => intro i; exact Fin.elim0 i
          | succ m ihm =>
              intro i
              refine Fin.cases ?_ (fun i' => ?_) i
              · exact hfalse_tot m
              · exact ihm i'
        change suffixParity n (Fin.tail (Function.update (fun _ : Fin (n + 1) => false) 0 true)) j' = _
        rw [htail, hfalse]
        simp
      · have htail : Fin.tail (Function.update (fun _ : Fin (n + 1) => false) k'.succ true) =
            Function.update (fun _ : Fin n => false) k' true := by
          funext i
          by_cases hi : i = k'
          · subst hi; simp [Fin.tail, Function.update]
          · simp [Fin.tail, Function.update, hi]
        change totalParity n (Fin.tail (Function.update (fun _ : Fin (n + 1) => false) k'.succ true)) = _
        rw [htail, totalParity_update_single_eq]
        simp
      · have htail : Fin.tail (Function.update (fun _ : Fin (n + 1) => false) k'.succ true) =
            Function.update (fun _ : Fin n => false) k' true := by
          funext i
          by_cases hi : i = k'
          · subst hi; simp [Fin.tail, Function.update]
          · simp [Fin.tail, Function.update, hi]
        change suffixParity n (Fin.tail (Function.update (fun _ : Fin (n + 1) => false) k'.succ true)) j' = _
        rw [htail, ih k' j']
        simp [Fin.succ_lt_succ_iff]

/-- Matrix readback of `singleSiteChain n k nullPlus` places `J1` before `k`, `cl11EquivMat nullPlus`
at `k`, and `1` after `k`. -/
theorem leftMatrixEquiv_singleSiteChain_nullPlus (n : ℕ) (k : Fin n) :
    leftMatrixEquiv n (singleSiteChain n k nullPlus) =
      ordinaryChain n (fun j => if j < k then J1 else if j = k then cl11EquivMat nullPlus else 1) := by
  dsimp [singleSiteChain]
  have hhom : ∀ i : Fin n,
      CliffordAlgebra.involute (Function.update (fun _ => (1 : CliffordAlgebra q11)) k nullPlus i) =
        if Function.update (fun _ => false) k true i then
          -(Function.update (fun _ => (1 : CliffordAlgebra q11)) k nullPlus i)
        else Function.update (fun _ => (1 : CliffordAlgebra q11)) k nullPlus i := by
    intro i
    by_cases hi : i = k
    · subst hi; simp [involute_nullPlus]
    · simp [Function.update, hi]
  rw [nativeChain_matrix_suffixParity n _ _ hhom]
  congr 1
  funext j
  rw [suffixParity_update_single]
  by_cases hjlt : j < k
  · have hjne : j ≠ k := ne_of_lt hjlt
    simp [hjlt, hjne, Function.update]
  · by_cases hjeq : j = k
    · subst hjeq
      simp [Function.update]
    · simp [hjlt, hjeq, Function.update]

/-- XOR parity of all strictly earlier sites `j < k` in a chain of length `n`. -/
def prefixParity : (n : ℕ) → (Fin n → Bool) → Fin n → Bool :=
  Nat.rec (motive := fun n => (Fin n → Bool) → Fin n → Bool)
    (fun _ i => Fin.elim0 i)
    (fun _ ih p => Fin.cons false (fun k => Bool.xor (p 0) (ih (Fin.tail p) k)))

@[simp] theorem prefixParity_zero (n : ℕ) (p : Fin (n + 1) → Bool) :
    prefixParity (n + 1) p 0 = false := rfl

@[simp] theorem prefixParity_succ (n : ℕ) (p : Fin (n + 1) → Bool) (k : Fin n) :
    prefixParity (n + 1) p k.succ = Bool.xor (p 0) (prefixParity n (Fin.tail p) k) := rfl

private theorem mem_evenOdd_of_involute
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) (x : CliffordAlgebra Q) (q : Bool)
    (hx : CliffordAlgebra.involute x = if q then -x else x) :
    x ∈ CliffordAlgebra.evenOdd Q (if q then 1 else 0) := by
  obtain ⟨e, o, heo, _⟩ :=
    Submodule.existsUnique_add_of_isCompl (CliffordAlgebra.evenOdd_isCompl (Q := Q)) x
  have hinvol : CliffordAlgebra.involute x = (e : CliffordAlgebra Q) - o := by
    rw [← heo, map_add, CliffordAlgebra.involute_eq_of_mem_even e.property,
      CliffordAlgebra.involute_eq_of_mem_odd o.property, sub_eq_add_neg]
  cases q
  · simp only [Bool.false_eq_true, ↓reduceIte] at hx ⊢
    have hsum : (e : CliffordAlgebra Q) + o = (e : CliffordAlgebra Q) - o :=
      heo.trans (hx.symm.trans hinvol)
    have honeg : (o : CliffordAlgebra Q) = -o :=
      add_left_cancel (by simpa only [sub_eq_add_neg] using hsum)
    have hozero : (o : CliffordAlgebra Q) = 0 := by
      have htwo : (2 : ℝ) • (o : CliffordAlgebra Q) = 0 := by
        rw [two_smul]; nth_rw 2 [honeg]; exact add_neg_cancel _
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    rw [← heo, hozero, add_zero]
    exact e.property
  · simp only [↓reduceIte] at hx ⊢
    have hsum : (e : CliffordAlgebra Q) - o = -((e : CliffordAlgebra Q) + o) :=
      hinvol.symm.trans (hx.trans (congrArg Neg.neg heo.symm))
    have hneg_e : (e : CliffordAlgebra Q) = -(e : CliffordAlgebra Q) :=
      add_right_cancel (by simpa only [sub_eq_add_neg, neg_add] using hsum)
    have hezero : (e : CliffordAlgebra Q) = 0 := by
      have htwo : (2 : ℝ) • (e : CliffordAlgebra Q) = 0 := by
        rw [two_smul]; nth_rw 2 [hneg_e]; exact add_neg_cancel _
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    rw [← heo, hezero, zero_add]
    exact o.property

private theorem consNative_left_one_mul_consNative (n : ℕ)
    (c₁ c₂ : CliffordAlgebra q11) (x₂ : Clsplit n) :
    consNative n c₁ 1 * consNative n c₂ x₂ = consNative n (c₁ * c₂) x₂ := by
  rw [consNative_apply, consNative_apply, consNative_apply, ← map_mul]
  congr 1
  obtain ⟨e, o, heo, _⟩ :=
    Submodule.existsUnique_add_of_isCompl (CliffordAlgebra.evenOdd_isCompl (Q := q11)) c₂
  have hL : (c₁ ᵍ⊗ₜ[ℝ] (1 : Clsplit n) :
        CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) *
      ((e : CliffordAlgebra q11) ᵍ⊗ₜ[ℝ] x₂) = (c₁ * e) ᵍ⊗ₜ[ℝ] x₂ := by
    have h := GradedTensorProduct.tmul_zero_coe_mul_coe_tmul
      (CliffordAlgebra.evenOdd q11) (CliffordAlgebra.evenOdd (Qsplit n))
      c₁ (1 : CliffordAlgebra.evenOdd (Qsplit n) 0) e x₂
    simpa [one_mul] using h
  have hR : (c₁ ᵍ⊗ₜ[ℝ] (1 : Clsplit n) :
        CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) *
      ((o : CliffordAlgebra q11) ᵍ⊗ₜ[ℝ] x₂) = (c₁ * o) ᵍ⊗ₜ[ℝ] x₂ := by
    have h := GradedTensorProduct.tmul_zero_coe_mul_coe_tmul
      (CliffordAlgebra.evenOdd q11) (CliffordAlgebra.evenOdd (Qsplit n))
      c₁ (1 : CliffordAlgebra.evenOdd (Qsplit n) 0) o x₂
    simpa [one_mul] using h
  have hadd1 : (((e : CliffordAlgebra q11) + (o : CliffordAlgebra q11)) ᵍ⊗ₜ[ℝ] x₂ :
      CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) =
      ((e : CliffordAlgebra q11) ᵍ⊗ₜ[ℝ] x₂) + ((o : CliffordAlgebra q11) ᵍ⊗ₜ[ℝ] x₂) := by
    simp [GradedTensorProduct.tmul, TensorProduct.add_tmul]
  have hadd2 : ((c₁ * ((e : CliffordAlgebra q11) + (o : CliffordAlgebra q11))) ᵍ⊗ₜ[ℝ] x₂ :
      CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) =
      ((c₁ * e) ᵍ⊗ₜ[ℝ] x₂) + ((c₁ * o) ᵍ⊗ₜ[ℝ] x₂) := by
    rw [mul_add]; simp [GradedTensorProduct.tmul, TensorProduct.add_tmul]
  rw [← heo, hadd1, hadd2, mul_add, hL, hR]

private theorem consNative_mul_consNative_right_one (n : ℕ)
    (c₁ : CliffordAlgebra q11) (x₁ x₂ : Clsplit n) :
    consNative n c₁ x₁ * consNative n 1 x₂ = consNative n c₁ (x₁ * x₂) := by
  rw [consNative_apply, consNative_apply, consNative_apply, ← map_mul]
  congr 1
  obtain ⟨e, o, heo, _⟩ :=
    Submodule.existsUnique_add_of_isCompl (CliffordAlgebra.evenOdd_isCompl (Q := Qsplit n)) x₁
  have hL : (c₁ ᵍ⊗ₜ[ℝ] (e : Clsplit n) :
        CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) *
      ((1 : CliffordAlgebra q11) ᵍ⊗ₜ[ℝ] x₂) = c₁ ᵍ⊗ₜ[ℝ] (e * x₂) := by
    have h := GradedTensorProduct.tmul_coe_mul_zero_coe_tmul
      (CliffordAlgebra.evenOdd q11) (CliffordAlgebra.evenOdd (Qsplit n))
      c₁ e (1 : CliffordAlgebra.evenOdd q11 0) x₂
    simpa [mul_one] using h
  have hR : (c₁ ᵍ⊗ₜ[ℝ] (o : Clsplit n) :
        CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) *
      ((1 : CliffordAlgebra q11) ᵍ⊗ₜ[ℝ] x₂) = c₁ ᵍ⊗ₜ[ℝ] (o * x₂) := by
    have h := GradedTensorProduct.tmul_coe_mul_zero_coe_tmul
      (CliffordAlgebra.evenOdd q11) (CliffordAlgebra.evenOdd (Qsplit n))
      c₁ o (1 : CliffordAlgebra.evenOdd q11 0) x₂
    simpa [mul_one] using h
  have hadd1 : (c₁ ᵍ⊗ₜ[ℝ] ((e : Clsplit n) + (o : Clsplit n)) :
      CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) =
      (c₁ ᵍ⊗ₜ[ℝ] (e : Clsplit n)) + (c₁ ᵍ⊗ₜ[ℝ] (o : Clsplit n)) := by
    simp [GradedTensorProduct.tmul, TensorProduct.tmul_add]
  have hadd2 : (c₁ ᵍ⊗ₜ[ℝ] (((e : Clsplit n) + (o : Clsplit n)) * x₂) :
      CliffordAlgebra.evenOdd q11 ᵍ⊗[ℝ] CliffordAlgebra.evenOdd (Qsplit n)) =
      (c₁ ᵍ⊗ₜ[ℝ] (e * x₂)) + (c₁ ᵍ⊗ₜ[ℝ] (o * x₂)) := by
    rw [add_mul]; simp [GradedTensorProduct.tmul, TensorProduct.tmul_add]
  rw [← heo, hadd1, hadd2, add_mul, hL, hR]

private theorem consNative_one_mul_consNative_homogeneous (n : ℕ)
    (x₁ : Clsplit n) (q : Bool) (hx₁ : nativeParity n x₁ = if q then -x₁ else x₁)
    (c₂ : CliffordAlgebra q11) (p₀ : Bool) (hc₂ : CliffordAlgebra.involute c₂ = if p₀ then -c₂ else c₂)
    (x₂ : Clsplit n) :
    consNative n 1 x₁ * consNative n c₂ x₂ =
      (if (q && p₀) then (-1 : ℝ) else 1) • consNative n c₂ (x₁ * x₂) := by
  rw [consNative_apply, consNative_apply, consNative_apply, ← map_mul, ← map_smul]
  congr 1
  have hx₁' := mem_evenOdd_of_involute (Qsplit n) x₁ q hx₁
  have hc₂' := mem_evenOdd_of_involute q11 c₂ p₀ hc₂
  have h := GradedTensorProduct.tmul_coe_mul_coe_tmul
    (CliffordAlgebra.evenOdd q11) (CliffordAlgebra.evenOdd (Qsplit n))
    (1 : CliffordAlgebra q11) ⟨x₁, hx₁'⟩ ⟨c₂, hc₂'⟩ x₂
  rw [one_mul] at h
  rw [h]
  cases q <;> cases p₀ <;> simp

private theorem consNative_mul_consNative_one_homogeneous (n : ℕ)
    (c₁ : CliffordAlgebra q11) (x₁ : Clsplit n) (r : Bool) (hx₁ : nativeParity n x₁ = if r then -x₁ else x₁)
    (c₂ : CliffordAlgebra q11) (q : Bool) (hc₂ : CliffordAlgebra.involute c₂ = if q then -c₂ else c₂) :
    consNative n c₁ x₁ * consNative n c₂ 1 =
      (if (r && q) then (-1 : ℝ) else 1) • consNative n (c₁ * c₂) x₁ := by
  rw [consNative_apply, consNative_apply, consNative_apply, ← map_mul, ← map_smul]
  congr 1
  have hx₁' := mem_evenOdd_of_involute (Qsplit n) x₁ r hx₁
  have hc₂' := mem_evenOdd_of_involute q11 c₂ q hc₂
  have h := GradedTensorProduct.tmul_coe_mul_coe_tmul
    (CliffordAlgebra.evenOdd q11) (CliffordAlgebra.evenOdd (Qsplit n))
    c₁ ⟨x₁, hx₁'⟩ ⟨c₂, hc₂'⟩ (1 : Clsplit n)
  rw [mul_one] at h
  rw [h]
  cases r <;> cases q <;> simp

/-- Left multiplication by an odd single-site chain `singleSiteChain n k d` acts on any
homogeneous `nativeChain n a` by multiplying site `k` on the left by `d`, with sign
`(-1) ^ prefixParity n p k`. -/
theorem singleSiteChain_mul_nativeChain_homogeneous (n : ℕ) (k : Fin n)
    (d : CliffordAlgebra q11) (hd : CliffordAlgebra.involute d = -d)
    (a : Fin n → CliffordAlgebra q11) (p : Fin n → Bool)
    (ha : ∀ i, CliffordAlgebra.involute (a i) = if p i then -(a i) else a i) :
    singleSiteChain n k d * nativeChain n a =
      (if prefixParity n p k then (-1 : ℝ) else 1) •
        nativeChain n (Function.update a k (d * a k)) := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      refine Fin.cases ?_ ?_ k
      · rw [singleSiteChain_zero, nativeChain, consNative_left_one_mul_consNative,
          prefixParity_zero]
        simp only [Bool.false_eq_true, ↓reduceIte, one_smul]
        have htail : Fin.tail (Function.update a 0 (d * a 0)) = Fin.tail a := by
          funext i; simp [Fin.tail, Function.update]
        change consNative n (d * a 0) (nativeChain n (Fin.tail a)) =
          consNative n (Function.update a 0 (d * a 0) 0)
            (nativeChain n (Fin.tail (Function.update a 0 (d * a 0))))
        rw [htail, Function.update_self]
      · intro k'
        rw [singleSiteChain_succ, nativeChain, prefixParity_succ]
        have hd_hom : CliffordAlgebra.involute d = if true then -d else d := by simp [hd]
        have hs := singleSiteChain_homogeneous n k' d true hd_hom
        rw [consNative_one_mul_consNative_homogeneous n (singleSiteChain n k' d) true hs
          (a 0) (p 0) (ha 0) (nativeChain n (Fin.tail a))]
        rw [ih k' (Fin.tail a) (Fin.tail p) (fun i => ha i.succ)]
        have hup0 : Function.update a k'.succ (d * a k'.succ) 0 = a 0 :=
          Function.update_of_ne (Fin.succ_ne_zero k').symm _ _
        have huptail : Fin.tail (Function.update a k'.succ (d * a k'.succ)) =
            Function.update (Fin.tail a) k' (d * Fin.tail a k') := by
          funext i
          by_cases hi : i = k'
          · subst hi; simp [Fin.tail, Function.update]
          · simp [Fin.tail, Function.update, hi]
        have hcons :
            consNative n (a 0) (nativeChain n (Function.update (Fin.tail a) k' (d * Fin.tail a k'))) =
              nativeChain (n + 1) (Function.update a k'.succ (d * a k'.succ)) := by
          change consNative n (a 0) (nativeChain n (Function.update (Fin.tail a) k' (d * Fin.tail a k'))) =
            consNative n (Function.update a k'.succ (d * a k'.succ) 0)
              (nativeChain n (Fin.tail (Function.update a k'.succ (d * a k'.succ))))
          rw [hup0, huptail]
        rw [map_smul (consNative n (a 0)), hcons, smul_smul]
        congr 1
        cases p 0 <;> cases prefixParity n (Fin.tail p) k' <;> simp

/-- Right multiplication by an odd single-site chain `singleSiteChain n k d` acts on any
homogeneous `nativeChain n a` by multiplying site `k` on the right by `d`, with sign
`(-1) ^ suffixParity n p k`. -/
theorem nativeChain_mul_singleSiteChain_homogeneous (n : ℕ) (k : Fin n)
    (d : CliffordAlgebra q11) (hd : CliffordAlgebra.involute d = -d)
    (a : Fin n → CliffordAlgebra q11) (p : Fin n → Bool)
    (ha : ∀ i, CliffordAlgebra.involute (a i) = if p i then -(a i) else a i) :
    nativeChain n a * singleSiteChain n k d =
      (if suffixParity n p k then (-1 : ℝ) else 1) •
        nativeChain n (Function.update a k (a k * d)) := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      refine Fin.cases ?_ ?_ k
      · rw [singleSiteChain_zero, nativeChain]
        have htail_par := nativeChain_homogeneous n (Fin.tail a) (Fin.tail p) (fun i => ha i.succ)
        have hd_hom : CliffordAlgebra.involute d = if true then -d else d := by simp [hd]
        rw [consNative_mul_consNative_one_homogeneous n (a 0) (nativeChain n (Fin.tail a))
          (totalParity n (Fin.tail p)) htail_par d true hd_hom]
        have hsuf : suffixParity (n + 1) p 0 = totalParity n (Fin.tail p) := rfl
        have htail : Fin.tail (Function.update a 0 (a 0 * d)) = Fin.tail a := by
          funext i; simp [Fin.tail, Function.update]
        have hcons :
            consNative n (a 0 * d) (nativeChain n (Fin.tail a)) =
              nativeChain (n + 1) (Function.update a 0 (a 0 * d)) := by
          change consNative n (a 0 * d) (nativeChain n (Fin.tail a)) =
            consNative n (Function.update a 0 (a 0 * d) 0)
              (nativeChain n (Fin.tail (Function.update a 0 (a 0 * d))))
          rw [htail, Function.update_self]
        rw [hsuf, hcons]
        cases totalParity n (Fin.tail p) <;> simp
      · intro k'
        rw [singleSiteChain_succ, nativeChain, consNative_mul_consNative_right_one,
          ih k' (Fin.tail a) (Fin.tail p) (fun i => ha i.succ)]
        have hup0 : Function.update a k'.succ (a k'.succ * d) 0 = a 0 :=
          Function.update_of_ne (Fin.succ_ne_zero k').symm _ _
        have huptail : Fin.tail (Function.update a k'.succ (a k'.succ * d)) =
            Function.update (Fin.tail a) k' (Fin.tail a k' * d) := by
          funext i
          by_cases hi : i = k'
          · subst hi; simp [Fin.tail, Function.update]
          · simp [Fin.tail, Function.update, hi]
        have hsuf : suffixParity (n + 1) p k'.succ =
            suffixParity n (Fin.tail p) k' := rfl
        have hcons :
            consNative n (a 0) (nativeChain n (Function.update (Fin.tail a) k' (Fin.tail a k' * d))) =
              nativeChain (n + 1) (Function.update a k'.succ (a k'.succ * d)) := by
          change consNative n (a 0)
              (nativeChain n (Function.update (Fin.tail a) k' (Fin.tail a k' * d))) =
            consNative n (Function.update a k'.succ (a k'.succ * d) 0)
              (nativeChain n (Fin.tail (Function.update a k'.succ (a k'.succ * d))))
          rw [hup0, huptail]
        rw [map_smul (consNative n (a 0)), hcons, hsuf]

theorem totalParity_xor_suffixParity (n : ℕ) (p : Fin n → Bool) (k : Fin n) :
    Bool.xor (totalParity n p) (suffixParity n p k) =
      Bool.xor (prefixParity n p k) (p k) := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      refine Fin.cases ?_ ?_ k
      · have htot : totalParity (n + 1) p = Bool.xor (p 0) (totalParity n (Fin.tail p)) := rfl
        have hsuf : suffixParity (n + 1) p 0 = totalParity n (Fin.tail p) := rfl
        rw [htot, hsuf, prefixParity_zero]
        cases p 0 <;> cases totalParity n (Fin.tail p) <;> rfl
      · intro k'
        have htot : totalParity (n + 1) p = Bool.xor (p 0) (totalParity n (Fin.tail p)) := rfl
        have hsuf : suffixParity (n + 1) p k'.succ = suffixParity n (Fin.tail p) k' := rfl
        rw [htot, hsuf, prefixParity_succ]
        have hk := ih (Fin.tail p) k'
        change Bool.xor (Bool.xor (p 0) (totalParity n (Fin.tail p)))
            (suffixParity n (Fin.tail p) k') =
          Bool.xor (Bool.xor (p 0) (prefixParity n (Fin.tail p) k')) (Fin.tail p k')
        rw [Bool.xor_assoc, hk, ← Bool.xor_assoc]

theorem singleSiteChain_mul_singleSiteChain (n : ℕ) (k : Fin n)
    (c d : CliffordAlgebra q11) :
    singleSiteChain n k c * singleSiteChain n k d = singleSiteChain n k (c * d) := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      refine Fin.cases ?_ (fun k' => ?_) k
      · rw [singleSiteChain_zero, singleSiteChain_zero, singleSiteChain_zero,
          consNative_left_one_mul_consNative]
      · rw [singleSiteChain_succ, singleSiteChain_succ, singleSiteChain_succ,
          consNative_mul_consNative_right_one, ih k']

theorem singleSiteChain_zero_arg (n : ℕ) (k : Fin n) :
    singleSiteChain n k 0 = 0 := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      refine Fin.cases ?_ (fun k' => ?_) k
      · rw [singleSiteChain_zero, consNative_zero_head]
      · rw [singleSiteChain_succ, ih k', map_zero]

theorem singleSiteChain_nullPlus_sq (n : ℕ) (k : Fin n) :
    singleSiteChain n k nullPlus * singleSiteChain n k nullPlus = 0 := by
  rw [singleSiteChain_mul_singleSiteChain, nullPlus_sq, singleSiteChain_zero_arg]

theorem singleSiteChain_nullMinus_sq (n : ℕ) (k : Fin n) :
    singleSiteChain n k nullMinus * singleSiteChain n k nullMinus = 0 := by
  rw [singleSiteChain_mul_singleSiteChain, nullMinus_sq, singleSiteChain_zero_arg]

theorem singleSiteChain_null_car (n : ℕ) (k : Fin n) :
    singleSiteChain n k nullPlus * singleSiteChain n k nullMinus +
      singleSiteChain n k nullMinus * singleSiteChain n k nullPlus = 1 := by
  rw [singleSiteChain_mul_singleSiteChain, singleSiteChain_mul_singleSiteChain]
  have hadd : ∀ c d : CliffordAlgebra q11,
      singleSiteChain n k c + singleSiteChain n k d = singleSiteChain n k (c + d) := by
    intro c d
    induction n with
    | zero => exact Fin.elim0 k
    | succ n ih =>
        refine Fin.cases ?_ ?_ k
        · rw [singleSiteChain_zero, singleSiteChain_zero, singleSiteChain_zero, consNative_add_head]
        · intro k'
          rw [singleSiteChain_succ, singleSiteChain_succ, singleSiteChain_succ,
            ← map_add (consNative n 1), ih k']
  rw [hadd, nullPlus_mul_nullMinus_add]
  dsimp [singleSiteChain]
  have hup : Function.update (fun _ : Fin n => (1 : CliffordAlgebra q11)) k 1 =
      fun _ => (1 : CliffordAlgebra q11) := by
    funext i; by_cases hi : i = k <;> simp [Function.update, hi]
  rw [hup, nativeChain_ones]

end SingleSiteChainsAndPrefixParity

end InfoGeometry.Clifford.Cl11HomogeneousChains
