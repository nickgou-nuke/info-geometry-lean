/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorContentNetwork.Basic
import InfoGeometry.Core.PeirceCompressionDefect
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Data.Matrix.Basis

/-!
# Causal support and compression of real block operators

Every permitted block is an arbitrary real square matrix. Transitivity of
the vertex order makes causal support stable under ordered block products.
Compression identities reuse the existing generic Peirce defect owner.
-/

namespace InfoGeometry.Canonical.OperatorContentNetwork

abbrev BlockOperator (V n : Type*) := Matrix V V (Operator n)

variable {V n : Type*}

/-- The relation specifies the permitted blocks, without restricting their entries. -/
def SupportedBy (r : V → V → Prop) (A : BlockOperator V n) : Prop :=
  ∀ i j, ¬ r i j → A i j = 0

theorem supportedBy_zero (r : V → V → Prop) :
    SupportedBy r (0 : BlockOperator V n) := by
  intro i j _
  rfl

theorem supportedBy_add {r : V → V → Prop} {A B : BlockOperator V n}
    (hA : SupportedBy r A) (hB : SupportedBy r B) : SupportedBy r (A + B) := by
  intro i j hij
  change A i j + B i j = 0
  rw [hA i j hij, hB i j hij, add_zero]

theorem supportedBy_neg {r : V → V → Prop} {A : BlockOperator V n}
    (hA : SupportedBy r A) : SupportedBy r (-A) := by
  intro i j hij
  change -A i j = 0
  rw [hA i j hij, neg_zero]

theorem supportedBy_sub {r : V → V → Prop} {A B : BlockOperator V n}
    (hA : SupportedBy r A) (hB : SupportedBy r B) : SupportedBy r (A - B) := by
  simpa only [sub_eq_add_neg] using supportedBy_add hA (supportedBy_neg hB)

theorem supportedBy_smul {r : V → V → Prop} {A : BlockOperator V n}
    (hA : SupportedBy r A) (c : ℝ) : SupportedBy r (c • A) := by
  intro i j hij
  change c • A i j = 0
  rw [hA i j hij, smul_zero]

theorem supportedBy_mono {r s : V → V → Prop} {A : BlockOperator V n}
    (hrs : ∀ i j, r i j → s i j) (hA : SupportedBy r A) : SupportedBy s A := by
  intro i j hij
  exact hA i j (fun hr => hij (hrs i j hr))

/-- Transposition reverses the vertex support relation while retaining the block entries. -/
theorem supportedBy_transpose_iff (r : V → V → Prop) (A : BlockOperator V n) :
    SupportedBy (fun i j => r j i) A.transpose ↔ SupportedBy r A := by
  constructor
  · intro h i j hij
    exact h j i hij
  · intro h i j hij
    exact h j i hij

section Causal

variable [PartialOrder V]

def CausalSupport (A : BlockOperator V n) : Prop := SupportedBy (· ≤ ·) A

theorem causalSupport_zero : CausalSupport (0 : BlockOperator V n) :=
  supportedBy_zero _

theorem causalSupport_add {A B : BlockOperator V n}
    (hA : CausalSupport A) (hB : CausalSupport B) : CausalSupport (A + B) :=
  supportedBy_add hA hB

theorem causalSupport_sub {A B : BlockOperator V n}
    (hA : CausalSupport A) (hB : CausalSupport B) : CausalSupport (A - B) :=
  supportedBy_sub hA hB

theorem causalSupport_one [DecidableEq V] [DecidableEq n] :
    CausalSupport (1 : BlockOperator V n) := by
  intro i j hij
  have hne : i ≠ j := by
    intro h
    subst j
    exact hij le_rfl
  simp [hne]

theorem causalSupport_transpose_iff (A : BlockOperator V n) :
    SupportedBy (fun i j : V => j ≤ i) A.transpose ↔ CausalSupport A :=
  supportedBy_transpose_iff _ A

theorem causalSupport_single [DecidableEq V] (i j : V) (M : Operator n) (hij : i ≤ j) :
    CausalSupport (Matrix.single i j M) := by
  intro a b hab
  apply Matrix.single_apply_of_ne
  rintro ⟨rfl, rfl⟩
  exact hab hij

variable [Fintype V] [DecidableEq V] [Fintype n] [DecidableEq n]

omit [DecidableEq V] [DecidableEq n] in
/-- Transitivity supplies a vanishing factor in every forbidden product block. -/
theorem causalSupport_mul {A B : BlockOperator V n}
    (hA : CausalSupport A) (hB : CausalSupport B) : CausalSupport (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i ≤ k
  · have hkj : ¬ k ≤ j := fun h => hij (hik.trans h)
    rw [hB k j hkj, mul_zero]
  · rw [hA i k hik, zero_mul]

theorem causalSupport_algebraMap (c : ℝ) :
    CausalSupport (algebraMap ℝ (BlockOperator V n) c) := by
  intro i j hij
  have hne : i ≠ j := by
    intro h
    subst j
    exact hij le_rfl
  simp [Matrix.algebraMap_matrix_apply, hne]

/-- A real subalgebra of full matrix-valued causal blocks. -/
def causalSubalgebra : Subalgebra ℝ (BlockOperator V n) where
  carrier := {A | CausalSupport A}
  zero_mem' := causalSupport_zero
  one_mem' := causalSupport_one
  add_mem' := causalSupport_add
  mul_mem' := causalSupport_mul
  algebraMap_mem' := causalSupport_algebraMap

@[simp] theorem mem_causalSubalgebra (A : BlockOperator V n) :
    A ∈ causalSubalgebra (V := V) (n := n) ↔ CausalSupport A := Iff.rfl

/-- Each permitted block, including every strict causal block, carries any real operator. -/
theorem causalBlock_evaluation_surjective (i j : V) (hij : i ≤ j) :
    Function.Surjective (fun A : causalSubalgebra (V := V) (n := n) => A.1 i j) := by
  intro M
  refine ⟨⟨Matrix.single i j M, causalSupport_single i j M hij⟩, ?_⟩
  exact Matrix.single_apply_same i j M

theorem causalSupport_pow {A : BlockOperator V n} (hA : CausalSupport A) (k : ℕ) :
    CausalSupport (A ^ k) :=
  (causalSubalgebra (V := V) (n := n)).pow_mem hA k

omit [DecidableEq V] [DecidableEq n] in
theorem causalSupport_commutator {A B : BlockOperator V n}
    (hA : CausalSupport A) (hB : CausalSupport B) : CausalSupport (A * B - B * A) :=
  causalSupport_sub (causalSupport_mul hA hB) (causalSupport_mul hB hA)

end Causal

section Compression

variable [Fintype V] [DecidableEq V] [Fintype n] [DecidableEq n]

def compress (P A : BlockOperator V n) : BlockOperator V n := P * A * P

omit [DecidableEq V] [DecidableEq n] in
theorem compress_add (P A B : BlockOperator V n) :
    compress P (A + B) = compress P A + compress P B := by
  simp only [compress, mul_add, add_mul]

omit [DecidableEq V] [DecidableEq n] in
theorem compress_sub (P A B : BlockOperator V n) :
    compress P (A - B) = compress P A - compress P B := by
  simp only [compress, mul_sub, sub_mul]

def compressionLinear (P : BlockOperator V n) : BlockOperator V n →ₗ[ℝ] BlockOperator V n where
  toFun := compress P
  map_add' := compress_add P
  map_smul' c A := by simp [compress]

omit [DecidableEq V] [DecidableEq n] in
theorem compress_idempotent (P A : BlockOperator V n) (hP : P * P = P) :
    compress P (compress P A) = compress P A := by
  calc
    _ = (P * P) * A * (P * P) := by simp only [compress, mul_assoc]
    _ = _ := by simp only [hP, compress]

/-- The generic owner theorem is instantiated on noncommutative real block operators. -/
theorem compress_mul_defect (P A B : BlockOperator V n) (hP : P * P = P) :
    compress P (A * B) - compress P A * compress P B = P * A * (1 - P) * B * P :=
  InfoGeometry.Core.PeirceCompressionDefect.compression_mul_defect P A B hP

theorem compress_mul_eq_iff (P A B : BlockOperator V n) (hP : P * P = P) :
    compress P (A * B) = compress P A * compress P B ↔ P * A * (1 - P) * B * P = 0 := by
  rw [← sub_eq_zero, compress_mul_defect P A B hP]

theorem compress_mul_of_left_compatible (P A B : BlockOperator V n)
    (hP : P * P = P) (hA : P * A = P * A * P) :
    compress P (A * B) = compress P A * compress P B := by
  apply (compress_mul_eq_iff P A B hP).2
  have htransfer : P * A * (1 - P) = 0 := by
    rw [mul_sub, mul_one, ← hA, sub_self]
  rw [htransfer, zero_mul, zero_mul]

theorem compress_mul_ne_of_transfer_ne (P A B : BlockOperator V n)
    (hP : P * P = P) (h : P * A * (1 - P) * B * P ≠ 0) :
    compress P (A * B) ≠ compress P A * compress P B :=
  mt (compress_mul_eq_iff P A B hP).mp h

theorem compress_commutator (P A B : BlockOperator V n)
    (hP : P * P = P) (hA : P * A = P * A * P) (hB : P * B = P * B * P) :
    compress P (A * B - B * A) =
      compress P A * compress P B - compress P B * compress P A := by
  rw [compress_sub, compress_mul_of_left_compatible P A B hP hA,
    compress_mul_of_left_compatible P B A hP hB]

end Compression

end InfoGeometry.Canonical.OperatorContentNetwork
