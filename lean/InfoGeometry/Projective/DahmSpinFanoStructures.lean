/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.ZMod.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Spin squaring (`g = 2`), the `PG(3,2)` Pauli geometry, and an order-3 Clifford element

CAS-confirmed (SymPy / Sage / GAP, scratch scripts `stage456.py`), then proved here.

1. **Pauli squaring with operator-valued momenta.**  In any `[Ring B] [Algebra ℂ B]`,
   for noncommuting `π₁ π₂ π₃ : B`,
   `(σ·π)² = (π·π) 𝟙 + i σ·(π × π)` with `(π × π)_l = ε_{jkl}[π_j, π_k]/…` written
   as explicit commutators (`pauliDot_sq`).  If `[π_j, π_k] = i e ε_{jkl} B_l`
   (minimal coupling `π = p - eA`, `ħ = 1`), then `(σ·π)² = π·π 𝟙 - e σ·B`
   (`pauliDot_sq_minimal_coupling`).  With `H = (σ·π)²/2m` and `S = σ/2` this is
   the Zeeman term `-(e/2m) g S·B` with `g = 2`.  This is the standard algebraic
   derivation of `g = 2`; Dahm's geometric "force pair" reading is an
   interpretation of the same identity and is not itself a theorem proved here.
2. **`PG(3,2)` as the two-qubit Pauli geometry.**  Points: the 15 nonzero vectors
   of `𝔽₂⁴`; lines: the 35 triples `{a, b, a + b}`.  With the real Pauli labels
   `P(x,z) = XˣZᶻ` and `P(a) = P(a₀,a₁) ⊗ P(a₂,a₃)`, every line satisfies
   `P(a) P(b) P(a+b) = ±𝟙` (`pauli2_line_product`).  The source's `O₁O₂O₃ = 𝟙`
   therefore holds projectively, i.e. up to the sign `±1`; CAS shows both signs
   occur.  Exactly 15 lines are symplectically isotropic (`GQ(2,2)`), and
   GAP confirms `Sp(4,2) ≅ S₆` acts on the 15 points (recorded, not formalised).
3. **Order-3 Clifford element.**  `J = ½(𝟙 - iX - iY - iZ)` is in `SU(2)`, cycles
   `X → Y → Z → X` by conjugation, and `J³ = -𝟙`.  Hence `J³ = 𝟙` holds in
   `PSU(2)` (as an automorphism), not in `SU(2)`.

#### BUCKET 1: CLOSED FINITE THEOREMS
The operator Pauli identity, finite `PG(3,2)` enumeration, and explicit
two-qubit Pauli multiplication laws are proved in their stated carriers.

#### BUCKET 2: CONDITIONAL THEOREMS
The minimal-coupling identity assumes the three displayed commutator laws.

#### BUCKET 3: OPEN CLOSURE DEBT
The geometric `g = 2` interpretation, the `Sp(4,2) ≅ S₆` action, and a
projective or physical scattering construction are not established here.
-/

namespace InfoGeometry.Projective.DahmSpinFanoStructures

open Matrix Complex
open scoped Kronecker

/-! ## 1. Pauli squaring over a noncommutative ring -/

section PauliSquare

variable {B : Type*} [Ring B] [Algebra ℂ B]

/-- `σ·π = σ₁ π₁ + σ₂ π₂ + σ₃ π₃` with operator-valued `πₖ`. -/
def pauliDot (p₁ p₂ p₃ : B) : Matrix (Fin 2) (Fin 2) B :=
  !![p₃, p₁ - I • p₂;
     p₁ + I • p₂, -p₃]

/-- **Operator Pauli identity:** `(σ·π)² = (π·π) 𝟙 + i σ·[π × π]`, entrywise. -/
theorem pauliDot_sq (p₁ p₂ p₃ : B) :
    pauliDot p₁ p₂ p₃ * pauliDot p₁ p₂ p₃ =
      !![p₁ * p₁ + p₂ * p₂ + p₃ * p₃ + I • (p₁ * p₂ - p₂ * p₁),
          (p₃ * p₁ - p₁ * p₃) + I • (p₂ * p₃ - p₃ * p₂);
         -(p₃ * p₁ - p₁ * p₃) + I • (p₂ * p₃ - p₃ * p₂),
          p₁ * p₁ + p₂ * p₂ + p₃ * p₃ - I • (p₁ * p₂ - p₂ * p₁)] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [pauliDot, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.head_fin_const, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
      Complex.I_mul_I, neg_smul, one_smul, smul_sub, smul_add, neg_mul, mul_neg, smul_neg,
      neg_neg] <;> abel

/-- `σ·B` for a field `B₁ B₂ B₃ : B`. -/
def sigmaDotField (B₁ B₂ B₃ : B) : Matrix (Fin 2) (Fin 2) B := pauliDot B₁ B₂ B₃

/-- **`g = 2`:** under minimal-coupling commutators `[π_j, π_k] = i e ε_{jkl} B_l`,
`(σ·π)² = (π·π) 𝟙 - e σ·B`, written entrywise (`σ·B = pauliDot B₁ B₂ B₃`). -/
theorem pauliDot_sq_minimal_coupling (p₁ p₂ p₃ B₁ B₂ B₃ : B) (e : ℂ)
    (h₁₂ : p₁ * p₂ - p₂ * p₁ = (I * e) • B₃)
    (h₂₃ : p₂ * p₃ - p₃ * p₂ = (I * e) • B₁)
    (h₃₁ : p₃ * p₁ - p₁ * p₃ = (I * e) • B₂) :
    pauliDot p₁ p₂ p₃ * pauliDot p₁ p₂ p₃ =
      !![p₁ * p₁ + p₂ * p₂ + p₃ * p₃, 0; 0, p₁ * p₁ + p₂ * p₂ + p₃ * p₃] -
        e • sigmaDotField B₁ B₂ B₃ := by
  have hIIe : I * (I * e) = -e := by rw [← mul_assoc, I_mul_I, neg_one_mul]
  rw [pauliDot_sq, h₁₂, h₂₃, h₃₁]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [sigmaDotField, pauliDot, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, smul_smul, smul_sub, smul_add, smul_neg, hIIe, neg_smul,
      mul_comm e I, sub_zero, zero_sub] <;> abel

end PauliSquare

/-! ## 2. `PG(3,2)` and the two-qubit Pauli labels -/

section Fano

/-- `𝔽₂⁴`. -/
abbrev F24 := Fin 4 → ZMod 2

/-! Points of `PG(3,2)` are encoded as `Fin 16` bit vectors `(x₁, z₁, x₂, z₂)` (bits 0–3);
vector addition is bitwise `xor`.  Lines `{a, b, a ⊕ b}` are counted once each as
strictly increasing triples. -/

/-- `𝔽₂⁴` addition on the bit encoding. -/
def bxor (a b : Fin 16) : Fin 16 := ⟨(a.val ^^^ b.val) % 16, Nat.mod_lt _ (by norm_num)⟩

/-- Symplectic form `x₁z₁' + z₁x₁' + x₂z₂' + z₂x₂'` on the bit encoding. -/
def sympBits (a b : Fin 16) : Bool :=
  ((a.val.testBit 0 && b.val.testBit 1) ^^ (a.val.testBit 1 && b.val.testBit 0)) ^^
    ((a.val.testBit 2 && b.val.testBit 3) ^^ (a.val.testBit 3 && b.val.testBit 2))

/-- The 15 points of `PG(3,2)`. -/
def pg32Points : Finset (Fin 16) := Finset.univ.filter (· ≠ 0)

/-- The nonzero bit vectors give the 15 projective points. -/
theorem pg32Points_card : pg32Points.card = 15 := by
  have hset : pg32Points = Finset.univ.erase (0 : Fin 16) := by
    ext x
    simp [pg32Points]
  rw [hset, Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin 16))]
  simp

/-- Lines `{a < b < a ⊕ b}` of `PG(3,2)`, one representative per line. -/
def pg32Lines : Finset (Fin 16 × Fin 16) :=
  Finset.univ.filter (fun ab => 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < bxor ab.1 ab.2)

/-- The canonical sorted representatives enumerate the 35 projective lines. -/
theorem pg32Lines_card : pg32Lines.card = 35 := by decide

/-- The third point of every line is nonzero and differs from either chosen
point. -/
theorem pg32Lines_third (ab : Fin 16 × Fin 16) (h : ab ∈ pg32Lines) :
    bxor ab.1 ab.2 ≠ 0 ∧ bxor ab.1 ab.2 ≠ ab.1 ∧ bxor ab.1 ab.2 ≠ ab.2 := by
  simp only [pg32Lines, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨ne_of_gt (h1.trans (h2.trans h3)), ne_of_gt (h2.trans h3), ne_of_gt h3⟩

/-- Exactly 15 lines are totally isotropic (the generalized quadrangle `GQ(2,2)`). -/
theorem pg32_isotropic_lines_card :
    (pg32Lines.filter (fun ab => sympBits ab.1 ab.2 = false)).card = 15 := by decide

/-- Single-qubit real Pauli labels `P(x,z) = Xˣ Zᶻ` over `ℤ`. -/
def pauli1 (x z : ZMod 2) : Matrix (Fin 2) (Fin 2) ℤ :=
  (if x = 1 then !![0, 1; 1, 0] else 1) * (if z = 1 then !![1, 0; 0, -1] else 1)

/-- Single-qubit labels multiply up to sign. -/
theorem pauli1_mul (x z x' z' : ZMod 2) :
    pauli1 x z * pauli1 x' z' = pauli1 (x + x') (z + z') ∨
      pauli1 x z * pauli1 x' z' = -pauli1 (x + x') (z + z') := by
  revert x z x' z'; decide

/-- Single-qubit labels square to `±1`. -/
theorem pauli1_sq (x z : ZMod 2) : pauli1 x z * pauli1 x z = 1 ∨ pauli1 x z * pauli1 x z = -1 := by
  revert x z; decide

/-- Two-qubit labels `P(a) = P(a₀,a₁) ⊗ P(a₂,a₃)`. -/
def pauli2 (a : F24) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ :=
  pauli1 (a 0) (a 1) ⊗ₖ pauli1 (a 2) (a 3)

/-- Negating the first tensor factor negates the Kronecker product. -/
private theorem neg_kron {m n : Type*} (A : Matrix m m ℤ) (B : Matrix n n ℤ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i, j⟩ ⟨k, l⟩; simp [Matrix.kroneckerMap_apply]

/-- Negating the second tensor factor negates the Kronecker product. -/
private theorem kron_neg {m n : Type*} (A : Matrix m m ℤ) (B : Matrix n n ℤ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i, j⟩ ⟨k, l⟩; simp [Matrix.kroneckerMap_apply]

/-- Tensor Pauli labels multiply to the xor label up to a real sign. -/
theorem pauli2_mul (a b : F24) :
    pauli2 a * pauli2 b = pauli2 (a + b) ∨ pauli2 a * pauli2 b = -pauli2 (a + b) := by
  unfold pauli2
  rw [← Matrix.mul_kronecker_mul]
  rcases pauli1_mul (a 0) (a 1) (b 0) (b 1) with h | h <;>
    rcases pauli1_mul (a 2) (a 3) (b 2) (b 3) with h' | h' <;>
    rw [h, h'] <;> simp only [Pi.add_apply, neg_kron, kron_neg, neg_neg] <;> simp

/-- Every two-qubit real Pauli label squares to a signed identity. -/
theorem pauli2_sq (a : F24) : pauli2 a * pauli2 a = 1 ∨ pauli2 a * pauli2 a = -1 := by
  unfold pauli2
  rw [← Matrix.mul_kronecker_mul]
  rcases pauli1_sq (a 0) (a 1) with h | h <;> rcases pauli1_sq (a 2) (a 3) with h' | h' <;>
    rw [h, h'] <;> simp only [Matrix.one_kronecker_one, neg_kron, kron_neg, neg_neg] <;> simp

/-- Every encoded line triple multiplies to a signed identity. -/
theorem pauli2_line_product (a b : F24) :
    pauli2 a * pauli2 b * pauli2 (a + b) = 1 ∨ pauli2 a * pauli2 b * pauli2 (a + b) = -1 := by
  rcases pauli2_mul a b with h | h <;> rcases pauli2_sq (a + b) with h' | h' <;>
    simp [h, h']

end Fano

/-! ## 3. Order-3 Clifford element `J` -/

section Clifford

/-- Pauli matrices over `ℂ`. -/
def σX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
def σZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `J = ½(𝟙 - iX - iY - iZ)`. -/
noncomputable def cliffordJ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 - I) / 2, (-1 - I) / 2; (1 - I) / 2, (1 + I) / 2]

/-- Coordinate form of the order-three spin element. -/
theorem cliffordJ_def :
    cliffordJ = (1 / 2 : ℂ) • (1 - I • σX - I • σY - I • σZ) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [cliffordJ, σX, σY, σZ] <;> ring_nf <;> simp [I_sq] <;> ring

/-- The spin element has determinant one. -/
theorem cliffordJ_det : cliffordJ.det = 1 := by
  rw [cliffordJ, Matrix.det_fin_two_of]
  ring_nf
  rw [I_sq]
  ring

/-- The spin element is unitary. -/
theorem cliffordJ_unitary : cliffordJᴴ * cliffordJ = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [cliffordJ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.one_apply_eq, Matrix.one_apply_ne,
      ne_eq, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, not_false_eq_true, OfNat.ofNat_ne_one,
      zero_ne_one, one_ne_zero] <;>
    apply Complex.ext <;> simp [Complex.div_re, Complex.div_im] <;> norm_num

/-- `J X = Y J`, `J Y = Z J`, `J Z = X J`: conjugation by `J` cycles `X → Y → Z → X`. -/
theorem cliffordJ_cycles :
    cliffordJ * σX = σY * cliffordJ ∧ cliffordJ * σY = σZ * cliffordJ ∧
      cliffordJ * σZ = σX * cliffordJ := by
  refine ⟨?_, ?_, ?_⟩ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [cliffordJ, σX, σY, σZ, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;> norm_num

/-- `J³ = -𝟙`; so `J` has order 3 in `PSU(2)` and order 6 in `SU(2)`. -/
theorem cliffordJ_cube : cliffordJ * cliffordJ * cliffordJ = -1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cliffordJ, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;> norm_num

end Clifford

end InfoGeometry.Projective.DahmSpinFanoStructures
