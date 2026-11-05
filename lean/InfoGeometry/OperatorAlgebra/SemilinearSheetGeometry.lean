/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.MatrixTraceGeometry
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Semilinear exchange of two full matrix sectors

Entrywise complex conjugation followed by simultaneous sheet exchange is a
native real algebra equivalence. It preserves multiplication order, unlike
the adjoint. All four blocks remain arbitrary complex matrices.

Odd-observable cancellation requires an invariant state and an odd
observable. Hermiticity makes the trace pairing real; symmetry alone does
not assert vanishing energy. The generator identities distinguish even
Hamiltonians from odd Hamiltonians and assert no existence theorem for a
differential equation or physical completion.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SemilinearSheetGeometry

open Matrix
open scoped ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev SheetMatrix (n : Type*) := Matrix (n ⊕ n) (n ⊕ n) ℂ

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugation of coefficients and simultaneous exchange of both matrix indices. -/
def sheetConj : SheetMatrix n ≃ₐ[ℝ] SheetMatrix n :=
  Complex.conjAe.mapMatrix.trans
    (Matrix.reindexAlgEquiv ℝ ℂ (Equiv.sumComm n n))

@[simp] theorem sheetConj_apply (X : SheetMatrix n) (i j : n ⊕ n) :
    sheetConj X i j = star (X (Sum.swap i) (Sum.swap j)) := rfl

theorem sheetConj_eq_submatrix (X : SheetMatrix n) :
    sheetConj X = (X.map (starRingEnd ℂ)).submatrix Sum.swap Sum.swap := rfl

/-- This is a conjugate-semilinear action over the complex coefficient field. -/
theorem sheetConj_smul (z : ℂ) (X : SheetMatrix n) :
    sheetConj (z • X) = star z • sheetConj X := by
  ext i j
  simp [sheetConj_apply, star_mul, mul_comm]

@[simp] theorem sheetConj_involutive (X : SheetMatrix n) :
    sheetConj (sheetConj X) = X := by
  ext i j
  simp only [sheetConj_apply, Sum.swap_swap, star_star]

/-- Operator products retain their original order. -/
theorem sheetConj_mul (X Y : SheetMatrix n) :
    sheetConj (X * Y) = sheetConj X * sheetConj Y :=
  map_mul sheetConj X Y

/-- The semilinear automorphism commutes with the native matrix adjoint. -/
theorem sheetConj_star (X : SheetMatrix n) :
    sheetConj (star X) = star (sheetConj X) := by
  ext i j
  rfl

theorem sheetConj_lie (X Y : SheetMatrix n) :
    sheetConj ⁅X, Y⁆ = ⁅sheetConj X, sheetConj Y⁆ := by
  simp only [Ring.lie_def, map_sub, map_mul]

/-- The concrete exchange matrix has full identity blocks. -/
def sheetSwap : SheetMatrix n := Matrix.fromBlocks 0 1 1 0

theorem sheetSwap_sq : (sheetSwap : SheetMatrix n) * sheetSwap = 1 := by
  simp [sheetSwap, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

omit [Fintype n] in
theorem sheetSwap_star : star (sheetSwap : SheetMatrix n) = sheetSwap := by
  change (Matrix.fromBlocks 0 1 1 0 : SheetMatrix n)ᴴ = _
  simp [sheetSwap, Matrix.fromBlocks_conjTranspose]

/-- The entire four-block action, with no scalar or commutativity restriction. -/
theorem sheetConj_fromBlocks (A B C D : Matrix n n ℂ) :
    sheetConj (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (D.map (starRingEnd ℂ)) (C.map (starRingEnd ℂ))
        (B.map (starRingEnd ℂ)) (A.map (starRingEnd ℂ)) := by
  rw [sheetConj_eq_submatrix, Matrix.fromBlocks_map,
    Matrix.fromBlocks_submatrix_sum_swap_sum_swap]

/-- The native equivalence agrees with conjugation by the concrete sheet swap
after coefficient conjugation; the middle operation is not an adjoint. -/
theorem sheetConj_eq_swap_conj (X : SheetMatrix n) :
    sheetConj X = sheetSwap * X.map (starRingEnd ℂ) * sheetSwap := by
  rw [← Matrix.fromBlocks_toBlocks X]
  simp only [sheetConj_fromBlocks, Matrix.fromBlocks_map, sheetSwap,
    Matrix.fromBlocks_multiply, zero_mul, mul_zero, one_mul, mul_one,
    zero_add, add_zero]

/-- Sheet exchange preserves trace and coefficient conjugation conjugates it. -/
theorem trace_sheetConj (X : SheetMatrix n) :
    Matrix.trace (sheetConj X) = star (Matrix.trace X) := by
  rw [sheetConj_eq_swap_conj, Matrix.trace_mul_cycle, sheetSwap_sq, one_mul]
  exact (AddMonoidHom.map_trace (starRingEnd ℂ) X).symm

theorem sheetConj_isHermitian {X : SheetMatrix n} (hX : X.IsHermitian) :
    (sheetConj X).IsHermitian := by
  change star (sheetConj X) = sheetConj X
  rw [← sheetConj_star, hX.star_eq]

/-- Positivity uses the native matrix cone and requires no chosen matrix norm. -/
theorem sheetConj_posSemidef {X : SheetMatrix n} (hX : X.PosSemidef) :
    (sheetConj X).PosSemidef := by
  have hmap : X.map (starRingEnd ℂ) = Xᵀ := by
    ext i j
    exact hX.isHermitian.apply j i
  rw [sheetConj_eq_submatrix, hmap]
  exact hX.transpose.submatrix Sum.swap

theorem sheetConj_posSemidef_iff (X : SheetMatrix n) :
    (sheetConj X).PosSemidef ↔ X.PosSemidef := by
  constructor
  · intro h
    simpa only [sheetConj_involutive] using sheetConj_posSemidef h
  · exact sheetConj_posSemidef

/-- The Hilbert--Schmidt trace pairing is conjugated by this semilinear symmetry. -/
theorem trace_star_sheetConj (X Y : SheetMatrix n) :
    Matrix.trace (star (sheetConj X) * sheetConj Y) =
      star (Matrix.trace (star X * Y)) := by
  rw [← sheetConj_star, ← sheetConj_mul, trace_sheetConj]

omit [Fintype n] [DecidableEq n] in
private theorem map_conj_twice (A : Matrix n n ℂ) :
    (A.map (starRingEnd ℂ)).map (starRingEnd ℂ) = A := by
  ext i j
  exact star_star _

omit [Fintype n] [DecidableEq n] in
private theorem conjTranspose_map_conj (B : Matrix n n ℂ) :
    Bᴴ.map (starRingEnd ℂ) = Bᵀ := by
  ext i j
  exact star_star _

omit [Fintype n] [DecidableEq n] in
theorem coupledBlock_isHermitian_iff (A B D : Matrix n n ℂ) :
    (Matrix.fromBlocks A B Bᴴ D).IsHermitian ↔
      A.IsHermitian ∧ D.IsHermitian := by
  simp [Matrix.isHermitian_fromBlocks_iff]

/-- Even coupled operators have conjugate diagonal blocks and symmetric coupling.
The symmetry is matrix transpose, not a commutation hypothesis on the blocks. -/
theorem sheetConj_coupledBlock_even_iff (A B D : Matrix n n ℂ) :
    sheetConj (Matrix.fromBlocks A B Bᴴ D) = Matrix.fromBlocks A B Bᴴ D ↔
      D = A.map (starRingEnd ℂ) ∧ Bᵀ = B := by
  rw [sheetConj_fromBlocks, Matrix.fromBlocks_inj, conjTranspose_map_conj]
  constructor
  · intro h
    exact ⟨h.2.2.2.symm, h.2.1⟩
  · rintro ⟨hD, hB⟩
    refine ⟨?_, hB, ?_, hD.symm⟩
    · rw [hD, map_conj_twice]
    · change B.map (starRingEnd ℂ) = Bᵀ.map (starRingEnd ℂ)
      rw [hB]

/-- Odd coupled operators have opposite conjugate diagonal blocks and
skew-symmetric coupling; this is a different constraint from evenness. -/
theorem sheetConj_coupledBlock_odd_iff (A B D : Matrix n n ℂ) :
    sheetConj (Matrix.fromBlocks A B Bᴴ D) = -Matrix.fromBlocks A B Bᴴ D ↔
      D = -A.map (starRingEnd ℂ) ∧ Bᵀ = -B := by
  rw [sheetConj_fromBlocks, Matrix.fromBlocks_neg, Matrix.fromBlocks_inj,
    conjTranspose_map_conj]
  constructor
  · intro h
    refine ⟨?_, h.2.1⟩
    simpa only [neg_neg] using congrArg Neg.neg h.2.2.2.symm
  · rintro ⟨hD, hB⟩
    refine ⟨?_, hB, ?_, ?_⟩
    · rw [hD]
      ext i j
      simp
    · change B.map (starRingEnd ℂ) = -(Bᵀ.map (starRingEnd ℂ))
      rw [hB]
      ext i j
      simp
    · rw [hD, neg_neg]

omit [DecidableEq n] in
/-- The trace of a product of Hermitian matrices is real even when they do not commute. -/
theorem star_trace_mul_of_isHermitian {ρ A : SheetMatrix n}
    (hρ : ρ.IsHermitian) (hA : A.IsHermitian) :
    star (Matrix.trace (ρ * A)) = Matrix.trace (ρ * A) := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hρ.eq]
  exact Matrix.trace_mul_comm A ρ

/-- Invariance and oddness make the complex trace pairing anti-real.
Without Hermiticity, this conclusion alone does not force that trace to vanish. -/
theorem star_trace_mul_of_even_odd {ρ A : SheetMatrix n}
    (hρ : sheetConj ρ = ρ) (hA : sheetConj A = -A) :
    star (Matrix.trace (ρ * A)) = -Matrix.trace (ρ * A) := by
  rw [← trace_sheetConj, sheetConj_mul, hρ, hA, mul_neg, Matrix.trace_neg]

/-- Exact cancellation in an invariant Hermitian density and an odd Hermitian
observable. Positivity or trace normalization may be added by consumers. -/
theorem trace_mul_eq_zero_of_even_odd {ρ A : SheetMatrix n}
    (hρ : ρ.IsHermitian) (hA : A.IsHermitian)
    (hρeven : sheetConj ρ = ρ) (hAodd : sheetConj A = -A) :
    Matrix.trace (ρ * A) = 0 := by
  apply CharZero.eq_neg_self_iff.mp
  exact (star_trace_mul_of_isHermitian hρ hA).symm.trans
    (star_trace_mul_of_even_odd hρeven hAodd)

/-- The ordered inner generator uses the existing native associative Lie bracket. -/
def liouvillian (H X : SheetMatrix n) : SheetMatrix n :=
  -Complex.I • ⁅H, X⁆

theorem liouvillian_eq_ordered (H X : SheetMatrix n) :
    liouvillian H X = -Complex.I • (H * X - X * H) := rfl

/-- The cyclic trace annihilates the full inner generator. -/
theorem trace_liouvillian (H X : SheetMatrix n) :
    Matrix.trace (liouvillian H X) = 0 := by
  rw [liouvillian, Matrix.trace_smul,
    MatrixTraceGeometry.trace_lie_zero, smul_zero]

theorem liouvillian_isHermitian {H X : SheetMatrix n}
    (hH : H.IsHermitian) (hX : X.IsHermitian) :
    (liouvillian H X).IsHermitian := by
  change star (-Complex.I • ⁅H, X⁆) = -Complex.I • ⁅H, X⁆
  rw [star_smul, MatrixOperatorIdentities.star_lie_of_isSelfAdjoint
    hH.isSelfAdjoint hX.isSelfAdjoint]
  simp only [star_neg, Complex.star_def, Complex.conj_I, neg_neg, smul_neg, neg_smul]

/-- Conjugating the imaginary coefficient reverses the generator sign. -/
theorem sheetConj_liouvillian (H X : SheetMatrix n) :
    sheetConj (liouvillian H X) = -liouvillian (sheetConj H) (sheetConj X) := by
  unfold liouvillian
  rw [sheetConj_smul, sheetConj_lie]
  simp only [star_neg, Complex.star_def, Complex.conj_I, neg_neg, neg_smul]

/-- Even Hamiltonians give the algebraic sign required by time reversal. -/
theorem sheetConj_liouvillian_of_even {H : SheetMatrix n}
    (hH : sheetConj H = H) (X : SheetMatrix n) :
    sheetConj (liouvillian H X) = -liouvillian H (sheetConj X) := by
  rw [sheetConj_liouvillian, hH]

/-- Odd Hamiltonians instead commute with the semilinear generator action. -/
theorem sheetConj_liouvillian_of_odd {H : SheetMatrix n}
    (hH : sheetConj H = -H) (X : SheetMatrix n) :
    sheetConj (liouvillian H X) = liouvillian H (sheetConj X) := by
  rw [sheetConj_liouvillian, hH]
  simp only [liouvillian, neg_lie, smul_neg, neg_neg]

end InfoGeometry.OperatorAlgebra.SemilinearSheetGeometry
