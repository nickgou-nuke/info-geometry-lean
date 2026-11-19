/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.WeightedAdjointCompatibility
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Real Krein parity and ordered trace kernels

A symmetric involution `η` supplies an actual conjugation parity on the full
real matrix algebra. Its Krein adjoint is the existing weighted adjoint at the
unit whose value and inverse are both `η`; no second adjoint is introduced.

The two-weight trace identities are pointwise algebraic identities. Reciprocity
does not require the weights to commute with `η`. Simultaneous parity invariance
and mixed-parity orthogonality do require this commutation. No positivity is
asserted for arbitrary weights. Strict sign claims below concern the actual
unweighted Hilbert--Schmidt trace and are proved from native matrix positivity.

This file does not construct density powers, a BKM integral, a Hessian, a
matrix logarithm, or a dynamical stability theorem.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealKreinTrace

open Matrix
open InfoGeometry.OperatorAlgebra.WeightedAdjointCompatibility

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The native matrix unit associated with an involution. -/
def symmetryUnit (η : Matrix n n ℝ) (hη : η * η = 1) : (Matrix n n ℝ)ˣ where
  val := η
  inv := η
  val_inv := hη
  inv_val := hη

/-- Conjugation parity acts on full matrices, with their ordinary product. -/
def parity (η A : Matrix n n ℝ) : Matrix n n ℝ := η * A * η

theorem parity_add (η A B : Matrix n n ℝ) :
    parity η (A + B) = parity η A + parity η B := by
  simp only [parity, mul_add, add_mul]

omit [DecidableEq n] in
theorem parity_sub (η A B : Matrix n n ℝ) :
    parity η (A - B) = parity η A - parity η B := by
  simp only [parity, mul_sub, sub_mul]

theorem parity_smul (η A : Matrix n n ℝ) (r : ℝ) :
    parity η (r • A) = r • parity η A := by
  simp only [parity, mul_smul_comm, smul_mul_assoc]

theorem parity_mul (η : Matrix n n ℝ) (hη : η * η = 1)
    (A B : Matrix n n ℝ) :
    parity η (A * B) = parity η A * parity η B := by
  calc
    parity η (A * B) = η * A * (η * η) * B * η := by
      simp only [parity, hη, mul_one, mul_assoc]
    _ = parity η A * parity η B := by
      simp only [parity, mul_assoc]

theorem parity_involutive (η : Matrix n n ℝ) (hη : η * η = 1)
    (A : Matrix n n ℝ) : parity η (parity η A) = A := by
  calc
    parity η (parity η A) = (η * η) * A * (η * η) := by
      simp only [parity, mul_assoc]
    _ = A := by rw [hη, one_mul, mul_one]

omit [DecidableEq n] in
theorem parity_transpose (η : Matrix n n ℝ) (hsym : ηᵀ = η)
    (A : Matrix n n ℝ) : (parity η A)ᵀ = parity η Aᵀ := by
  simp only [parity, transpose_mul, hsym, mul_assoc]

theorem trace_parity (η : Matrix n n ℝ) (hη : η * η = 1)
    (A : Matrix n n ℝ) : trace (parity η A) = trace A := by
  rw [parity, trace_mul_cycle, hη, one_mul]

/-- Evenness is exactly commutation with the actual symmetry matrix. -/
theorem parity_eq_self_iff (η : Matrix n n ℝ) (hη : η * η = 1)
    (A : Matrix n n ℝ) : parity η A = A ↔ Commute η A := by
  constructor
  · intro h
    have hm := congrArg (fun M : Matrix n n ℝ => M * η) h
    change η * A = A * η
    simpa only [parity, mul_assoc, hη, mul_one] using hm
  · intro h
    change η * A * η = A
    rw [h.eq, mul_assoc, hη, mul_one]

/-- Oddness is exactly anticommutation, with the factor order retained. -/
theorem parity_eq_neg_iff (η : Matrix n n ℝ) (hη : η * η = 1)
    (A : Matrix n n ℝ) : parity η A = -A ↔ η * A = -(A * η) := by
  constructor
  · intro h
    have hm := congrArg (fun M : Matrix n n ℝ => M * η) h
    simpa only [parity, mul_assoc, hη, mul_one, neg_mul] using hm
  · intro h
    change η * A * η = -A
    rw [h, neg_mul, mul_assoc, hη, mul_one]

/-- The existing weighted adjoint specializes to the real Krein formula. -/
theorem adjoint_symmetryUnit (η : Matrix n n ℝ) (hη : η * η = 1)
    (A : Matrix n n ℝ) : adjoint (symmetryUnit η hη) A = η * Aᵀ * η := by
  change η * star A * η = η * Aᵀ * η
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

/-- The Krein adjoint is the transpose of the actual conjugation parity. -/
theorem adjoint_eq_transpose_parity (η : Matrix n n ℝ) (hη : η * η = 1)
    (hsym : ηᵀ = η) (A : Matrix n n ℝ) :
    adjoint (symmetryUnit η hη) A = (parity η A)ᵀ := by
  simpa only [parity, transpose_mul, hsym, mul_assoc] using
    adjoint_symmetryUnit η hη A

theorem adjoint_of_even (η : Matrix n n ℝ) (hη : η * η = 1)
    (hsym : ηᵀ = η) (A : Matrix n n ℝ) (hA : parity η A = A) :
    adjoint (symmetryUnit η hη) A = Aᵀ := by
  rw [adjoint_eq_transpose_parity η hη hsym, hA]

theorem adjoint_of_odd (η : Matrix n n ℝ) (hη : η * η = 1)
    (hsym : ηᵀ = η) (A : Matrix n n ℝ) (hA : parity η A = -A) :
    adjoint (symmetryUnit η hη) A = -Aᵀ := by
  rw [adjoint_eq_transpose_parity η hη hsym, hA, transpose_neg]

/-- On the odd sector, Krein skew-adjointness is ordinary transpose symmetry. -/
theorem adjoint_eq_neg_iff_transpose_eq_of_odd
    (η : Matrix n n ℝ) (hη : η * η = 1) (hsym : ηᵀ = η)
    (A : Matrix n n ℝ) (hA : parity η A = -A) :
    adjoint (symmetryUnit η hη) A = -A ↔ Aᵀ = A := by
  rw [adjoint_of_odd η hη hsym A hA, neg_inj]

/-- On the odd sector, Krein self-adjointness is ordinary transpose skew-symmetry. -/
theorem adjoint_eq_self_iff_transpose_eq_neg_of_odd
    (η : Matrix n n ℝ) (hη : η * η = 1) (hsym : ηᵀ = η)
    (A : Matrix n n ℝ) (hA : parity η A = -A) :
    adjoint (symmetryUnit η hη) A = A ↔ Aᵀ = -A := by
  rw [adjoint_of_odd η hη hsym A hA]
  constructor
  · intro h
    simpa using congrArg (fun M : Matrix n n ℝ => -M) h
  · intro h
    simpa using congrArg (fun M : Matrix n n ℝ => -M) h

/-- The square of an odd Krein-skew matrix is a genuine positive-semidefinite matrix. -/
theorem square_posSemidef_of_odd_adjoint_eq_neg
    (η : Matrix n n ℝ) (hη : η * η = 1) (hsym : ηᵀ = η)
    (A : Matrix n n ℝ) (hA : parity η A = -A)
    (hskew : adjoint (symmetryUnit η hη) A = -A) :
    (A * A).PosSemidef := by
  have hT := (adjoint_eq_neg_iff_transpose_eq_of_odd η hη hsym A hA).mp hskew
  simpa only [conjTranspose_eq_transpose_of_trivial, hT] using
    Matrix.posSemidef_conjTranspose_mul_self A

/-- An odd Krein-self matrix has a negative-semidefinite square, in the native sense. -/
theorem neg_square_posSemidef_of_odd_adjoint_eq_self
    (η : Matrix n n ℝ) (hη : η * η = 1) (hsym : ηᵀ = η)
    (A : Matrix n n ℝ) (hA : parity η A = -A)
    (hself : adjoint (symmetryUnit η hη) A = A) :
    (-(A * A)).PosSemidef := by
  have hT := (adjoint_eq_self_iff_transpose_eq_neg_of_odd η hη hsym A hA).mp hself
  simpa only [conjTranspose_eq_transpose_of_trivial, hT, neg_mul] using
    Matrix.posSemidef_conjTranspose_mul_self A

/-- The two skew-adjoint conditions intersect trivially in the odd sector. -/
theorem eq_zero_of_odd_krein_skew_and_transpose_skew
    (η : Matrix n n ℝ) (hη : η * η = 1) (hsym : ηᵀ = η)
    (A : Matrix n n ℝ) (hA : parity η A = -A)
    (hskew : adjoint (symmetryUnit η hη) A = -A) (hT : Aᵀ = -A) :
    A = 0 := by
  have hsymA := (adjoint_eq_neg_iff_transpose_eq_of_odd η hη hsym A hA).mp hskew
  have hneg : A = -A := hsymA.symm.trans hT
  ext i j
  have hij := congrArg (fun M : Matrix n n ℝ => M i j) hneg
  change A i j = -(A i j) at hij
  change A i j = 0
  linarith

/-- The positive parity projection on the matrix vector space. -/
def evenPart (η A : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (A + parity η A)

/-- The negative parity projection on the matrix vector space. -/
def oddPart (η A : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (A - parity η A)

omit [DecidableEq n] in
theorem evenPart_add_oddPart (η A : Matrix n n ℝ) :
    evenPart η A + oddPart η A = A := by
  dsimp [evenPart, oddPart]
  module

omit [DecidableEq n] in
theorem parity_eq_evenPart_sub_oddPart (η A : Matrix n n ℝ) :
    parity η A = evenPart η A - oddPart η A := by
  dsimp [evenPart, oddPart]
  module

theorem parity_evenPart (η : Matrix n n ℝ) (hη : η * η = 1)
    (A : Matrix n n ℝ) : parity η (evenPart η A) = evenPart η A := by
  simp only [evenPart, parity_smul, parity_add, parity_involutive η hη]
  congr 1
  exact add_comm _ _

theorem parity_oddPart (η : Matrix n n ℝ) (hη : η * η = 1)
    (A : Matrix n n ℝ) : parity η (oddPart η A) = -oddPart η A := by
  simp only [oddPart, parity_smul, parity_sub, parity_involutive η hη]
  rw [← smul_neg, neg_sub]

/-- Any decomposition into the actual parity eigenspaces has this even part. -/
theorem evenPart_unique (η : Matrix n n ℝ) (A X Y : Matrix n n ℝ)
    (hX : parity η X = X) (hY : parity η Y = -Y) (hA : X + Y = A) :
    evenPart η A = X := by
  rw [evenPart, ← hA, parity_add, hX, hY]
  module

/-- The odd component is determined by the same eigenspace decomposition. -/
theorem oddPart_unique (η : Matrix n n ℝ) (A X Y : Matrix n n ℝ)
    (hX : parity η X = X) (hY : parity η Y = -Y) (hA : X + Y = A) :
    oddPart η A = Y := by
  rw [oddPart, ← hA, parity_add, hX, hY]
  module

/-- An ordered two-weight transpose kernel; arbitrary weights need not be positive. -/
def transposeWeightedTrace (L R A B : Matrix n n ℝ) : ℝ :=
  trace (L * Aᵀ * R * B)

/-- The same ordered kernel using the existing weighted Krein adjoint. -/
def kreinWeightedTrace (η : Matrix n n ℝ) (hη : η * η = 1)
    (L R A B : Matrix n n ℝ) : ℝ :=
  trace (L * adjoint (symmetryUnit η hη) A * R * B)

theorem transposeWeightedTrace_add_right (L R A B C : Matrix n n ℝ) :
    transposeWeightedTrace L R A (B + C) =
      transposeWeightedTrace L R A B + transposeWeightedTrace L R A C := by
  simp only [transposeWeightedTrace, mul_add, trace_add]

omit [DecidableEq n] in
theorem transposeWeightedTrace_sub_left (L R A B C : Matrix n n ℝ) :
    transposeWeightedTrace L R (A - B) C =
      transposeWeightedTrace L R A C - transposeWeightedTrace L R B C := by
  simp only [transposeWeightedTrace, transpose_sub, mul_sub, sub_mul, trace_sub]

omit [DecidableEq n] in
theorem transposeWeightedTrace_neg_left (L R A B : Matrix n n ℝ) :
    transposeWeightedTrace L R (-A) B = -transposeWeightedTrace L R A B := by
  simp only [transposeWeightedTrace, transpose_neg, mul_neg, neg_mul, trace_neg]

omit [DecidableEq n] in
theorem transposeWeightedTrace_neg_right (L R A B : Matrix n n ℝ) :
    transposeWeightedTrace L R A (-B) = -transposeWeightedTrace L R A B := by
  simp only [transposeWeightedTrace, mul_neg, trace_neg]

/-- Pointwise reciprocity needs no commutation or positivity condition on either weight. -/
theorem kreinWeightedTrace_eq_transposeWeightedTrace
    (η : Matrix n n ℝ) (hη : η * η = 1) (hsym : ηᵀ = η)
    (L R A B : Matrix n n ℝ) :
    kreinWeightedTrace η hη L R A B =
      transposeWeightedTrace L R (parity η A) B := by
  simp only [kreinWeightedTrace, transposeWeightedTrace,
    adjoint_eq_transpose_parity η hη hsym]

/-- Applying parity again recovers the transpose kernel with arbitrary weights. -/
theorem transposeWeightedTrace_eq_kreinWeightedTrace
    (η : Matrix n n ℝ) (hη : η * η = 1) (hsym : ηᵀ = η)
    (L R A B : Matrix n n ℝ) :
    transposeWeightedTrace L R A B =
      kreinWeightedTrace η hη L R (parity η A) B := by
  rw [kreinWeightedTrace_eq_transposeWeightedTrace η hη hsym,
    parity_involutive η hη]

/-- Commuting weights, rather than reciprocity alone, give simultaneous parity invariance. -/
theorem transposeWeightedTrace_parity
    (η : Matrix n n ℝ) (hη : η * η = 1) (hsym : ηᵀ = η)
    (L R : Matrix n n ℝ) (hL : Commute η L) (hR : Commute η R)
    (A B : Matrix n n ℝ) :
    transposeWeightedTrace L R (parity η A) (parity η B) =
      transposeWeightedTrace L R A B := by
  have hLp : parity η L = L := (parity_eq_self_iff η hη L).mpr hL
  have hRp : parity η R = R := (parity_eq_self_iff η hη R).mpr hR
  unfold transposeWeightedTrace
  calc
    trace (L * (parity η A)ᵀ * R * parity η B) =
        trace (parity η (L * Aᵀ * R * B)) := by
      simp only [parity_mul η hη, parity_transpose η hsym, hLp, hRp]
    _ = trace (L * Aᵀ * R * B) := trace_parity η hη _

theorem transposeWeightedTrace_even_odd_zero
    (η : Matrix n n ℝ) (hη : η * η = 1) (hsym : ηᵀ = η)
    (L R : Matrix n n ℝ) (hL : Commute η L) (hR : Commute η R)
    (X Y : Matrix n n ℝ) (hX : parity η X = X) (hY : parity η Y = -Y) :
    transposeWeightedTrace L R X Y = 0 := by
  have hinv := transposeWeightedTrace_parity η hη hsym L R hL hR X Y
  rw [hX, hY, transposeWeightedTrace_neg_right] at hinv
  exact eq_zero_of_neg_eq hinv

/-- The reverse ordering also vanishes; symmetry of the weights is unnecessary. -/
theorem transposeWeightedTrace_odd_even_zero
    (η : Matrix n n ℝ) (hη : η * η = 1) (hsym : ηᵀ = η)
    (L R : Matrix n n ℝ) (hL : Commute η L) (hR : Commute η R)
    (X Y : Matrix n n ℝ) (hX : parity η X = -X) (hY : parity η Y = Y) :
    transposeWeightedTrace L R X Y = 0 := by
  have hinv := transposeWeightedTrace_parity η hη hsym L R hL hR X Y
  rw [hX, hY, transposeWeightedTrace_neg_left] at hinv
  exact eq_zero_of_neg_eq hinv

/-- The signed quadratic decomposition follows from actual parity orthogonality. -/
theorem kreinWeightedTrace_self_split
    (η : Matrix n n ℝ) (hη : η * η = 1) (hsym : ηᵀ = η)
    (L R : Matrix n n ℝ) (hL : Commute η L) (hR : Commute η R)
    (A : Matrix n n ℝ) :
    kreinWeightedTrace η hη L R A A =
      transposeWeightedTrace L R (evenPart η A) (evenPart η A) -
        transposeWeightedTrace L R (oddPart η A) (oddPart η A) := by
  have hEO := transposeWeightedTrace_even_odd_zero η hη hsym L R hL hR
    (evenPart η A) (oddPart η A) (parity_evenPart η hη A) (parity_oddPart η hη A)
  have hOE := transposeWeightedTrace_odd_even_zero η hη hsym L R hL hR
    (oddPart η A) (evenPart η A) (parity_oddPart η hη A) (parity_evenPart η hη A)
  calc
    kreinWeightedTrace η hη L R A A = transposeWeightedTrace L R (parity η A) A :=
      kreinWeightedTrace_eq_transposeWeightedTrace η hη hsym L R A A
    _ = transposeWeightedTrace L R
        (evenPart η A - oddPart η A) (evenPart η A + oddPart η A) := by
      rw [← parity_eq_evenPart_sub_oddPart η A, evenPart_add_oddPart η A]
    _ = _ := by
      rw [transposeWeightedTrace_sub_left, transposeWeightedTrace_add_right,
        transposeWeightedTrace_add_right, hEO, hOE, add_zero, zero_add]

omit [DecidableEq n] in
/-- The ordinary matrix Gram trace is nonnegative over the reals. -/
theorem trace_transpose_mul_self_nonneg (A : Matrix n n ℝ) :
    0 ≤ trace (Aᵀ * A) := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg

omit [DecidableEq n] in
/-- The actual Gram trace vanishes exactly at the zero matrix. -/
theorem trace_transpose_mul_self_eq_zero_iff (A : Matrix n n ℝ) :
    trace (Aᵀ * A) = 0 ↔ A = 0 := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    (Matrix.trace_conjTranspose_mul_self_eq_zero_iff (A := A))

omit [DecidableEq n] in
theorem trace_transpose_mul_self_pos (A : Matrix n n ℝ) (hA : A ≠ 0) :
    0 < trace (Aᵀ * A) := by
  have hnonneg := trace_transpose_mul_self_nonneg A
  have hne : trace (Aᵀ * A) ≠ 0 := by
    intro hzero
    exact hA ((trace_transpose_mul_self_eq_zero_iff A).mp hzero)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- The unweighted Krein quadratic form is the difference of two genuine Gram traces. -/
theorem trace_adjoint_mul_self_split
    (η : Matrix n n ℝ) (hη : η * η = 1) (hsym : ηᵀ = η)
    (A : Matrix n n ℝ) :
    trace (adjoint (symmetryUnit η hη) A * A) =
      trace ((evenPart η A)ᵀ * evenPart η A) -
        trace ((oddPart η A)ᵀ * oddPart η A) := by
  have hone : Commute η (1 : Matrix n n ℝ) := by
    change η * 1 = 1 * η
    rw [mul_one, one_mul]
  simpa only [kreinWeightedTrace, transposeWeightedTrace, one_mul, mul_one] using
    kreinWeightedTrace_self_split η hη hsym 1 1 hone hone A

/-- Every nonzero even matrix has positive unweighted Krein quadratic trace. -/
theorem trace_adjoint_mul_self_pos_of_even
    (η : Matrix n n ℝ) (hη : η * η = 1) (hsym : ηᵀ = η)
    (A : Matrix n n ℝ) (hparity : parity η A = A) (hA : A ≠ 0) :
    0 < trace (adjoint (symmetryUnit η hη) A * A) := by
  rw [adjoint_of_even η hη hsym A hparity]
  exact trace_transpose_mul_self_pos A hA

/-- Every nonzero odd matrix has strictly negative unweighted Krein quadratic trace. -/
theorem trace_adjoint_mul_self_neg_of_odd
    (η : Matrix n n ℝ) (hη : η * η = 1) (hsym : ηᵀ = η)
    (A : Matrix n n ℝ) (hparity : parity η A = -A) (hA : A ≠ 0) :
    trace (adjoint (symmetryUnit η hη) A * A) < 0 := by
  rw [adjoint_of_odd η hη hsym A hparity, neg_mul, trace_neg]
  have hpos := trace_transpose_mul_self_pos A hA
  linarith

end InfoGeometry.OperatorAlgebra.RealKreinTrace
