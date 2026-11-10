/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
Lev's Galois Field Quantum Theory (GFQT)
Investigating the modular representations of so(1,4).

This file records only finite algebraic interfaces inspired by Felix M. Lev,
"Why is quantum physics based on complex numbers?", arXiv:hep-th/0309003v2.
It does not formalize Lev's full spinless modular representation theorem.
The certified layer below is the explicit quadratic-pair algebra `a + bI` with
`I² = -1`, together with a concrete `ZMod 3` base-field witness that `-1` is
not already a square.
-/

namespace InfoGeometry.Algebra.LevGFQT

section SO14

variable {K : Type*} [Ring K]

/-- The diagonal metric tensor for so(1,4) signature (+, -, -, -, -) -/
def eta : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.diagonal ![1, -1, -1, -1, -1]

/-- The generators of the so(1,4) Lie algebra represented over K. -/
def M (a b : Fin 5) : Matrix (Fin 5) (Fin 5) K :=
  fun i j => 
    if i = a ∧ j = b then (eta b b : K)
    else if i = b ∧ j = a then -(eta a a : K)
    else 0

end SO14

section GFQT

variable {p : ℕ} [Fact p.Prime]

/-- The GFQT arithmetic condition used by Lev for the finite complex extension lane. -/
def is_p_mod_4_eq_3 : Prop := p % 4 = 3

end GFQT

section QuadraticPair

variable (R : Type*)

/-- Explicit quadratic-pair carrier for the formal finite analogue of `a + bI`. -/
abbrev QuadraticPair := R × R

variable {R}

/-- Addition of quadratic pairs. -/
def qadd [Add R] (z w : QuadraticPair R) : QuadraticPair R :=
  (z.1 + w.1, z.2 + w.2)

/-- Negation of quadratic pairs. -/
def qneg [Neg R] (z : QuadraticPair R) : QuadraticPair R :=
  (-z.1, -z.2)

/-- Multiplication with the relation `I² = -1`. -/
def qmul [Ring R] (z w : QuadraticPair R) : QuadraticPair R :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- The real unit in the quadratic-pair algebra. -/
def qone [Zero R] [One R] : QuadraticPair R :=
  (1, 0)

/-- The formal imaginary unit in the quadratic-pair algebra. -/
def qI [Zero R] [One R] : QuadraticPair R :=
  (0, 1)

/-- Conjugation `a + bI ↦ a - bI`. -/
def qconj [Neg R] (z : QuadraticPair R) : QuadraticPair R :=
  (z.1, -z.2)

/-- Norm readout `a² + b²`, i.e. `(a + bI)(a - bI)` in the pair model. -/
def qnorm [Ring R] (z : QuadraticPair R) : R :=
  z.1 * z.1 + z.2 * z.2

/-- The defining quadratic-pair relation: the formal unit squares to `-1`. -/
theorem qI_sq [Ring R] :
    qmul (qI : QuadraticPair R) qI = qneg (qone : QuadraticPair R) := by
  ext <;> simp [qmul, qI, qneg, qone]

/-- Pair conjugation is involutive. -/
theorem qconj_involutive [InvolutiveNeg R] (z : QuadraticPair R) :
    qconj (qconj z) = z := by
  ext <;> simp [qconj]

/-- Pair conjugation preserves the real unit. -/
theorem qconj_one [Ring R] :
    qconj (qone : QuadraticPair R) = qone := by
  ext <;> simp [qconj, qone]

/-- Pair conjugation sends `I` to `-I`. -/
theorem qconj_I [Ring R] :
    qconj (qI : QuadraticPair R) = qneg qI := by
  ext <;> simp [qconj, qI, qneg]

/-- Over any non-commutative ring `[Ring R]`, pair conjugation preserves the product
`qconj (qmul z w) = qmul (qconj z) (qconj w)`. -/
theorem qconj_mul_ring [Ring R] (z w : QuadraticPair R) :
    qconj (qmul z w) = qmul (qconj z) (qconj w) := by
  ext
  · dsimp [qconj, qmul]
    noncomm_ring
  · dsimp [qconj, qmul]
    noncomm_ring

/-- Over any non-commutative ring `[Ring R]`, multiplying by the conjugate gives the norm
in the real component whenever the two components of `z` commute (`Commute z.1 z.2`). -/
theorem qmul_conj_of_commute [Ring R] (z : QuadraticPair R) (hcomm : Commute z.1 z.2) :
    qmul z (qconj z) = (qnorm z, 0) := by
  ext
  · dsimp [qconj, qmul, qnorm]
    noncomm_ring
  · dsimp [qconj, qmul, qnorm]
    rw [mul_neg, hcomm.eq, neg_add_cancel]

/-- Pair conjugation is multiplicative for the quadratic-pair product. -/
theorem qconj_mul [CommRing R] (z w : QuadraticPair R) :
    qconj (qmul z w) = qmul (qconj z) (qconj w) :=
  qconj_mul_ring z w

/-- Multiplying by the conjugate gives the norm in the real component. -/
theorem qmul_conj [CommRing R] (z : QuadraticPair R) :
    qmul z (qconj z) = (qnorm z, 0) :=
  qmul_conj_of_commute z (Commute.all z.1 z.2)

end QuadraticPair

open InfoGeometry.Algebra.FiniteSpin in
/-- Non-commutativity witness for the finite spin operator carrier. -/
theorem lev_gfqt_spin_carrier_noncomm : J_plus * J_minus ≠ J_minus * J_plus :=
  j_plus_j_minus_ne

section ConcreteBaseFieldWitness

/-- Concrete base-field witness: in `ZMod 3`, the element `-1` is not a square. -/
theorem zmod_three_no_square_minus_one (x : ZMod 3) : x * x ≠ -1 := by
  fin_cases x <;> decide

/-- Concrete arithmetic side condition for the smallest `p ≡ 3 mod 4` example. -/
theorem three_mod_four_eq_three : 3 % 4 = 3 := by
  decide

theorem zmodThreeQuadraticExtensionCertificate :
  Nat.Prime 3 ∧
    3 % 4 = 3 ∧
      (∀ x : ZMod 3, x * x ≠ -1) ∧
        qmul (qI : QuadraticPair (ZMod 3)) qI = qneg (qone : QuadraticPair (ZMod 3)) := by
  exact ⟨by decide, three_mod_four_eq_three,
    zmod_three_no_square_minus_one, qI_sq⟩

end ConcreteBaseFieldWitness

end InfoGeometry.Algebra.LevGFQT
