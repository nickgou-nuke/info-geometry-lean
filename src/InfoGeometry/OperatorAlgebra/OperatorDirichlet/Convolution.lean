/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing

/-!
# Operator-valued Dirichlet convolution: Möbius delta, inversion, von Mangoldt

Let `A` be an arbitrary (non-commutative) ring, e.g. a matrix or operator
ring. Then `ArithmeticFunction A` with Dirichlet convolution is again a
non-commutative ring (`dirichlet_ring_not_commutative` for `2 × 2` integer
matrices). Inside it:

1. the Möbius "delta" `μ ⋆ ζ = ζ ⋆ μ = 1`; this is the unit, i.e. the delta
   function at `n = 1`;
2. `ζ` and `μ` are central, so Möbius inversion works from either side;
3. for an `ℝ`-algebra `A`, multiplying by `log n` is a derivation of the
   non-commutative Dirichlet ring (`logMul_mul`). Its value on `ζ` is
   `Λ ⋆ ζ` (`logMul_zeta`), so `Λ = (logMul ζ) ⋆ μ` (`vonMangoldt_eq`).

The coefficients `μ n`, `Λ n` are scalars. The ring in which the convolution
takes place is non-commutative, and all identities keep the order of factors.
-/

namespace InfoGeometry.OperatorAlgebra.OperatorDirichlet

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-! ### Möbius delta and two-sided inversion -/

section Moebius

variable {A : Type*} [Ring A]

/-- The Möbius delta in the operator-valued Dirichlet ring. -/
theorem moebius_mul_zeta : ((μ : ArithmeticFunction A) * (ζ : ArithmeticFunction A)) = 1 :=
  coe_moebius_mul_coe_zeta

theorem zeta_mul_moebius : ((ζ : ArithmeticFunction A) * (μ : ArithmeticFunction A)) = 1 :=
  coe_zeta_mul_coe_moebius

/-- `ζ` is central in the non-commutative Dirichlet ring. -/
theorem zeta_commute (f : ArithmeticFunction A) : Commute (ζ : ArithmeticFunction A) f := by
  ext n
  rw [coe_zeta_mul_apply, coe_mul_zeta_apply]

/-- `μ` is central in the non-commutative Dirichlet ring. -/
theorem moebius_commute (f : ArithmeticFunction A) : Commute (μ : ArithmeticFunction A) f := by
  have h := (zeta_commute f).symm
  calc (μ : ArithmeticFunction A) * f = μ * (f * (ζ * μ)) := by rw [zeta_mul_moebius, mul_one]
    _ = μ * ((f * ζ) * μ) := by rw [mul_assoc]
    _ = μ * ((ζ * f) * μ) := by rw [h.eq]
    _ = (μ * ζ) * (f * μ) := by noncomm_ring
    _ = f * μ := by rw [moebius_mul_zeta, one_mul]

/-- Möbius inversion (right form): `f = g ⋆ ζ ↔ g = f ⋆ μ`. -/
theorem moebius_inversion_right (f g : ArithmeticFunction A) :
    f = g * ζ ↔ g = f * μ := by
  constructor
  · rintro rfl; rw [mul_assoc, zeta_mul_moebius, mul_one]
  · rintro rfl; rw [mul_assoc, moebius_mul_zeta, mul_one]

/-- Möbius inversion (left form): `f = ζ ⋆ g ↔ g = μ ⋆ f`. -/
theorem moebius_inversion_left (f g : ArithmeticFunction A) :
    f = ζ * g ↔ g = μ * f := by
  constructor
  · rintro rfl; rw [← mul_assoc, moebius_mul_zeta, one_mul]
  · rintro rfl; rw [← mul_assoc, zeta_mul_moebius, one_mul]

end Moebius

/-! ### The Dirichlet ring of a matrix ring is not commutative -/

section NonCommutative

variable {A : Type*} [Ring A]

/-- An operator placed at `n = 1`. -/
def atOne (a : A) : ArithmeticFunction A := ⟨fun n => if n = 1 then a else 0, by simp⟩

@[simp] theorem atOne_apply (a : A) (n : ℕ) : atOne a n = if n = 1 then a else 0 := rfl

theorem atOne_mul_atOne_one (a b : A) : (atOne a * atOne b) 1 = a * b := by
  rw [mul_apply, Nat.divisorsAntidiagonal_one, Finset.sum_singleton]
  simp

/-- Dirichlet convolution of `2 × 2` integer-matrix-valued arithmetic functions is
not commutative. -/
theorem dirichlet_ring_not_commutative :
    ¬ ∀ f g : ArithmeticFunction (Matrix (Fin 2) (Fin 2) ℤ), f * g = g * f := by
  intro h
  have h1 := congrArg (fun F => F 1) (h (atOne !![0, 1; 0, 0]) (atOne !![0, 0; 1, 0]))
  simp only [atOne_mul_atOne_one] at h1
  have h2 := congrFun (congrFun h1 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h2

end NonCommutative

/-! ### von Mangoldt as a logarithmic derivation -/

section Mangoldt

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Scalar arithmetic functions acting in the operator ring. -/
noncomputable def ofReal (f : ArithmeticFunction ℝ) : ArithmeticFunction A :=
  ⟨fun n => algebraMap ℝ A (f n), by simp⟩

@[simp] theorem ofReal_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    ofReal (A := A) f n = algebraMap ℝ A (f n) := rfl

theorem ofReal_mul (f g : ArithmeticFunction ℝ) :
    ofReal (A := A) (f * g) = ofReal f * ofReal g := by
  ext n
  simp [mul_apply, map_sum, map_mul]

theorem ofReal_zeta : ofReal (A := A) (ζ : ArithmeticFunction ℝ) = (ζ : ArithmeticFunction A) := by
  ext n
  by_cases hn : n = 0 <;> simp [hn, natCoe_apply, zeta_apply]

/-- Multiplication by `log n`. -/
noncomputable def logMul (f : ArithmeticFunction A) : ArithmeticFunction A :=
  ⟨fun n => Real.log n • f n, by simp⟩

@[simp] theorem logMul_apply (f : ArithmeticFunction A) (n : ℕ) :
    logMul f n = Real.log n • f n := rfl

/-- `logMul` is a derivation of the non-commutative Dirichlet ring. -/
theorem logMul_mul (f g : ArithmeticFunction A) :
    logMul (f * g) = logMul f * g + f * logMul g := by
  ext n
  simp only [logMul_apply, mul_apply, ArithmeticFunction.add_apply, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hxn, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have h1 : (x.1 : ℝ) ≠ 0 := by
    exact_mod_cast fun h => hn (by rw [← hxn, h, zero_mul])
  have h2 : (x.2 : ℝ) ≠ 0 := by
    exact_mod_cast fun h => hn (by rw [← hxn, h, mul_zero])
  rw [← hxn, Nat.cast_mul, Real.log_mul h1 h2, add_smul, smul_mul_assoc, mul_smul_comm]

theorem logMul_zeta :
    logMul (ζ : ArithmeticFunction A) = ofReal vonMangoldt * (ζ : ArithmeticFunction A) := by
  rw [← ofReal_zeta, ← ofReal_mul, vonMangoldt_mul_zeta]
  ext n
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, natCoe_apply, zeta_apply, log_apply, Algebra.algebraMap_eq_smul_one]

/-- von Mangoldt in the operator Dirichlet ring: `Λ = (log ⋅ ζ) ⋆ μ`. -/
theorem vonMangoldt_eq :
    ofReal (A := A) vonMangoldt = logMul (ζ : ArithmeticFunction A) * μ :=
  (moebius_inversion_right _ _).mp (logMul_zeta (A := A))

/-- Chain rule: the log-derivative of a `ζ`-summatory transform. -/
theorem logMul_mul_zeta (f : ArithmeticFunction A) :
    logMul (f * (ζ : ArithmeticFunction A)) =
      logMul f * (ζ : ArithmeticFunction A) +
        f * (ofReal vonMangoldt * (ζ : ArithmeticFunction A)) := by
  rw [logMul_mul, logMul_zeta]

end Mangoldt

end InfoGeometry.OperatorAlgebra.OperatorDirichlet
