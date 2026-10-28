/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CliffordDirac.Defect
import InfoGeometry.Core.AnticommutingSum
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Star.Module

/-!
# Graded charges and their Clifford realization

An odd involution gives a negative-square companion. Multiplication by the
central complex scalar `I` gives a self-adjoint equal-square companion. The
Clifford application constructs the grading and charge from the original data.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CliffordDirac

section Ring

variable {A : Type*} [Ring A]

/-- The existing finite anticommuting-sum theorem specialized to two operators. -/
theorem anticommuting_add_sq (d m : A) (hanti : d * m + m * d = 0) :
    (d + m) * (d + m) = d * d + m * m := by
  have ha : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ∀ j ∈ (Finset.univ : Finset (Fin 2)),
      i ≠ j → (![d, m] i) * (![d, m] j) + (![d, m] j) * (![d, m] i) = 0 := by
    intro i _ j _ hij
    fin_cases i <;> fin_cases j <;> simp_all [add_comm]
  simpa [Fin.sum_univ_two] using
    InfoGeometry.Core.AnticommutingSum.sum_square Finset.univ ![d, m] ha

theorem grading_mul_sq_neg {γ q : A} (hγ : γ * γ = 1)
    (hodd : γ * q + q * γ = 0) : (γ * q) * (γ * q) = -(q * q) := by
  have hswap : q * γ = -(γ * q) := eq_neg_of_add_eq_zero_right hodd
  calc
    _ = γ * (q * γ) * q := by noncomm_ring
    _ = -(γ * γ) * (q * q) := by rw [hswap]; noncomm_ring
    _ = _ := by rw [hγ, neg_one_mul]

theorem odd_companion_anticommute {γ q : A} (hodd : γ * q + q * γ = 0) :
    q * (γ * q) + (γ * q) * q = 0 := by
  have hswap : q * γ = -(γ * q) := eq_neg_of_add_eq_zero_right hodd
  rw [← mul_assoc q γ q, hswap]
  noncomm_ring

theorem bivector_mul_clifford_sum {g h : A} (hg : g * g = 1) (hh : h * h = 1)
    (hanti : g * h + h * g = 0) (x y : A) :
    (g * h) * (g * x + h * y) = -(h * x - g * y) := by
  have hswap : h * g = -(g * h) := eq_neg_of_add_eq_zero_right hanti
  calc
    _ = g * (h * g) * x + g * (h * h) * y := by noncomm_ring
    _ = -(g * g) * (h * x) + g * (h * h) * y := by rw [hswap]; noncomm_ring
    _ = _ := by rw [hg, hh]; noncomm_ring

theorem clifford_sum_mul_bivector {g h x y : A}
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0)
    (cgx : Commute g x) (cgy : Commute g y)
    (chx : Commute h x) (chy : Commute h y) :
    (g * x + h * y) * (g * h) = h * x - g * y := by
  have hswap : h * g = -(g * h) := eq_neg_of_add_eq_zero_right hanti
  have cx : x * (g * h) = (g * h) * x := ((cgx.mul_left chx).symm).eq
  have cy : y * (g * h) = (g * h) * y := ((cgy.mul_left chy).symm).eq
  calc
    _ = g * (x * (g * h)) + h * (y * (g * h)) := by noncomm_ring
    _ = (g * g) * (h * x) + (h * g) * h * y := by rw [cx, cy]; noncomm_ring
    _ = (g * g) * (h * x) - g * (h * h) * y := by rw [hswap]; noncomm_ring
    _ = _ := by rw [hg, hh]; noncomm_ring

end Ring

section ComplexAlgebra

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The complex companion of an operator with respect to a grading. -/
def chiralMate (γ q : A) : A := Complex.I • (γ * q)

theorem chiralMate_sq {γ q : A} (hγ : γ * γ = 1)
    (hodd : γ * q + q * γ = 0) :
    chiralMate γ q * chiralMate γ q = q * q := by
  simp only [chiralMate, smul_mul_assoc, mul_smul_comm, smul_smul,
    Complex.I_mul_I, grading_mul_sq_neg hγ hodd, neg_one_smul, neg_neg]

theorem chiralMate_anticommute {γ q : A} (hodd : γ * q + q * γ = 0) :
    q * chiralMate γ q + chiralMate γ q * q = 0 := by
  simp only [chiralMate, mul_smul_comm, smul_mul_assoc, ← smul_add,
    odd_companion_anticommute hodd, smul_zero]

theorem chiralMate_odd {γ q : A} (hodd : γ * q + q * γ = 0) :
    γ * chiralMate γ q + chiralMate γ q * γ = 0 := by
  have hz : γ * (γ * q) + (γ * q) * γ = 0 := by
    calc
      _ = γ * (γ * q + q * γ) := by noncomm_ring
      _ = 0 := by rw [hodd, mul_zero]
  simp only [chiralMate, mul_smul_comm, smul_mul_assoc, ← smul_add, hz, smul_zero]

theorem chiralMate_commute_square {γ q : A} (hγ : γ * γ = 1)
    (hodd : γ * q + q * γ = 0) : Commute (chiralMate γ q) (q * q) := by
  rw [← chiralMate_sq hγ hodd]
  exact (Commute.refl _).mul_right (Commute.refl _)

variable [StarRing A] [StarModule ℂ A]

theorem chiralMate_selfAdjoint {γ q : A}
    (hγ : IsSelfAdjoint γ) (hq : IsSelfAdjoint q)
    (hodd : γ * q + q * γ = 0) : IsSelfAdjoint (chiralMate γ q) := by
  have hswap : q * γ = -(γ * q) := eq_neg_of_add_eq_zero_right hodd
  change star (Complex.I • (γ * q)) = Complex.I • (γ * q)
  simp [star_smul, star_mul, hγ.star_eq, hq.star_eq, hswap]

end ComplexAlgebra

section CliffordGrading

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The grading is constructed from the actual two Clifford generators. -/
def cliffordGrading (g h : A) : A := Complex.I • (g * h)

theorem cliffordGrading_sq {g h : A}
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0) :
    cliffordGrading g h * cliffordGrading g h = 1 := by
  have hs := InfoGeometry.Clifford.LorentzianBivectorSignatureBridge.positive_bivector_sq_neg_one
    hg hh hanti
  simp only [cliffordGrading, smul_mul_assoc, mul_smul_comm, smul_smul,
    Complex.I_mul_I, hs, neg_one_smul, neg_neg]

theorem cliffordGrading_odd {g h x y : A}
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0)
    (cgx : Commute g x) (cgy : Commute g y)
    (chx : Commute h x) (chy : Commute h y) :
    cliffordGrading g h * (g * x + h * y) +
      (g * x + h * y) * cliffordGrading g h = 0 := by
  simp only [cliffordGrading, smul_mul_assoc, mul_smul_comm, ← smul_add,
    bivector_mul_clifford_sum hg hh hanti,
    clifford_sum_mul_bivector hg hh hanti cgx cgy chx chy, neg_add_cancel, smul_zero]

theorem chiralMate_clifford_sum {g h : A}
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0) (x y : A) :
    chiralMate (cliffordGrading g h) (g * x + h * y) = h * x - g * y := by
  simp only [chiralMate, cliffordGrading, smul_mul_assoc, smul_smul,
    Complex.I_mul_I, neg_one_smul, bivector_mul_clifford_sum hg hh hanti, neg_neg]

/-- The rotated charge has the same square with noncommuting coefficients allowed. -/
theorem rotated_clifford_sum_sq {g h x y : A}
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0)
    (cgx : Commute g x) (cgy : Commute g y)
    (chx : Commute h x) (chy : Commute h y) :
    (h * x - g * y) * (h * x - g * y) = (g * x + h * y) * (g * x + h * y) := by
  rw [← chiralMate_clifford_sum hg hh hanti x y]
  exact chiralMate_sq (cliffordGrading_sq hg hh hanti)
    (cliffordGrading_odd hg hh hanti cgx cgy chx chy)

theorem rotated_clifford_sum_anticommute {g h x y : A}
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0)
    (cgx : Commute g x) (cgy : Commute g y)
    (chx : Commute h x) (chy : Commute h y) :
    (g * x + h * y) * (h * x - g * y) +
      (h * x - g * y) * (g * x + h * y) = 0 := by
  rw [← chiralMate_clifford_sum hg hh hanti x y]
  exact chiralMate_anticommute (cliffordGrading_odd hg hh hanti cgx cgy chx chy)

variable [StarRing A] [StarModule ℂ A]

theorem cliffordGrading_selfAdjoint {g h : A}
    (hg : IsSelfAdjoint g) (hh : IsSelfAdjoint h) (hanti : g * h + h * g = 0) :
    IsSelfAdjoint (cliffordGrading g h) := by
  have hswap : h * g = -(g * h) := eq_neg_of_add_eq_zero_right hanti
  change star (Complex.I • (g * h)) = Complex.I • (g * h)
  simp [star_smul, star_mul, hg.star_eq, hh.star_eq, hswap]

end CliffordGrading

end InfoGeometry.OperatorAlgebra.CliffordDirac
