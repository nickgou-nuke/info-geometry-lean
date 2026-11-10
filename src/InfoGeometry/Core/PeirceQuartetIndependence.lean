/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Core.PeirceMatrixRepresentation

/-! # Linear independence of the supported operator quartet

The nonzero hypothesis rules out the zero representation. The restriction on
two is needed for the sum/difference coordinates, not for the faithful matrix
representation itself. No Clifford universal property is asserted here.
All theorems hold over non-commutative coefficient rings `[Ring R]` and division
rings `[DivisionRing R]`.
-/
namespace InfoGeometry.Core.PeirceQuartetIndependence

open Matrix InfoGeometry.Core.DualSeedPeirce InfoGeometry.Core.PeirceRotor
open InfoGeometry.Core.PeirceMatrixRepresentation
open scoped Matrix BigOperators

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem peirceQuartetIndependence_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

section NoncommRing

variable {R A : Type*} [Ring R] [Ring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] {d₀ b₀ : A}

/-- In any noncommutative ring `[Ring R]` acting torsion-freely on `d₀`, the quartet
`(d₀ + b₀, d₀ - b₀, d₀ * b₀ - b₀ * d₀, d₀ * b₀ + b₀ * d₀)` is linearly independent
whenever multiplication by `2` is torsion-free in `R`. -/
theorem ring_quartet_combination_eq_zero_iff (h : IsDualSeedPair d₀ b₀)
    (hd_free : ∀ r : R, r • d₀ = 0 → r = 0)
    (h2_free : ∀ r : R, (2 : R) * r = 0 → r = 0)
    (a b c d : R) :
    a • (d₀ + b₀) + b • (d₀ - b₀) + c • (d₀ * b₀ - b₀ * d₀) +
      d • (d₀ * b₀ + b₀ * d₀) = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro hz
    have hm : (!![c + d, a + b; a - b, d - c] : Matrix (Fin 2) (Fin 2) R) = 0 := by
      apply (ringRepresentation_eq_zero_iff h hd_free _).mp
      change (c + d) • (d₀ * b₀) + (a + b) • d₀ + (a - b) • b₀ +
        (d - c) • (b₀ * d₀) = 0
      calc
        _ = a • (d₀ + b₀) + b • (d₀ - b₀) + c • (d₀ * b₀ - b₀ * d₀) +
            d • (d₀ * b₀ + b₀ * d₀) := by
          simp only [smul_add, smul_sub, add_smul, sub_smul]
          abel
        _ = 0 := hz
    have h00 : c + d = 0 := by simpa using congrArg (fun M => M 0 0) hm
    have h01 : a + b = 0 := by simpa using congrArg (fun M => M 0 1) hm
    have h10 : a - b = 0 := by simpa using congrArg (fun M => M 1 0) hm
    have h11 : d - c = 0 := by simpa using congrArg (fun M => M 1 1) hm
    have ha : (2 : R) * a = 0 := by
      calc
        (2 : R) * a = (a + b) + (a - b) := by rw [two_mul]; abel
        _ = 0 := by rw [h01, h10, add_zero]
    have hb : (2 : R) * b = 0 := by
      calc
        (2 : R) * b = (a + b) - (a - b) := by rw [two_mul]; abel
        _ = 0 := by rw [h01, h10, sub_zero]
    have hc : (2 : R) * c = 0 := by
      calc
        (2 : R) * c = (c + d) - (d - c) := by rw [two_mul]; abel
        _ = 0 := by rw [h00, h11, sub_zero]
    have hd : (2 : R) * d = 0 := by
      calc
        (2 : R) * d = (c + d) + (d - c) := by rw [two_mul]; abel
        _ = 0 := by rw [h00, h11, add_zero]
    exact ⟨h2_free a ha, h2_free b hb, h2_free c hc, h2_free d hd⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp

/-- Linear independence of the supported operator quartet in any `[Module R A]` over a
noncommutative coefficient ring `[Ring R]`. -/
theorem ring_quartet_linearIndependent (h : IsDualSeedPair d₀ b₀)
    (hd_free : ∀ r : R, r • d₀ = 0 → r = 0)
    (h2_free : ∀ r : R, (2 : R) * r = 0 → r = 0) :
    LinearIndependent R (![d₀ + b₀, d₀ - b₀, d₀ * b₀ - b₀ * d₀, d₀ * b₀ + b₀ * d₀] :
      Fin 4 → A) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hz : g 0 = 0 ∧ g 1 = 0 ∧ g 2 = 0 ∧ g 3 = 0 :=
    (ring_quartet_combination_eq_zero_iff h hd_free h2_free _ _ _ _).mp
      (by simpa [Fin.sum_univ_succ, add_assoc] using hg)
  fin_cases i <;> simp_all

end NoncommRing

variable {n R : Type*} [Fintype n] [DecidableEq n] [Field R]
variable {X Y : Matrix n n R}

/-- The quartet is an invertible change of coordinates on the represented matrix algebra. -/
theorem quartet_combination_eq_zero_iff (h : IsDualSeedPair X Y) (hx : X ≠ 0)
    (h2 : (2 : R) ≠ 0) (a b c d : R) :
    a • (X + Y) + b • (X - Y) + c • (X * Y - Y * X) +
      d • (X * Y + Y * X) = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 :=
  ring_quartet_combination_eq_zero_iff h
    (fun _ hr => (smul_eq_zero.mp hr).resolve_right hx)
    (fun _ hr => (mul_eq_zero.mp hr).resolve_left h2)
    a b c d

/-- Native linear independence in the full ambient matrix vector space. -/
theorem quartet_linearIndependent (h : IsDualSeedPair X Y) (hx : X ≠ 0)
    (h2 : (2 : R) ≠ 0) :
    LinearIndependent R (![X + Y, X - Y, X * Y - Y * X, X * Y + Y * X] :
      Fin 4 → Matrix n n R) :=
  ring_quartet_linearIndependent h
    (fun _ hr => (smul_eq_zero.mp hr).resolve_right hx)
    (fun _ hr => (mul_eq_zero.mp hr).resolve_left h2)

end InfoGeometry.Core.PeirceQuartetIndependence
