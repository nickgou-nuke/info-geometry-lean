/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceMatrixRepresentation

/-! # Linear independence of the supported operator quartet

The nonzero hypothesis rules out the zero representation. The restriction on
two is needed for the sum/difference coordinates, not for the faithful matrix
representation itself. No Clifford universal property is asserted here.
-/
namespace InfoGeometry.Core.PeirceQuartetIndependence

open Matrix InfoGeometry.Core.DualSeedPeirce InfoGeometry.Core.PeirceRotor
open InfoGeometry.Core.PeirceMatrixRepresentation
open scoped Matrix BigOperators

variable {n R : Type*} [Fintype n] [DecidableEq n] [Field R]
variable {X Y : Matrix n n R}

/-- The quartet is an invertible change of coordinates on the represented matrix algebra. -/
theorem quartet_combination_eq_zero_iff (h : IsDualSeedPair X Y) (hx : X ≠ 0)
    (h2 : (2 : R) ≠ 0) (a b c d : R) :
    a • (X + Y) + b • (X - Y) + c • (X * Y - Y * X) +
      d • (X * Y + Y * X) = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro hz
    have hm : (!![c + d, a + b; a - b, d - c] : Matrix (Fin 2) (Fin 2) R) = 0 := by
      apply (representation_eq_zero_iff h hx _).mp
      change (c + d) • (X * Y) + (a + b) • X + (a - b) • Y +
        (d - c) • (Y * X) = 0
      calc
        _ = a • (X + Y) + b • (X - Y) + c • (X * Y - Y * X) +
            d • (X * Y + Y * X) := by module
        _ = 0 := hz
    have h00 : c + d = 0 := by simpa using congrArg (fun M => M 0 0) hm
    have h01 : a + b = 0 := by simpa using congrArg (fun M => M 0 1) hm
    have h10 : a - b = 0 := by simpa using congrArg (fun M => M 1 0) hm
    have h11 : d - c = 0 := by simpa using congrArg (fun M => M 1 1) hm
    have ha : (2 : R) * a = 0 := by linear_combination h01 + h10
    have hb : (2 : R) * b = 0 := by linear_combination h01 - h10
    have hc : (2 : R) * c = 0 := by linear_combination h00 - h11
    have hd : (2 : R) * d = 0 := by linear_combination h00 + h11
    exact ⟨(mul_eq_zero.mp ha).resolve_left h2, (mul_eq_zero.mp hb).resolve_left h2,
      (mul_eq_zero.mp hc).resolve_left h2, (mul_eq_zero.mp hd).resolve_left h2⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp

/-- Native linear independence in the full ambient matrix vector space. -/
theorem quartet_linearIndependent (h : IsDualSeedPair X Y) (hx : X ≠ 0)
    (h2 : (2 : R) ≠ 0) :
    LinearIndependent R (![X + Y, X - Y, X * Y - Y * X, X * Y + Y * X] :
      Fin 4 → Matrix n n R) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hz : g 0 = 0 ∧ g 1 = 0 ∧ g 2 = 0 ∧ g 3 = 0 :=
    (quartet_combination_eq_zero_iff h hx h2 _ _ _ _).mp
      (by simpa [Fin.sum_univ_succ, add_assoc] using hg)
  fin_cases i <;> simp_all

end InfoGeometry.Core.PeirceQuartetIndependence
