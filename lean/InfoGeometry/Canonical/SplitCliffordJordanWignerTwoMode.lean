import Mathlib
import InfoGeometry.Canonical.SplitCliffordTwoModeCAR
import InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent

/-!
# InfoGeometry.Canonical.SplitCliffordJordanWignerTwoMode

Concrete two-mode Jordan-Wigner CAR closure step in `M₄(ℝ)`.

This file records the finite two-mode CAR facts and finite current table
without promoting them to a full infinite Heisenberg representation.
-/

namespace InfoGeometry.Canonical.SplitCliffordJordanWignerTwoMode

open Matrix

abbrev M4R : Type := Matrix (Fin 4) (Fin 4) ℝ
abbrev V4R : Type := Matrix (Fin 4) (Fin 1) ℝ

abbrev a1 : M4R := InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1
abbrev a1Dag : M4R := InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag
abbrev a2 : M4R := InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2
abbrev a2Dag : M4R := InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag

abbrev Jpos : M4R := InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jplus
abbrev Jneg : M4R := InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jminus
abbrev Jfin : Int → M4R := InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jfin
abbrev finiteChargeDiag : M4R := InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Hdiag

def comm4 (X Y : M4R) : M4R := X * Y - Y * X

theorem car_mode1 : a1 * a1Dag + a1Dag * a1 = (1 : M4R) := by
  simpa [a1, a1Dag] using InfoGeometry.Canonical.SplitCliffordTwoModeCAR.mode1_car_identity

theorem car_mode2 : a2 * a2Dag + a2Dag * a2 = (1 : M4R) := by
  simpa [a2, a2Dag] using InfoGeometry.Canonical.SplitCliffordTwoModeCAR.mode2_car_identity

theorem car_cross_annihilate : a1 * a2 + a2 * a1 = (0 : M4R) := by
  simpa [a1, a2] using InfoGeometry.Canonical.SplitCliffordTwoModeCAR.cross_annihilate_anticommute

theorem car_cross_annihilate_create : a1 * a2Dag + a2Dag * a1 = (0 : M4R) := by
  simpa [a1, a2Dag] using InfoGeometry.Canonical.SplitCliffordTwoModeCAR.cross_mixed_anticommute

theorem Jfin_eq_zero_iff (n : Int) : Jfin n = 0 ↔ n ≠ 1 ∧ n ≠ -1 := by
  simpa [Jfin] using InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jfin_eq_zero_iff n

theorem Jfin_trunc_vector (v : V4R) :
    ∀ᶠ n : Int in Filter.atTop, Jfin n * v = 0 := by
  simpa [Jfin] using InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jfin_trunc_vector v

theorem Jfin_trunc_uniform_matrix_entry (i j : Fin 4) :
    ∀ᶠ n : Int in Filter.atTop, (Jfin n) i j = 0 := by
  simpa [Jfin] using
    InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jfin_trunc_uniform_matrix_entry i j

theorem Jfin_comm_1_1 : comm4 (Jfin 1) (Jfin 1) = (0 : M4R) := by
  simpa [comm4, Jfin] using InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jfin_comm_1_1

theorem Jfin_comm_neg1_neg1 : comm4 (Jfin (-1)) (Jfin (-1)) = (0 : M4R) := by
  simpa [comm4, Jfin] using InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jfin_comm_neg1_neg1

theorem Jfin_comm_1_neg1_explicit : comm4 (Jfin 1) (Jfin (-1)) = finiteChargeDiag := by
  simpa [comm4, Jfin, finiteChargeDiag] using
    InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jfin_comm_1_neg1_explicit

theorem Jfin_comm_neg1_1_explicit : comm4 (Jfin (-1)) (Jfin 1) = -finiteChargeDiag := by
  simpa [comm4, Jfin, finiteChargeDiag] using
    InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jfin_comm_neg1_1_explicit

theorem Jfin_comm_zero_of_either_outside_support
    {m n : Int}
    (h : (m ≠ 1 ∧ m ≠ -1) ∨ (n ≠ 1 ∧ n ≠ -1)) :
    comm4 (Jfin m) (Jfin n) = (0 : M4R) := by
  simpa [comm4, Jfin] using
    (InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Jfin_comm_m_n_zero_of_outside_support
      (m := m) (n := n) h)

theorem represented_current_commutator_two_mode :
    ∃ J : Int → M4R,
      (∀ v : V4R, ∀ᶠ n : Int in Filter.atTop, J n * v = 0) ∧
      J 1 = Jpos ∧
      J (-1) = Jneg ∧
      comm4 (J 1) (J 1) = 0 ∧
      comm4 (J (-1)) (J (-1)) = 0 ∧
      comm4 (J 1) (J (-1)) = finiteChargeDiag ∧
      comm4 (J (-1)) (J 1) = -finiteChargeDiag ∧
      (∀ {m n : Int},
        ((m ≠ 1 ∧ m ≠ -1) ∨ (n ≠ 1 ∧ n ≠ -1)) →
          comm4 (J m) (J n) = 0) := by
  refine ⟨Jfin, ?_⟩
  refine ⟨?_, rfl, rfl, Jfin_comm_1_1, Jfin_comm_neg1_neg1, Jfin_comm_1_neg1_explicit, Jfin_comm_neg1_1_explicit, ?_⟩
  · intro v
    exact Jfin_trunc_vector v
  · intro m n h
    exact Jfin_comm_zero_of_either_outside_support h

theorem Jfin_comm_1_neg1_ne_identity :
    comm4 (Jfin 1) (Jfin (-1)) ≠ (1 : M4R) := by
  intro h
  have h00 := congrArg (fun M : M4R => M (0 : Fin 4) (0 : Fin 4)) h
  rw [Jfin_comm_1_neg1_explicit] at h00
  have h01 : (0 : ℝ) = 1 := by
    simpa [finiteChargeDiag, InfoGeometry.Canonical.SplitCliffordJordanWignerTwoModeCurrent.Hdiag] using h00
  norm_num at h01

end InfoGeometry.Canonical.SplitCliffordJordanWignerTwoMode
