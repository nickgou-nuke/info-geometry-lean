import Mathlib
import InfoGeometry.Canonical.SplitCliffordTwoModeCAR
import InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

/-!
# InfoGeometry.Canonical.SplitCliffordJordanWignerTwoMode

Concrete two-mode Jordan-Wigner CAR and finite current table in `M₄(ℝ)`.

This file packages already-constructed concrete matrix lemmas into one owner
surface:

* same-mode CAR for two modes;
* cross-mode anticommutation;
* finite current family on modes `±1`;
* explicit finite commutator table;
* eventual truncation at `atTop`;
* obstruction that `[J₁,J₋₁]` is not the identity.

No wrappers. No placeholders.
-/

namespace InfoGeometry.Canonical.SplitCliffordJordanWignerTwoMode

open Matrix
open Filter
open InfoGeometry.Canonical.SplitCliffordTwoModeCAR
open InfoGeometry.Canonical.SplitCliffordSourceCurrentWick

abbrev M4R : Type := Matrix (Fin 4) (Fin 4) ℝ
abbrev V4R : Type := Matrix (Fin 4) (Fin 1) ℝ

/-- Ordinary associative commutator in `M₄(ℝ)`. -/
def comm4 (X Y : M4R) : M4R := X * Y - Y * X

/-- Two-mode finite current family, concretely from Jordan-Wigner CAR blocks. -/
def Jfin : Int → M4R := sourceJfin

/-- Two-mode diagonal charge commutator readout. -/
def finiteChargeDiag : M4R :=
  !![0,  0, 0, 0;
     0, -1, 0, 0;
     0,  0, 1, 0;
     0,  0, 0, 0]

/-- Same-mode CAR for mode 1. -/
theorem car_mode1 :
    a1 * a1Dag + a1Dag * a1 = (1 : M4R) := by
  simpa using mode1_car_identity

/-- Same-mode CAR for mode 2. -/
theorem car_mode2 :
    a2 * a2Dag + a2Dag * a2 = (1 : M4R) := by
  simpa using mode2_car_identity

/-- Cross-mode annihilators anticommute. -/
theorem car_cross_annihilate :
    a1 * a2 + a2 * a1 = (0 : M4R) := by
  simpa using cross_annihilate_anticommute

/-- Cross-mode creators anticommute. -/
theorem car_cross_create :
    a1Dag * a2Dag + a2Dag * a1Dag = (0 : M4R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a1Dag, a2Dag, Matrix.mul_apply, Fin.sum_univ_four]

/-- Cross-mode annihilation/creation anticommutes. -/
theorem car_cross_annihilate_create :
    a1 * a2Dag + a2Dag * a1 = (0 : M4R) := by
  simpa using cross_mixed_anticommute

/-- Cross-mode creation/annihilation anticommutes. -/
theorem car_cross_create_annihilate :
    a1Dag * a2 + a2 * a1Dag = (0 : M4R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a1Dag, a2, Matrix.mul_apply, Fin.sum_univ_four]

/-- Evaluation at mode `1`. -/
theorem Jfin_eval_one :
    Jfin 1 = a1Dag * a2 := by
  simp [Jfin, sourceJfin]

/-- Evaluation at mode `-1`. -/
theorem Jfin_eval_neg_one :
    Jfin (-1 : Int) = a2Dag * a1 := by
  simp [Jfin, sourceJfin]

/-- Vanishing outside support `±1`. -/
theorem Jfin_eq_zero_of_outside_support
    (n : Int) (h1 : n ≠ 1) (hm1 : n ≠ -1) :
    Jfin n = 0 := by
  simp [Jfin, sourceJfin, h1, hm1]

/-- Explicit finite current commutator `[J₁,J₋₁]`. -/
theorem Jfin_comm_1_neg1_explicit :
    comm4 (Jfin 1) (Jfin (-1 : Int)) = finiteChargeDiag := by
  simpa [comm4, Jfin, finiteChargeDiag]
    using sourceJfin_commutator_one_neg_one

/-- Explicit finite current commutator `[J₋₁,J₁] = -finiteChargeDiag`. -/
theorem Jfin_comm_neg1_1_explicit :
    comm4 (Jfin (-1 : Int)) (Jfin 1) = -finiteChargeDiag := by
  calc
    comm4 (Jfin (-1 : Int)) (Jfin 1)
        = -comm4 (Jfin 1) (Jfin (-1 : Int)) := by
          unfold comm4
          abel
    _ = -finiteChargeDiag := by
          rw [Jfin_comm_1_neg1_explicit]

/-- If either mode is outside support, the commutator vanishes. -/
theorem Jfin_comm_m_n_zero_of_outside_support
    {m n : Int}
    (h :
      (m ≠ 1 ∧ m ≠ (-1 : Int)) ∨
      (n ≠ 1 ∧ n ≠ (-1 : Int))) :
    comm4 (Jfin m) (Jfin n) = 0 := by
  simpa [comm4, Jfin] using sourceJfin_commutator_zero_of_outside_support m n h

/-- Finite current truncation on vectors (`4 × 1` matrices). -/
theorem Jfin_trunc_vector :
    ∀ v : V4R, ∀ᶠ n : Int in atTop, Jfin n * v = 0 := by
  intro v
  refine eventually_atTop.2 ?_
  refine ⟨2, ?_⟩
  intro n hn
  have h1 : n ≠ 1 := by omega
  have hm1 : n ≠ -1 := by omega
  rw [Jfin_eq_zero_of_outside_support n h1 hm1]
  simp

/-- Uniform eventual truncation per matrix entry. -/
theorem Jfin_trunc_uniform_matrix_entry
    (i j : Fin 4) :
    ∀ᶠ n : Int in atTop, (Jfin n) i j = 0 := by
  simpa [Jfin] using sourceJfin_trunc_entry i j

/--
The two-mode finite current is not the scalar Heisenberg central identity.
-/
theorem Jfin_comm_1_neg1_ne_identity :
    comm4 (Jfin 1) (Jfin (-1 : Int)) ≠ (1 : M4R) := by
  intro h
  have h00 := congrArg (fun M : M4R => M 0 0) h
  rw [Jfin_comm_1_neg1_explicit] at h00
  norm_num [finiteChargeDiag] at h00

end InfoGeometry.Canonical.SplitCliffordJordanWignerTwoMode
