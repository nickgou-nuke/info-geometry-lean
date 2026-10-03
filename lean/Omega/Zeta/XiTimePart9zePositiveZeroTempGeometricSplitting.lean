import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The concrete window-6 address set used by the finite shell certificate. -/
abbrev xi_time_part9ze_positive_zero_temp_geometric_splitting_address := Fin 21

/-- The multiplicity-four shell selected by positive zero temperature. -/
def xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell :
    Finset xi_time_part9ze_positive_zero_temp_geometric_splitting_address :=
  Finset.univ.filter fun w => w.val < 9

/-- The four long-root addresses inside the maximal shell. -/
def xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell :
    Finset xi_time_part9ze_positive_zero_temp_geometric_splitting_address :=
  Finset.univ.filter fun w => w.val < 4

/-- The five short-root addresses inside the maximal shell. -/
def xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell :
    Finset xi_time_part9ze_positive_zero_temp_geometric_splitting_address :=
  Finset.univ.filter fun w => 4 ≤ w.val ∧ w.val < 9

/-- Window-6 multiplicities: nine points of weight `4`, four of weight `3`, and eight of `2`. -/
def xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity
    (w : xi_time_part9ze_positive_zero_temp_geometric_splitting_address) : ℕ :=
  if w.val < 9 then 4 else if w.val < 13 then 3 else 2

/-- The positive zero-temperature limiting law, uniform on the multiplicity-four shell. -/
def xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass
    (w : xi_time_part9ze_positive_zero_temp_geometric_splitting_address) : ℚ :=
  if w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell then 1 / 9 else 0

/-- Paper-facing finite certificate for the window-6 positive zero-temperature split. -/
def xi_time_part9ze_positive_zero_temp_geometric_splitting_statement : Prop :=
  xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell.card = 9 ∧
    xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell.card = 4 ∧
    xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell.card = 5 ∧
    Disjoint
      xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell
      xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell ∧
    xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell ∪
        xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell =
      xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell ∧
    (∀ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell,
      xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity w = 4) ∧
    (∀ w, w ∉ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell →
      xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity w < 4) ∧
    (∀ q : ℕ,
      (∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell,
          xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity w ^ q) =
        9 * 4 ^ q) ∧
    (∑ w, xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass w) = 1 ∧
    (∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell,
        xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass w) = 4 / 9 ∧
    (∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell,
        xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass w) = 5 / 9

/-- Paper label: `thm:xi-time-part9ze-positive-zero-temp-geometric-splitting`. -/
theorem paper_xi_time_part9ze_positive_zero_temp_geometric_splitting :
    xi_time_part9ze_positive_zero_temp_geometric_splitting_statement := by
  have hMaxCard :
      xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell.card = 9 := by
    decide
  have hLongCard :
      xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell.card = 4 := by
    decide
  have hShortCard :
      xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell.card = 5 := by
    decide
  have hDisjoint :
      Disjoint
        xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell
        xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell := by
    decide
  have hUnion :
      xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell ∪
          xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell =
        xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell := by
    decide
  have hMaxMultiplicity :
      ∀ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell,
        xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity w = 4 := by
    decide
  have hOffMax :
      ∀ w, w ∉ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell →
        xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity w < 4 := by
    decide
  have hPower :
      ∀ q : ℕ,
        (∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell,
            xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity w ^ q) =
          9 * 4 ^ q := by
    intro q
    calc
      (∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell,
          xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity w ^ q)
          = ∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell,
              4 ^ q := by
            refine Finset.sum_congr rfl ?_
            intro w hw
            rw [hMaxMultiplicity w hw]
      _ = 9 * 4 ^ q := by
            simp [hMaxCard]
  have hTotalMass :
      (∑ w, xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass w) = 1 := by
    calc
      _ = ∑ w,
          if w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell then
            (1 / 9 : ℚ) else 0 := by
        simp only [xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass]
      _ = ∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell,
          (1 / 9 : ℚ) := by rw [Finset.sum_ite_mem_eq]
      _ = (xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell.card : ℚ) *
          (1 / 9 : ℚ) := by simp
      _ = 1 := by rw [hMaxCard]; norm_num
  have hLongMass :
      (∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell,
          xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass w) = 4 / 9 := by
    calc
      _ = ∑ _w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell,
          (1 / 9 : ℚ) := by
        apply Finset.sum_congr rfl
        intro w hw
        have hwval : w.val < 4 := by
          simpa [xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell] using hw
        have hwmax :
            w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell := by
          simp only [xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell,
            Finset.mem_filter, Finset.mem_univ, true_and]
          exact Nat.lt_trans hwval (by norm_num)
        simp [xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass, hwmax]
      _ = (xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell.card : ℚ) *
          (1 / 9 : ℚ) := by simp
      _ = 4 / 9 := by rw [hLongCard]; norm_num
  have hShortMass :
      (∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell,
          xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass w) = 5 / 9 := by
    calc
      _ = ∑ _w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell,
          (1 / 9 : ℚ) := by
        apply Finset.sum_congr rfl
        intro w hw
        have hwval : 4 ≤ w.val ∧ w.val < 9 := by
          simpa [xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell] using hw
        have hwmax :
            w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell := by
          simp only [xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell,
            Finset.mem_filter, Finset.mem_univ, true_and]
          exact hwval.2
        simp [xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass, hwmax]
      _ = (xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell.card : ℚ) *
          (1 / 9 : ℚ) := by simp
      _ = 5 / 9 := by rw [hShortCard]; norm_num
  exact ⟨hMaxCard, hLongCard, hShortCard, hDisjoint, hUnion, hMaxMultiplicity, hOffMax,
    hPower, hTotalMass, hLongMass, hShortMass⟩

end Omega.Zeta
