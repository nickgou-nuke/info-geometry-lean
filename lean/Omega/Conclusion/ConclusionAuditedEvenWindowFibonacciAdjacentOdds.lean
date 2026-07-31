import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The four audited even windows. -/
def conclusion_audited_even_window_fibonacci_adjacent_odds_window : Fin 4 → ℕ
  | 0 => 6
  | 1 => 8
  | 2 => 10
  | 3 => 12

/-- `M_m = |\mathcal S_{m,d_{\min}(m)}|`. -/
def conclusion_audited_even_window_fibonacci_adjacent_odds_min_sector_count
    (i : Fin 4) : ℕ :=
  Nat.fib (conclusion_audited_even_window_fibonacci_adjacent_odds_window i)

/-- `L_m = D_{2m-2}`. -/
def conclusion_audited_even_window_fibonacci_adjacent_odds_adjacent_fiber_count
    (i : Fin 4) : ℕ :=
  Nat.fib (conclusion_audited_even_window_fibonacci_adjacent_odds_window i + 1)

/-- `|X_m|`. -/
def conclusion_audited_even_window_fibonacci_adjacent_odds_ambient_count
    (i : Fin 4) : ℕ :=
  Nat.fib (conclusion_audited_even_window_fibonacci_adjacent_odds_window i + 2)

/-- The audited sequence of adjacent odd ratios listed in the paper. -/
def conclusion_audited_even_window_fibonacci_adjacent_odds_audited_ratio
    (i : Fin 4) : ℚ :=
  (Nat.fib (i.1 + 7) : ℚ) / Nat.fib (i.1 + 6)

/-- Paper-facing Fibonacci identifications and adjacent-odds ratios on the audited even windows. -/
def conclusion_audited_even_window_fibonacci_adjacent_odds_statement
    (i : Fin 4) : Prop :=
  let m := conclusion_audited_even_window_fibonacci_adjacent_odds_window i
  let M := conclusion_audited_even_window_fibonacci_adjacent_odds_min_sector_count i
  let L := conclusion_audited_even_window_fibonacci_adjacent_odds_adjacent_fiber_count i
  let X := conclusion_audited_even_window_fibonacci_adjacent_odds_ambient_count i
  (M, L, X) = (Nat.fib m, Nat.fib (m + 1), Nat.fib (m + 2)) ∧
    ((L : ℚ) / M = (Nat.fib (m + 1) : ℚ) / Nat.fib m) ∧
    ((M : ℚ) / X = (Nat.fib m : ℚ) / Nat.fib (m + 2)) ∧
    ((L : ℚ) / X = (Nat.fib (m + 1) : ℚ) / Nat.fib (m + 2)) ∧
    (i = 0 →
      conclusion_audited_even_window_fibonacci_adjacent_odds_audited_ratio i = (13 : ℚ) / 8) ∧
    (i = 1 →
      conclusion_audited_even_window_fibonacci_adjacent_odds_audited_ratio i = (21 : ℚ) / 13) ∧
    (i = 2 →
      conclusion_audited_even_window_fibonacci_adjacent_odds_audited_ratio i = (34 : ℚ) / 21) ∧
    (i = 3 →
      conclusion_audited_even_window_fibonacci_adjacent_odds_audited_ratio i = (55 : ℚ) / 34)

/-- Paper label: `thm:conclusion-audited-even-window-fibonacci-adjacent-odds`. -/
theorem paper_conclusion_audited_even_window_fibonacci_adjacent_odds
    (i : Fin 4) :
    conclusion_audited_even_window_fibonacci_adjacent_odds_statement i := by
  fin_cases i
  · change conclusion_audited_even_window_fibonacci_adjacent_odds_statement 0
    have hf6 : Nat.fib 6 = 8 := by decide
    have hf7 : Nat.fib 7 = 13 := by decide
    have hf8 : Nat.fib 8 = 21 := by decide
    simp [conclusion_audited_even_window_fibonacci_adjacent_odds_statement,
      conclusion_audited_even_window_fibonacci_adjacent_odds_window,
      conclusion_audited_even_window_fibonacci_adjacent_odds_min_sector_count,
      conclusion_audited_even_window_fibonacci_adjacent_odds_adjacent_fiber_count,
      conclusion_audited_even_window_fibonacci_adjacent_odds_ambient_count,
      conclusion_audited_even_window_fibonacci_adjacent_odds_audited_ratio, hf6, hf7, hf8]
  · change conclusion_audited_even_window_fibonacci_adjacent_odds_statement 1
    have hf7 : Nat.fib 7 = 13 := by decide
    have hf8 : Nat.fib 8 = 21 := by decide
    have hf9 : Nat.fib 9 = 34 := by decide
    have hf10 : Nat.fib 10 = 55 := by decide
    simp [conclusion_audited_even_window_fibonacci_adjacent_odds_statement,
      conclusion_audited_even_window_fibonacci_adjacent_odds_window,
      conclusion_audited_even_window_fibonacci_adjacent_odds_min_sector_count,
      conclusion_audited_even_window_fibonacci_adjacent_odds_adjacent_fiber_count,
      conclusion_audited_even_window_fibonacci_adjacent_odds_ambient_count,
      conclusion_audited_even_window_fibonacci_adjacent_odds_audited_ratio, hf7, hf8, hf9, hf10]
  · change conclusion_audited_even_window_fibonacci_adjacent_odds_statement 2
    have hf8 : Nat.fib 8 = 21 := by decide
    have hf9 : Nat.fib 9 = 34 := by decide
    have hf10 : Nat.fib 10 = 55 := by decide
    have hf11 : Nat.fib 11 = 89 := by decide
    have hf12 : Nat.fib 12 = 144 := by decide
    simp [conclusion_audited_even_window_fibonacci_adjacent_odds_statement,
      conclusion_audited_even_window_fibonacci_adjacent_odds_window,
      conclusion_audited_even_window_fibonacci_adjacent_odds_min_sector_count,
      conclusion_audited_even_window_fibonacci_adjacent_odds_adjacent_fiber_count,
      conclusion_audited_even_window_fibonacci_adjacent_odds_ambient_count,
      conclusion_audited_even_window_fibonacci_adjacent_odds_audited_ratio, hf8, hf9, hf10, hf11,
      hf12]
  · change conclusion_audited_even_window_fibonacci_adjacent_odds_statement 3
    have hf9 : Nat.fib 9 = 34 := by decide
    have hf10 : Nat.fib 10 = 55 := by decide
    have hf12 : Nat.fib 12 = 144 := by decide
    have hf13 : Nat.fib 13 = 233 := by decide
    have hf14 : Nat.fib 14 = 377 := by decide
    simp [conclusion_audited_even_window_fibonacci_adjacent_odds_statement,
      conclusion_audited_even_window_fibonacci_adjacent_odds_window,
      conclusion_audited_even_window_fibonacci_adjacent_odds_min_sector_count,
      conclusion_audited_even_window_fibonacci_adjacent_odds_adjacent_fiber_count,
      conclusion_audited_even_window_fibonacci_adjacent_odds_ambient_count,
      conclusion_audited_even_window_fibonacci_adjacent_odds_audited_ratio, hf9, hf10, hf12, hf13,
      hf14]

end Omega.Conclusion
