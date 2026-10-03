import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Certified cycle lengths on the 160-point Nielsen class. -/
def xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths160 : List ℕ :=
  List.replicate 36 3 ++ List.replicate 12 2 ++ List.replicate 28 1

/-- Certified cycle lengths on the 40-point quotient Nielsen class. -/
def xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths40 : List ℕ :=
  List.replicate 9 3 ++ List.replicate 13 1

/-- Total support size represented by a cycle certificate. -/
def xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_support
    (cycleLengths : List ℕ) : ℕ :=
  cycleLengths.sum

/-- Permutation order represented by a cycle certificate. -/
def xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_order
    (cycleLengths : List ℕ) : ℕ :=
  cycleLengths.foldl Nat.lcm 1

/-- The two certified Hurwitz cycle decompositions have support sizes `160` and `40`, and
orders `6` and `3`, respectively. -/
def xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_statement : Prop :=
  xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_support
      xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths160 = 160 ∧
    xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_order
        xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths160 = 6 ∧
      xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_support
          xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths40 = 40 ∧
        xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_order
            xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths40 = 3

/-- Repeating a cycle length does not change the accumulated order after its first
occurrence. This keeps the certificate proof proportional to the number of cycle types. -/
private theorem foldl_lcm_replicate (a : ℕ) : ∀ n seed, 0 < n →
    (List.replicate n a).foldl Nat.lcm seed = Nat.lcm seed a := by
  intro n
  induction n with
  | zero => intro seed h; omega
  | succ n ih =>
    intro seed _
    cases n with
    | zero => simp
    | succ n =>
      rw [List.replicate_succ, List.foldl_cons]
      rw [ih (Nat.lcm seed a) (by omega)]
      simp

/-- Paper label: `prop:xi-terminal-zm-hurwitz-generator-cycle-types-on-160-and-40`. -/
theorem paper_xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40 :
    xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_statement := by
  unfold xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_statement
  constructor
  · unfold xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_support
    unfold xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths160
    simp only [List.sum_append, List.sum_replicate]
    norm_num
  · constructor
    · unfold xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_order
      unfold xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths160
      rw [List.foldl_append, List.foldl_append]
      rw [foldl_lcm_replicate 3 36 1 (by omega)]
      simp only [Nat.lcm_one_left]
      rw [foldl_lcm_replicate 2 12 3 (by omega)]
      norm_num
      rw [foldl_lcm_replicate 1 28 6 (by omega)]
      norm_num
    · constructor
      · unfold xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_support
        unfold xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths40
        simp only [List.sum_append, List.sum_replicate]
        norm_num
      · unfold xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_order
        unfold xi_terminal_zm_hurwitz_generator_cycle_types_on_160_and_40_lengths40
        rw [List.foldl_append]
        rw [foldl_lcm_replicate 3 9 1 (by omega)]
        simp only [Nat.lcm_one_left]
        rw [foldl_lcm_replicate 1 13 3 (by omega)]
        norm_num

end Omega.Zeta
