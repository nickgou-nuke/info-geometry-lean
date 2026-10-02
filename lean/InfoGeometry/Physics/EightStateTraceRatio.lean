import Mathlib.Data.Rat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Eight-state weak-isospin/electric-charge trace ratio

This module proves the exact rational trace identity on the finite eight-state
table

  ν, e, u_r, u_g, u_b, d_r, d_g, d_b.

With the conventional assignments

  T₃ = (+1/2,-1/2,+1/2,+1/2,+1/2,-1/2,-1/2,-1/2)

and

  Q = (0,-1,2/3,2/3,2/3,-1/3,-1/3,-1/3),

the finite sums satisfy

  Σ T₃² = 2,
  Σ Q² = 8/3,
  (Σ T₃²)/(Σ Q²) = 3/8.

This is a finite rational identity.  The module does not identify this ratio
with the physical electroweak weak-mixing angle without an additional theorem
relating the finite trace normalization to gauge couplings.
-/

namespace InfoGeometry.Physics.EightStateTraceRatio

inductive State8 where
  | nu
  | electron
  | up : Fin 3 → State8
  | down : Fin 3 → State8

open State8

/-- Weak-isospin third component on the eight-state table. -/
def weakT3 : State8 → ℚ
  | nu => 1 / 2
  | electron => -1 / 2
  | up _ => 1 / 2
  | down _ => -1 / 2

/-- Electric-charge assignment on the eight-state table. -/
def electricQ : State8 → ℚ
  | nu => 0
  | electron => -1
  | up _ => 2 / 3
  | down _ => -1 / 3

/-- Explicit sum over the three colour labels. -/
def sumColor (f : Fin 3 → ℚ) : ℚ :=
  f 0 + f 1 + f 2

/-- Finite trace/readout of T₃². -/
def traceT3Sq : ℚ :=
  weakT3 nu ^ 2 +
  weakT3 electron ^ 2 +
  sumColor (fun c => weakT3 (up c) ^ 2) +
  sumColor (fun c => weakT3 (down c) ^ 2)

/-- Finite trace/readout of Q². -/
def traceQSq : ℚ :=
  electricQ nu ^ 2 +
  electricQ electron ^ 2 +
  sumColor (fun c => electricQ (up c) ^ 2) +
  sumColor (fun c => electricQ (down c) ^ 2)

theorem traceT3Sq_eq_two :
    traceT3Sq = 2 := by
  norm_num [traceT3Sq, sumColor, weakT3]

theorem traceQSq_eq_eight_thirds :
    traceQSq = 8 / 3 := by
  norm_num [traceQSq, sumColor, electricQ]

/-- Exact finite eight-state trace ratio. -/
theorem trace_ratio_eq_three_eighths :
    traceT3Sq / traceQSq = 3 / 8 := by
  rw [traceT3Sq_eq_two, traceQSq_eq_eight_thirds]
  norm_num

/-- A transparent packet exposing the three finite rational identities. -/
theorem eight_state_trace_packet :
    traceT3Sq = 2 ∧
    traceQSq = 8 / 3 ∧
    traceT3Sq / traceQSq = 3 / 8 := by
  exact ⟨traceT3Sq_eq_two, traceQSq_eq_eight_thirds,
    trace_ratio_eq_three_eighths⟩

end InfoGeometry.Physics.EightStateTraceRatio
