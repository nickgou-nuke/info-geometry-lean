import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Canonical.ConformalFiveGradeInversion

/-!
# Five-graded Möbius/Witten globality packet

This file builds a **closed conditional bridge** for the five-graded
Möbius/Witten globality layer.

It does **not** prove:
- CCC (Cosmic Censorship Conjecture);
- black-hole unitarity;
- analytic superconformal index theory;
- complete orbit classification;
- global conformal-group equivalence;
- a full physical Witten-index theorem.

The five-grade closure laws are imported from the canonical involutive
grade-swap owner.  Only the independent grade-two evolution law remains data
at the ledger boundary.
-/

namespace InfoGeometry.Canonical.Globality

open InfoGeometry.Canonical.ConformalFiveGradeInversion

/--
A compatibility name for the canonical five-graded conformal inversion owner.

Its source/sink, incoming/outgoing, and center-stability laws are theorems
derived from involutivity and the grade-swap equation; they are not duplicated
as witness fields here.
-/
abbrev ConformalFiveGradeSystem (M : Type*) :=
  FiveGradedConformalInversion M

/--
One-step visible-loss / grade-two-gain ledger.

The burden is placed at the instantiation boundary:
`visibleLoss_eq_gradeTwoGain` is the local conservation witness.
-/
structure GradeTwoInformationLedger (State Info : Type*) where
  visible  : State → ℤ
  gradeTwo : State → ℤ
  evolution : ℝ → State → State

  visibleLoss_eq_gradeTwoGain :
    ∀ (step : ℝ) (s : State),
      visible s - visible (evolution step s) =
        gradeTwo (evolution step s) - gradeTwo s

/-- Recursive state evaluation by iterating the one-step evolution. -/
def stateAt {State Info : Type*}
    (A : GradeTwoInformationLedger State Info)
    (step : ℝ)
    (s : State) : ℕ → State
  | 0 => s
  | n + 1 => A.evolution step (stateAt A step s n)

/--
Recursive visible loss is exactly accumulated as grade-two reservoir gain.
-/
theorem recursive_visibleLoss_eq_gradeTwoGain {State Info : Type*}
    (A : GradeTwoInformationLedger State Info)
    (step : ℝ)
    (s : State)
    (n : ℕ) :
    A.visible s - A.visible (stateAt A step s n) =
      A.gradeTwo (stateAt A step s n) - A.gradeTwo s := by
  induction n with
  | zero =>
      simp [stateAt]
  | succ n ih =>
      simp only [stateAt]
      have hstep :=
        A.visibleLoss_eq_gradeTwoGain step (stateAt A step s n)
      calc
        A.visible s -
            A.visible (A.evolution step (stateAt A step s n))
            =
          (A.visible s - A.visible (stateAt A step s n)) +
          (A.visible (stateAt A step s n) -
            A.visible (A.evolution step (stateAt A step s n))) := by
              ring
        _ =
          (A.gradeTwo (stateAt A step s n) - A.gradeTwo s) +
          (A.gradeTwo (A.evolution step (stateAt A step s n)) -
            A.gradeTwo (stateAt A step s n)) := by
              rw [ih, hstep]
        _ =
          A.gradeTwo (A.evolution step (stateAt A step s n)) -
            A.gradeTwo s := by
              ring

/--
Capstone packet bridge.

This is a **conditional** bridge theorem: it packages five-grade closure,
Möbius trace cancellation, Witten four-layer parity cancellation, and
recursive grade-two compensation.

It does **not** prove:
- CCC;
- complete orbit classification;
- black-hole unitarity;
- analytic zeta/RH claims;
- full physical Witten-index theorem;
- global conformal-group equivalence.
-/
theorem five_graded_mobius_witten_globality_packet
    {M State Info : Type*}
    (G : ConformalFiveGradeSystem M)
    (A : GradeTwoInformationLedger State Info)
    (step : ℝ)
    (s : State)
    (n : ℕ)
    (chi_global_4 moebius_strip_4 : Matrix (Fin 4) (Fin 4) ℚ)
    (witten_parity_factor : ℕ → ℤ)
    (h_chi_global : Matrix.trace chi_global_4 = 0)
    (h_moebius_chiral :
      Matrix.trace (moebius_strip_4 * chi_global_4) = 0)
    (h_witten_parity :
      witten_parity_factor 1 + witten_parity_factor 2 +
      witten_parity_factor 3 + witten_parity_factor 4 = 0) :
    -- 1. Five-grade source/sink closure.
    (∀ x, x ∈ G.sourceSet ↔ G.theta x ∈ G.sinkSet) ∧
    -- 2. Five-grade incoming/outgoing closure.
    (∀ x, x ∈ G.incomingSet ↔ G.theta x ∈ G.outgoingSet) ∧
    -- 3. Zero-grade center stability.
    (∀ x, x ∈ G.centerSet ↔ G.theta x ∈ G.centerSet) ∧
    -- 4. Möbius chiral trace cancellation.
    Matrix.trace chi_global_4 = 0 ∧
    Matrix.trace (moebius_strip_4 * chi_global_4) = 0 ∧
    -- 5. Witten four-layer parity cancellation.
    witten_parity_factor 1 + witten_parity_factor 2 +
      witten_parity_factor 3 + witten_parity_factor 4 = 0 ∧
    -- 6. Recursive compensation.
    (A.visible s - A.visible (stateAt A step s n) =
      A.gradeTwo (stateAt A step s n) - A.gradeTwo s) := by
  exact ⟨
    G.mem_source_iff_mem_sink,
    G.mem_incoming_iff_mem_outgoing,
    G.mem_center_iff_mem_center,
    h_chi_global,
    h_moebius_chiral,
    h_witten_parity,
    recursive_visibleLoss_eq_gradeTwoGain A step s n
  ⟩

end InfoGeometry.Canonical.Globality
