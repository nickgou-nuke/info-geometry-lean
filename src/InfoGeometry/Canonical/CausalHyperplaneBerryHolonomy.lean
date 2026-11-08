/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-!
# Sum/difference transport across a Peirce throat

The results here are finite associative-ring identities. A pair of diagonal
Peirce connections acts on the two feet of an off-diagonal throat, giving an
exact commutator/anticommutator crossover. The final section records the
additional involution hypotheses needed for a commuting pair of adjoint
actions. No analytic connection, positivity, or topological quotient is
inferred from these identities.
-/

namespace InfoGeometry.Canonical.CausalHyperplaneBerryHolonomy

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The diagonal connection on the positive Peirce sheet. -/
def sheetPlusConnection (P Ω : B) : B := P * Ω * P

/-- The diagonal connection on the complementary Peirce sheet. -/
def sheetMinusConnection (P Ω : B) : B := (1 - P) * Ω * (1 - P)

/-- Sum of the two diagonal sheet connections. -/
def connectionSum (P Ω : B) : B :=
  sheetPlusConnection P Ω + sheetMinusConnection P Ω

/-- Difference of the two diagonal sheet connections. -/
def connectionDifference (P Ω : B) : B :=
  sheetPlusConnection P Ω - sheetMinusConnection P Ω

/-- The four sum/difference transport identities on the two Peirce throat
directions. The independent seeds `Ω`, `A`, and `C` are retained: a
connection and a throat are not identified without an explicit hypothesis. -/
theorem peirce_sum_difference_transport_crossover
    (P Ω A C : B) (hP : P * P = P) :
    comm (connectionDifference P Ω) (genPhi P A C) =
        anticomm (connectionSum P Ω) (genJ P A C) ∧
    anticomm (connectionDifference P Ω) (genPhi P A C) =
        comm (connectionSum P Ω) (genJ P A C) ∧
    comm (connectionDifference P Ω) (genJ P A C) =
        anticomm (connectionSum P Ω) (genPhi P A C) ∧
    anticomm (connectionDifference P Ω) (genJ P A C) =
        comm (connectionSum P Ω) (genPhi P A C) := by
  unfold connectionDifference connectionSum sheetPlusConnection sheetMinusConnection
  peirce_nf hP
  all_goals trivial

/-- The endogenous sum of the two Peirce corner products is the metric
operator `V`. -/
theorem endogenous_connection_sum_eq_genV (P A C : B) :
    conePlus P A * coneMinus P C + coneMinus P C * conePlus P A =
      genV P A C := by
  rfl

/-- The endogenous difference of the two Peirce corner products is the spin
operator `Σ`. -/
theorem endogenous_connection_difference_eq_genSig (P A C : B) :
    conePlus P A * coneMinus P C - coneMinus P C * conePlus P A =
      genSig P A C := by
  rfl

/-- Conjugation by an involution is an involutive map on the ring. -/
theorem innerConjugation_involutive (T : B) (hT : T * T = 1) :
    Function.Involutive (fun X : B => T * X * T) := by
  intro X
  simp only
  calc
    T * (T * X * T) * T = (T * T) * X * (T * T) := by noncomm_ring
    _ = X := by rw [hT]; noncomm_ring

/-- If two involutive generators anticommute, their inner conjugation actions
commute. Their scalar sign disappears because it occurs on both sides of the
conjugated element. -/
theorem innerConjugations_commute_of_anticommute
    (S U : B) (hSU : S * U = -(U * S)) (X : B) :
    S * (U * X * U) * S = U * (S * X * S) * U := by
  calc
    S * (U * X * U) * S = (S * U) * X * (U * S) := by noncomm_ring
    _ = U * (S * X * S) * U := by
      have hRight : U * (S * X * S) * U = -((U * S) * X * (U * S)) := by
        calc
          U * (S * X * S) * U = (U * S) * X * (S * U) := by noncomm_ring
          _ = (U * S) * X * (-(U * S)) := by rw [hSU]
          _ = -((U * S) * X * (U * S)) := by noncomm_ring
      rw [hSU, hRight]
      simp

/-- Conditional algebraic Klein-four action: the two involutive inner
conjugations commute, so their composite is again involutive. This theorem
does not identify the action with any particular topological quotient. -/
theorem innerConjugation_v4_relations
    (S U : B) (hS : S * S = 1) (hU : U * U = 1)
    (hSU : S * U = -(U * S)) :
    (∀ X : B, S * (S * X * S) * S = X) ∧
    (∀ X : B, U * (U * X * U) * U = X) ∧
    (∀ X : B, S * (U * X * U) * S = U * (S * X * S) * U) ∧
    (∀ X : B, (S * U) * ((S * U) * X * (U * S)) * (U * S) = X) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X
    exact innerConjugation_involutive S hS X
  · intro X
    exact innerConjugation_involutive U hU X
  · intro X
    exact innerConjugations_commute_of_anticommute S U hSU X
  · intro X
    have hSUSU : (S * U) * (S * U) = -1 := by
      calc
        (S * U) * (S * U) = S * (U * S) * U := by noncomm_ring
        _ = S * (-(S * U)) * U := by rw [show U * S = -(S * U) by rw [hSU]; simp]
        _ = -((S * S) * (U * U)) := by noncomm_ring
        _ = -1 := by rw [hS, hU]; simp
    have hUSUS : (U * S) * (U * S) = -1 := by
      calc
        (U * S) * (U * S) = U * (S * U) * S := by noncomm_ring
        _ = U * (-(U * S)) * S := by rw [hSU]
        _ = -((U * U) * (S * S)) := by noncomm_ring
        _ = -1 := by rw [hU, hS]; simp
    calc
      (S * U) * ((S * U) * X * (U * S)) * (U * S) =
          ((S * U) * (S * U)) * X * ((U * S) * (U * S)) := by noncomm_ring
      _ = (-1) * X * (-1) := by rw [hSUSU, hUSUS]
      _ = X := by simp

end InfoGeometry.Canonical.CausalHyperplaneBerryHolonomy
