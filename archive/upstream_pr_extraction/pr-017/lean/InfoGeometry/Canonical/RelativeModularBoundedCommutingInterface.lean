import InfoGeometry.Canonical.RelativeModularCommutingLift
import InfoGeometry.Canonical.MultiplicativeToAdditiveBridge
import InfoGeometry.Meta.Architecture

open scoped BigOperators

/-!
# Relative Modular Bounded Commuting Interface

Strict finite/bounded interface for the commuting positive lane:
`log(AB) = log A + log B` is exposed only with explicit positivity hypotheses.

This file does not claim unbounded/type-III functional calculus.
-/

namespace InfoGeometry.Canonical.RelativeModularBoundedCommutingInterface

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Canonical.RelativeModularCommutingLift
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal

section Finite

variable {n : ℕ} [Nonempty (Fin n)]

/-- Diagonal entries of finite relative modular operators are strictly positive. -/
@[rep_depth operator]
theorem relativeModularOperator_diag_pos
    (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    0 < relativeModularOperator (n := n) q q0 i i := by
  rw [relativeModularOperator_diag_eq_exp_relativeLogDensity]
  exact Real.exp_pos _

omit [Nonempty (Fin n)] in
/-- General bounded diagonal-positive `log(AB)=log A + log B` at a fixed diagonal coordinate. -/
@[rep_depth operator]
theorem log_mul_diag_of_diag_positive
    (A B : FinMat n)
    (hA : ∃ a : Fin n → ℝ, A = diagMatrix a ∧ ∀ i, 0 < a i)
    (hB : ∃ b : Fin n → ℝ, B = diagMatrix b ∧ ∀ i, 0 < b i)
    (i : Fin n) :
    Real.log ((A * B) i i) = Real.log (A i i) + Real.log (B i i) := by
  rcases hA with ⟨a, rfl, haPos⟩
  rcases hB with ⟨b, rfl, hbPos⟩
  have ha0 : a i ≠ 0 := (haPos i).ne'
  have hb0 : b i ≠ 0 := (hbPos i).ne'
  simp [diagMatrix, Real.log_mul, ha0, hb0]

/--
Concrete bounded commuting-positive `log` linearization for finite relative
modular operators.
-/
@[rep_depth operator]
theorem log_mul_relativeModularOperator_diag
    (q q0 r r0 : PositiveRay (Fin n)) (i : Fin n) :
    Real.log
        (((relativeModularOperator (n := n) q q0)
            * (relativeModularOperator (n := n) r r0)) i i)
      = Real.log (relativeModularOperator (n := n) q q0 i i)
          + Real.log (relativeModularOperator (n := n) r r0 i i) := by
  refine log_mul_diag_of_diag_positive (n := n)
    (A := relativeModularOperator (n := n) q q0)
    (B := relativeModularOperator (n := n) r r0) ?_ ?_ i
  · refine ⟨fun j => relativeDensity (α := Fin n) q q0 j, ?_, ?_⟩
    · rfl
    · intro j
      change 0 < relativeDensity (α := Fin n) q q0 j
      rw [relativeDensity_eq_exp_relativeLogDensity]
      exact Real.exp_pos _
  · refine ⟨fun j => relativeDensity (α := Fin n) r r0 j, ?_, ?_⟩
    · rfl
    · intro j
      change 0 < relativeDensity (α := Fin n) r r0 j
      rw [relativeDensity_eq_exp_relativeLogDensity]
      exact Real.exp_pos _

/--
Same `log`-linearization statement, with explicit commuting hypothesis.
In the finite diagonal lane the commute hypothesis is satisfied canonically.
-/
@[rep_depth operator, capstone]
theorem log_mul_relativeModularOperator_diag_of_commute
    (q q0 r r0 : PositiveRay (Fin n))
    (hcomm : Commute (relativeModularOperator (n := n) q q0)
      (relativeModularOperator (n := n) r r0))
    (i : Fin n) :
    Real.log
        (((relativeModularOperator (n := n) q q0)
            * (relativeModularOperator (n := n) r r0)) i i)
      = Real.log (relativeModularOperator (n := n) q q0 i i)
          + Real.log (relativeModularOperator (n := n) r r0 i i) := by
  have _hcommEq :
      (relativeModularOperator (n := n) q q0)
          * (relativeModularOperator (n := n) r r0)
        = (relativeModularOperator (n := n) r r0)
            * (relativeModularOperator (n := n) q q0) := hcomm.eq
  exact log_mul_relativeModularOperator_diag (n := n) q q0 r r0 i

/--
Canonical commuting witness for finite relative modular operators, exposed here
for bounded-interface clients.
-/
@[rep_depth operator]
theorem relativeModularOperator_commuting_witness
    (q q0 r r0 : PositiveRay (Fin n)) :
    Commute (relativeModularOperator (n := n) q q0)
      (relativeModularOperator (n := n) r r0) :=
  relativeModularOperator_commute (n := n) q q0 r r0

end Finite

end InfoGeometry.Canonical.RelativeModularBoundedCommutingInterface
