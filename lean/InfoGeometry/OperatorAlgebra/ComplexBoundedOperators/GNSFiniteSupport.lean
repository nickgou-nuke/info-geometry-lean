import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite-support GNS quotient model

This is the next step in the Lean reimplementation of the AFP
`Gelfand_Naimark_Segal` construction.

For the finite commutative algebra `Fin n → ℂ`, choose an active support
predicate `p`.  The state only sees active coordinates.  The concrete GNS
space is represented as functions on the subtype `{i : Fin n // p i}`.  Thus
algebra elements that differ off support become the same GNS vector, matching
AFP's zero-inner/null-space quotient step in this finite model.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupport

open scoped BigOperators

variable {n : ℕ} (p : Fin n → Prop) [DecidablePred p]

/-- Finite ambient algebra. -/
abbrev Alg (n : ℕ) := Fin n → ℂ

/-- Active support subtype seen by the state. -/
abbrev Active := {i : Fin n // p i}

/-- Concrete GNS quotient space: functions on the active support. -/
abbrev GNS := Active p → ℂ

/-- Cyclic vector, constantly one on the support. -/
def omegaVec : GNS p := fun _ => 1

/-- Quotient/restriction map from ambient algebra to GNS vectors. -/
def restrict (a : Alg n) : GNS p := fun i => a i.1

/-- Left multiplication action on the GNS representative space. -/
def liftMul (a : Alg n) (x : GNS p) : GNS p := fun i => a i.1 * x i

/-- Pointwise involution. -/
def involution (a : Alg n) : Alg n := fun i => star (a i)

/-- Explicit finite inner product on the active support. -/
def innerGNS (x y : GNS p) : ℂ := ∑ i : Active p, star (x i) * y i

/-- Real squared-norm sum used to characterize the null space. -/
def normInnerGNS (x : GNS p) : ℝ := ∑ i : Active p, ‖x i‖ ^ 2

/-- State obtained by summing active coordinates. -/
def omega (a : Alg n) : ℂ := ∑ i : Active p, a i.1

/-- Null subspace: algebra elements vanishing on the active support. -/
def nullSubspace (a : Alg n) : Prop := ∀ i : Active p, a i.1 = 0

@[simp]
theorem restrict_apply (a : Alg n) (i : Active p) :
    restrict p a i = a i.1 := by
  rfl

@[simp]
theorem liftMul_apply (a : Alg n) (x : GNS p) (i : Active p) :
    liftMul p a x i = a i.1 * x i := by
  rfl

/-- Vector-state recovery on the active support. -/
theorem vector_state_recovers_omega (a : Alg n) :
    innerGNS p (omegaVec p) (restrict p a) = omega p a := by
  unfold innerGNS omega omegaVec restrict
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- Cyclicity: every GNS vector is the restriction of an ambient algebra element. -/
theorem cyclic_witness (x : GNS p) :
    ∃ a : Alg n, restrict p a = x := by
  let a : Alg n := fun i => if h : p i then x ⟨i, h⟩ else 0
  refine ⟨a, ?_⟩
  funext i
  simp [restrict, a, i.2]

/-- Equality in the GNS quotient is exactly nullity of the difference. -/
theorem same_gns_iff_null_difference (a b : Alg n) :
    restrict p a = restrict p b ↔ nullSubspace p (a - b) := by
  constructor
  · intro h i
    have hi := congrFun h i
    simp [restrict] at hi
    exact sub_eq_zero.mpr hi
  · intro h
    funext i
    have hi := h i
    simp [restrict]
    exact sub_eq_zero.mp hi

/-- The lifted representation preserves addition. -/
theorem rep_add (a b : Alg n) (x : GNS p) :
    liftMul p (a + b) x = liftMul p a x + liftMul p b x := by
  funext i
  simp [liftMul]
  ring

/-- The lifted representation sends multiplication to composition. -/
theorem rep_mul (a b : Alg n) (x : GNS p) :
    liftMul p (fun i => a i * b i) x = liftMul p a (liftMul p b x) := by
  funext i
  simp [liftMul]
  ring

/-- The algebra unit acts as identity. -/
theorem rep_one (x : GNS p) :
    liftMul p 1 x = x := by
  funext i
  simp [liftMul]

/-- Algebraic adjoint relation for active-support left multiplication. -/
theorem adjoint_relation (a : Alg n) (x y : GNS p) :
    innerGNS p (liftMul p a x) y = innerGNS p x (liftMul p (involution a) y) := by
  unfold innerGNS
  apply Finset.sum_congr rfl
  intro i _
  simp [liftMul, involution]
  ring

/-- Nullity is equivalent to zero squared norm on the active support. -/
theorem null_iff_norm_inner_zero (a : Alg n) :
    nullSubspace p a ↔ normInnerGNS p (restrict p a) = 0 := by
  constructor
  · intro h
    unfold normInnerGNS restrict
    apply Finset.sum_eq_zero
    intro i _
    simp [h i]
  · intro h i
    have hterm : ‖restrict p a i‖ ^ 2 = (0 : ℝ) := by
      have hiff := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun i : Active p => ‖restrict p a i‖ ^ 2)
        (fun j _ => sq_nonneg (‖restrict p a j‖))).mp h
      exact hiff i (Finset.mem_univ i)
    have hnorm : ‖a i.1‖ = 0 := by
      have hsqrt : ‖restrict p a i‖ = 0 := sq_eq_zero_iff.mp hterm
      simpa [restrict] using hsqrt
    exact norm_eq_zero.mp hnorm

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.GNSFiniteSupport
