import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic

/-!
# Two-point finite algebraic GNS model

Step 2 of the Isabelle/AFP `Gelfand_Naimark_Segal` reimplementation after the
one-dimensional `ℂ` bounded-operator model.

This file proves the finite pre-Hilbert/GNS algebraic core for the commutative
finite C*-algebra `ℂ²`, represented as `Fin 2 → ℂ`:

* involution is pointwise `star`;
* left action is pointwise multiplication;
* cyclic vector is constantly `1`;
* inner product is the explicit finite sum
  `star x₀*y₀ + star x₁*y₁`;
* cyclicity, representation laws, and the adjoint relation are proved by
  explicit finite algebra.
-/

noncomputable section

namespace GNSFiniteTwoPoint

/-- The two-point finite commutative algebra `ℂ²`. -/
abbrev Two := Fin 2 → ℂ

/-- Cyclic vector `(1,1)`. -/
def omegaVec : Two := fun _ => 1

/-- Pointwise C*-involution. -/
def involution (a : Two) : Two := fun i => star (a i)

/-- Pointwise left multiplication. -/
def mulVec (a x : Two) : Two := fun i => a i * x i

/-- Explicit finite inner product on `ℂ²`, linear in the second argument. -/
def inner2 (x y : Two) : ℂ := star (x 0) * y 0 + star (x 1) * y 1

/-- The vector state induced by the cyclic vector. -/
def omega (a : Two) : ℂ := inner2 omegaVec (mulVec a omegaVec)

@[simp]
theorem mulVec_apply (a x : Two) (i : Fin 2) :
    mulVec a x i = a i * x i := by
  rfl

@[simp]
theorem omegaVec_apply (i : Fin 2) : omegaVec i = 1 := by
  rfl

theorem omegaVec_apply_zero : omegaVec 0 = 1 := by
  rfl

theorem omegaVec_apply_one : omegaVec 1 = 1 := by
  rfl

/-- The cyclic vector coefficient recovers the vector state by definition. -/
theorem vector_state_recovers_omega (a : Two) :
    inner2 omegaVec (mulVec a omegaVec) = omega a := by
  rfl

/-- Cyclicity: every vector is `a Ω` for `a = x`. -/
theorem cyclic_witness (x : Two) :
    ∃ a : Two, mulVec a omegaVec = x := by
  refine ⟨x, ?_⟩
  funext i
  simp [mulVec, omegaVec]

/-- Left multiplication preserves addition. -/
theorem rep_add (a b x : Two) :
    mulVec (a + b) x = mulVec a x + mulVec b x := by
  funext i
  simp [mulVec]
  ring

/-- Left multiplication sends algebra multiplication to composition. -/
theorem rep_mul (a b x : Two) :
    mulVec (mulVec a b) x = mulVec a (mulVec b x) := by
  funext i
  simp [mulVec]
  ring

/-- The algebra unit acts as identity. -/
theorem rep_one (x : Two) :
    mulVec 1 x = x := by
  funext i
  simp [mulVec]

/-- The pointwise involution reverses products. -/
theorem involution_mul (a b : Two) :
    involution (mulVec a b) = mulVec (involution b) (involution a) := by
  funext i
  simp [involution, mulVec]
  ring

/-- Algebraic adjoint relation for the GNS left action. -/
theorem adjoint_relation (a x y : Two) :
    inner2 (mulVec a x) y = inner2 x (mulVec (involution a) y) := by
  simp [inner2, mulVec, involution]
  ring

end GNSFiniteTwoPoint
