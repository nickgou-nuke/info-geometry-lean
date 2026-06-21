import Mathlib
import InfoGeometry.Canonical.TensorTowerColimit

/-!
# Tensor Colimit Expectations

Theorem-safe interface for linear functionals and conditional-expectation-style
superoperators on an inductive tensor colimit.

This file does **not** construct a C*-inductive limit, positivity, normality, or
Tomita--Takesaki/GNS data.  Those analytic ingredients are represented as
explicit fields.  The checked content is the algebraic readback discipline: a
compatible finite family may be compared with a supplied global functional, and
a supplied conditional expectation exposes projection, bimodule, unital, and
state-compatibility laws as kernel-checked theorems.
-/

namespace InfoGeometry.Canonical.TensorColimitExpectation

universe u v

variable {R : Type u} [CommSemiring R]
variable {A : ℕ → Type v}
variable [∀ n, Semiring (A n)] [∀ n, Algebra R (A n)]

/-- A compatible family of finite-stage linear functionals. -/
structure CompatibleFunctionalFamily
    (bond : ∀ n : ℕ, A n →ₐ[R] A (n + 1)) where
  omega : ∀ n : ℕ, A n →ₗ[R] R
  compatible : ∀ n (x : A n), omega (n + 1) (bond n x) = omega n x

/--
A supplied algebraic inductive-colimit carrier for a tensor tower.

The carrier and maps are data.  The file intentionally avoids asserting a
C*-completion or universal property unless an owner module supplies it.
-/
structure TensorInductiveLimit
    (bond : ∀ n : ℕ, A n →ₐ[R] A (n + 1)) where
  AInf : Type v
  instSemiring : Semiring AInf
  instAlgebra : Algebra R AInf
  inj : ∀ n : ℕ, A n →ₐ[R] AInf
  inj_compat : ∀ n (x : A n), inj (n + 1) (bond n x) = inj n x

attribute [instance] TensorInductiveLimit.instSemiring TensorInductiveLimit.instAlgebra

namespace TensorInductiveLimit

variable {bond : ∀ n : ℕ, A n →ₐ[R] A (n + 1)}
variable (L : TensorInductiveLimit bond)

/-- The global linear functional supplied on the colimit carrier. -/
abbrev LimitFunctional := L.AInf →ₗ[R] R

/-- The global functional restricts to the finite functional family. -/
def ExtendsFamily (F : CompatibleFunctionalFamily bond)
    (Ω : L.LimitFunctional) : Prop :=
  ∀ n (x : A n), Ω (L.inj n x) = F.omega n x

/-- Readback: a supplied global functional recovers each finite-stage functional. -/
theorem limit_functional_recovers_stage
    (F : CompatibleFunctionalFamily bond)
    (Ω : L.LimitFunctional)
    (hΩ : L.ExtendsFamily F Ω)
    (n : ℕ) (x : A n) :
    Ω (L.inj n x) = F.omega n x :=
  hΩ n x

/-- Existence of an extending global functional implies finite compatibility. -/
theorem extending_limit_functional_implies_compatible
    (F : CompatibleFunctionalFamily bond)
    (Ω : L.LimitFunctional)
    (hΩ : L.ExtendsFamily F Ω) :
    ∀ n (x : A n), F.omega (n + 1) (bond n x) = F.omega n x := by
  intro n x
  rw [← hΩ (n + 1) (bond n x), L.inj_compat n x, hΩ n x]

/--
A conditional-expectation-style superoperator from the colimit carrier onto
stage `n`.

For genuine C*-conditional expectations the fields `positive`, norm-one, and
normality would also be required.  Here we record only the algebraic laws needed
by the finite theorem-safe bridge.
-/
structure ConditionalExpectation (n : ℕ) where
  E : L.AInf →ₗ[R] A n
  projection : ∀ x : A n, E (L.inj n x) = x
  unital : E 1 = 1
  bimodule : ∀ (a b : A n) (x : L.AInf),
    E (L.inj n a * x * L.inj n b) = a * E x * b
  state_compat : ∀ (F : CompatibleFunctionalFamily bond)
    (Ω : L.LimitFunctional), L.ExtendsFamily F Ω →
      ∀ x : L.AInf, Ω x = F.omega n (E x)

namespace ConditionalExpectation

variable {L}
variable {n : ℕ} (CE : ConditionalExpectation L n)

/-- Readback of the projection law. -/
theorem projection_apply (x : A n) :
    CE.E (L.inj n x) = x :=
  CE.projection x

/-- Readback of the unital law. -/
theorem maps_one : CE.E 1 = 1 :=
  CE.unital

/-- Readback of the local bimodule/superoperator law. -/
theorem bimodule_property (a b : A n) (x : L.AInf) :
    CE.E (L.inj n a * x * L.inj n b) = a * CE.E x * b :=
  CE.bimodule a b x

/-- Readback of state compatibility through a local expectation. -/
theorem state_compatibility
    (F : CompatibleFunctionalFamily bond)
    (Ω : L.LimitFunctional)
    (hΩ : L.ExtendsFamily F Ω)
    (x : L.AInf) :
    Ω x = F.omega n (CE.E x) :=
  CE.state_compat F Ω hΩ x

/-- On the embedded finite stage, state compatibility reduces to the finite functional. -/
theorem state_compatibility_on_stage
    (CE : ConditionalExpectation L n)
    (F : CompatibleFunctionalFamily bond)
    (Ω : L.LimitFunctional)
    (hΩ : L.ExtendsFamily F Ω)
    (x : A n) :
    Ω (L.inj n x) = F.omega n x := by
  rw [ConditionalExpectation.state_compat CE F Ω hΩ (L.inj n x), CE.projection x]

end ConditionalExpectation

end TensorInductiveLimit

end InfoGeometry.Canonical.TensorColimitExpectation
