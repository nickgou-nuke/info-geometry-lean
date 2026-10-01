import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing

import InfoGeometry.Canonical.KahlerAtiyahCartanForms

/-!
# Kähler--Atiyah bivectors and the spin Lie action

This module is the next theorem edge after the Cartan-form Clifford
representation on the exterior algebra.

For a symmetric metric `g`, write `c(v)` for the Kähler--Atiyah action
`ε(v) + ι(g(v,-))`.  The normalized Clifford bivector

`Σ(v,u) = (1/4) [c(v), c(u)]`

acts on generators by the orthogonal Lie algebra formula

`[Σ(v,u), c(w)] = g(u,w)c(v) - g(v,w)c(u)`.

Thus the degree-two Clifford commutators on literal exterior forms realize
the infinitesimal spin/orthogonal action, without introducing a matrix gamma
representation.
-/

noncomputable section

namespace InfoGeometry.Canonical.KahlerAtiyahSpinConnection

open InfoGeometry.Canonical.KahlerAtiyahCartanForms

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- Commutator in the endomorphism algebra of exterior forms. -/
def endCommutator
    (A B : FormEnd V) :
    FormEnd V :=
  A * B - B * A

@[simp] theorem endCommutator_self
    (A : FormEnd V) :
    endCommutator A A = 0 := by
  simp [endCommutator]

theorem endCommutator_skew
    (A B : FormEnd V) :
    endCommutator A B = -endCommutator B A := by
  dsimp [endCommutator]
  abel

/-- Normalized Clifford bivector generator
`Σ(v,u) = 1/4 [c(v),c(u)]`. -/
def spinBivector
    (g : LinearMap.BilinForm ℝ V)
    (v u : V) :
    FormEnd V :=
  (1 / 4 : ℝ) •
    endCommutator
      (cartanCliffordAction g v)
      (cartanCliffordAction g u)

theorem spinBivector_skew
    (g : LinearMap.BilinForm ℝ V)
    (v u : V) :
    spinBivector g v u = -spinBivector g u v := by
  simp only [spinBivector, endCommutator_skew]
  rw [smul_neg]
  rfl

@[simp] theorem spinBivector_self
    (g : LinearMap.BilinForm ℝ V)
    (v : V) :
    spinBivector g v v = 0 := by
  simp [spinBivector]

/--
Unnormalized commutator identity behind the spin action.

For three Clifford generators `A = c(v)`, `B = c(u)`, `C = c(w)`,
the double commutator satisfies

`[[A,B],C] = 4 g(u,w) A - 4 g(v,w) B`.
-/
theorem clifford_double_commutator
    (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (v u w : V) :
    endCommutator
        (endCommutator
          (cartanCliffordAction g v)
          (cartanCliffordAction g u))
        (cartanCliffordAction g w) =
      (4 * g u w) • cartanCliffordAction g v -
        (4 * g v w) • cartanCliffordAction g u := by
  let A : FormEnd V := cartanCliffordAction g v
  let B : FormEnd V := cartanCliffordAction g u
  let C : FormEnd V := cartanCliffordAction g w

  have hBC :
      B * C + C * B =
        (2 * g u w) • (1 : FormEnd V) := by
    dsimp [B, C]
    exact cartanCliffordAction_anticommutator_of_symmetric g hg u w

  have hAC :
      A * C + C * A =
        (2 * g v w) • (1 : FormEnd V) := by
    dsimp [A, C]
    exact cartanCliffordAction_anticommutator_of_symmetric g hg v w

  have hrearrange :
      endCommutator (endCommutator A B) C =
        A * (B * C + C * B) -
          (A * C + C * A) * B -
          B * (A * C + C * A) +
          (B * C + C * B) * A := by
    dsimp [endCommutator]
    noncomm_ring

  rw [hrearrange, hBC, hAC]
  simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  apply LinearMap.ext
  intro α
  simp only [LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply]
  module

/--
The normalized Clifford bivector acts on Cartan generators by the defining
orthogonal Lie algebra representation:

`[Σ(v,u),c(w)] = g(u,w)c(v) - g(v,w)c(u)`.
-/
theorem spinBivector_comm_cartanCliffordAction
    (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (v u w : V) :
    endCommutator
        (spinBivector g v u)
        (cartanCliffordAction g w) =
      (g u w) • cartanCliffordAction g v -
        (g v w) • cartanCliffordAction g u := by
  unfold spinBivector
  unfold endCommutator
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub]
  change
    (1 / 4 : ℝ) •
        endCommutator
          (endCommutator
            (cartanCliffordAction g v)
            (cartanCliffordAction g u))
          (cartanCliffordAction g w) =
      _
  rw [clifford_double_commutator g hg v u w]
  apply LinearMap.ext
  intro α
  simp only [LinearMap.smul_apply, LinearMap.sub_apply]
  module

/--
Coframe specialization.  If `g(θ_a,θ_b)=η_ab`, the spin bivectors act on
the Cartan coframe generators by

`[Σ_ab,c(θ_c)] = η_bc c(θ_a) - η_ac c(θ_b)`.
-/
theorem coframe_spinBivector_action
    {ι : Type*}
    (g : LinearMap.BilinForm ℝ V)
    (hg : ∀ x y, g x y = g y x)
    (θ : ι → V)
    (η : ι → ι → ℝ)
    (hθ : ∀ a b, g (θ a) (θ b) = η a b)
    (a b c : ι) :
    endCommutator
        (spinBivector g (θ a) (θ b))
        (cartanCliffordAction g (θ c)) =
      (η b c) • cartanCliffordAction g (θ a) -
        (η a c) • cartanCliffordAction g (θ b) := by
  rw [spinBivector_comm_cartanCliffordAction g hg]
  rw [hθ, hθ]

end InfoGeometry.Canonical.KahlerAtiyahSpinConnection
