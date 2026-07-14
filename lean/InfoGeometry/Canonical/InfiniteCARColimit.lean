import Mathlib
import InfoGeometry.Prequantum.GNSBridge

/-!
# Abstract CAR Interface + Quotient Readout

This module provides an abstract interface for algebraic CAR relations and one
narrow readout in the repository's existing algebraic GNS quotient.

The quotient readout says only that a chosen annihilation generator has the same
`AbstractGNSState.gnsQuotient` class as zero when the wrapped state declares its
quadratic norm to be zero.  It is not an operator-action theorem: no CAR
representation, no action map on quotient classes, and no annihilation dynamics
are constructed here.

It intentionally does not assert the existence of a Hilbert-space completion, a
C*-completion, an infinite inductive limit, an anomaly index, or Macaulay2 de
Rham weights.  The closed statements here are exactly the CAR anticommutator
projection lemmas and the abstract-GNS quotient identities derived from the
declared null law, including `souriau_vacuum_annihilated`.
-/

noncomputable section

namespace InfiniteCARColimit

open Filter
open scoped Topology
open InfoGeometry.Prequantum.GNSBridge
open InfoGeometry.Prequantum.AlgebraicGNSState

universe u

/-- The anticommutator in a noncommutative ring. -/
def anticommutator {A : Type u} [Ring A] (x y : A) : A :=
  x * y + y * x

variable {A : Type u} [Ring A]

/-- Countable algebraic CAR data for creation operators `u` and annihilation
operators `v`. -/
structure CARAlgebra (A : Type u) [Ring A] where
  u : ℕ → A
  v : ℕ → A
  anticomm_uv : ∀ i j, anticommutator (u i) (v j) = if i = j then 1 else 0
  anticomm_uu : ∀ i j, anticommutator (u i) (u j) = 0
  anticomm_vv : ∀ i j, anticommutator (v i) (v j) = 0

namespace CARAlgebra

variable (car : CARAlgebra A)

/-- The defining `uᵢ vⱼ` CAR relation. -/
theorem anticommutator_u_v (i j : ℕ) :
    anticommutator (car.u i) (car.v j) = if i = j then 1 else 0 :=
  car.anticomm_uv i j

/-- Diagonal CAR specialization: `{uᵢ, vᵢ} = 1`. -/
@[simp] theorem anticommutator_u_v_self (i : ℕ) :
    anticommutator (car.u i) (car.v i) = 1 := by
  simp [car.anticomm_uv i i]

/-- Off-diagonal CAR specialization: `{uᵢ, vⱼ} = 0` when `i ≠ j`. -/
theorem anticommutator_u_v_of_ne {i j : ℕ} (hij : i ≠ j) :
    anticommutator (car.u i) (car.v j) = 0 := by
  simp [car.anticomm_uv i j, hij]

/-- Creation operators anticommute. -/
@[simp] theorem anticommutator_u_u (i j : ℕ) :
    anticommutator (car.u i) (car.u j) = 0 :=
  car.anticomm_uu i j

/-- Annihilation operators anticommute. -/
@[simp] theorem anticommutator_v_v (i j : ℕ) :
    anticommutator (car.v i) (car.v j) = 0 :=
  car.anticomm_vv i j

end CARAlgebra

section AbstractGNSQuotientReadout

variable [Algebra ℝ A] [StarRing A] [StarModule ℝ A]

/-- The Souriau state interface on the CAR algebra, carrying the repository's
existing abstract GNS state.  This is only state data, not a representation or
completed GNS Hilbert space. -/
structure SouriauState (car : CARAlgebra A) where
  functional : AbstractGNSState A
  vacuum_law : ∀ i, functional.eval (star (car.v i) * car.v i) = 0

/-- The declared vacuum law places each annihilation generator in the wrapped
algebraic GNS null set. -/
lemma souriau_annihilator_mem_gnsNullSet
    {car : CARAlgebra A} (s : SouriauState car) (i : ℕ) :
    car.v i ∈ s.functional.gnsNullSet := by
  rw [AbstractGNSState.mem_gnsNullSet_iff]
  exact s.vacuum_law i

/-- Null generators pair to zero against every algebra element in the wrapped
abstract GNS state.  This is a direct use of the repository's GNS bridge lemma,
not a representation action. -/
lemma souriau_annihilator_state_pairing_zero
    {car : CARAlgebra A} (s : SouriauState car) (i : ℕ) (x : A) :
    s.functional.state.eval (star (car.v i) * x) = 0 :=
  AbstractGNSState.state_null_product_zero s.functional x (car.v i)
    (souriau_annihilator_mem_gnsNullSet s i)

/--
A valid quotient-level identity for the CAR tower inside abstract GNS state data.
It says the representative `car.v i * 1` is equal to zero in
`AbstractGNSState.gnsQuotient` when its quadratic state norm is zero.
This is not a representation theorem and defines no operator action.
-/
lemma souriau_vacuum_annihilated
    {car : CARAlgebra A} (s : SouriauState car) (i : ℕ) :
    (Quotient.mk (AbstractGNSState.gnsSetoid s.functional) (car.v i * 1) :
        AbstractGNSState.gnsQuotient s.functional) =
    (Quotient.mk (AbstractGNSState.gnsSetoid s.functional) 0 :
        AbstractGNSState.gnsQuotient s.functional) := by
  rw [mul_one]
  apply Quotient.sound
  exact (show AbstractGNSState.gnsEquiv s.functional (car.v i) 0 from by
    simpa [AbstractGNSState.gnsEquiv, RealAlgebraicState.gnsEquiv]
      using souriau_annihilator_mem_gnsNullSet s i)

end AbstractGNSQuotientReadout

end InfiniteCARColimit
