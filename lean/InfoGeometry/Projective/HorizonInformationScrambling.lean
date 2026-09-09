import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Reflection
import InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding
import InfoGeometry.Projective.AndreevHorizonUnitarity
import InfoGeometry.Projective.FiveGradedCentralizer

/-!
# Horizon Information Braiding

#### BUCKET 1: CLOSED FINITE THEOREMS

- `horizonFibonacciRegister_card`
- `finite_unitary_braiding_packet`

#### BUCKET 2: CONDITIONAL INTERFACE

- `ModularTimeFlow.conserves_information` is an explicit witness field.

#### BUCKET 3: OPEN CLOSURE DEBT

- Construct an actual braid-group representation from the projective boundary.
- Prove unitarity implies the matrix quadratic-form conservation equation in
  the selected representation.
- Prove any Hayden-Preskill or fast-scrambling estimate from that
  representation.
- Connect the rank-32 Betti certificate to protected Majorana/Fibonacci boundary
  modes.

This module is an interface layer.  It records the finite Fibonacci register
cardinality already present in the repo and packages a supplied unitary
braiding/conservation witness.  It does not prove density of a braid-group
image, a fast-scrambling bound, or existence of Majorana zero modes on a
physical horizon.
-/

namespace InfoGeometry.Projective.Scrambling

open InfoGeometry.Canonical.FiniteFibonacciAnyonBraiding

/-- Finite boundary microstate registers. -/
structure HorizonMicrostates (n : ℕ) where
  state_vector : Matrix (Fin n) (Fin 1) ℂ

/-- Matrix quadratic-form conservation equation for a supplied braid operator. -/
def InformationConservationEquation {n : ℕ}
    (braidOperator : Matrix (Fin n) (Fin n) ℂ)
    (state : HorizonMicrostates n) : Prop :=
  (braidOperator * state.state_vector).conjTranspose *
      (braidOperator * state.state_vector) =
    state.state_vector.conjTranspose * state.state_vector

/-- A supplied finite unitary braiding operator with an explicit conservation certificate. -/
structure ModularTimeFlow (n : ℕ) where
  braid_operator : Matrix (Fin n) (Fin n) ℂ
  is_unitary : braid_operator.conjTranspose * braid_operator = 1
  conserves_information :
    ∀ state : HorizonMicrostates n,
      InformationConservationEquation braid_operator state

/-- A predicate verifying that the supplied flow is unitary. -/
def IsUnitaryBraiding {n : ℕ} (flow : ModularTimeFlow n) : Prop :=
  flow.braid_operator.conjTranspose * flow.braid_operator = 1

/-- The supplied flow preserves the quadratic information form on the given state. -/
def InformationIsConserved {n : ℕ}
    (flow : ModularTimeFlow n) (state : HorizonMicrostates n) : Prop :=
  InformationConservationEquation flow.braid_operator state

/-- The finite Fibonacci register associated to `2N + 2` anyons. -/
abbrev HorizonFibonacciRegister (N : ℕ) : Type :=
  FibonacciComputationalSpace N

/-- The finite Fibonacci register has the repo-owned Fibonacci cardinality. -/
theorem horizonFibonacciRegister_card (N : ℕ) :
    Fintype.card (HorizonFibonacciRegister N) = Nat.fib (2 * N + 1) :=
  card_fibonacciComputationalSpace N

/--
Finite unitary-braiding packet: supplied unitarity plus a supplied conservation
certificate.
-/
theorem finite_unitary_braiding_packet {n : ℕ}
    (flow : ModularTimeFlow n) (state : HorizonMicrostates n) :
    IsUnitaryBraiding flow ∧ InformationIsConserved flow state := by
  exact ⟨flow.is_unitary, flow.conserves_information state⟩

end InfoGeometry.Projective.Scrambling
