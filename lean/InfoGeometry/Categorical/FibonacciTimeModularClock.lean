import InfoGeometry.Categorical.FibonacciSelfDualCarrier
import InfoGeometry.Quantum.Monodromy

/-!
# InfoGeometry.Categorical.FibonacciTimeModularClock

Single-coefficient-semiring time/tick bridge for Fibonacci carrier observables.

The carrier introduced in `FibonacciSelfDualCarrier` is parameterized by one
coefficient semiring `A`.  This file keeps that constraint and adds a theorem
surface for:

* coefficient-time ticks as semiring endomorphisms `A →+* A`;
* monodromy ticks of matrix observables by applying the coefficient tick;
* stabilized parabolic clocks as fixed observables under all ticks;
* the existing nilpotent Jordan/parabolic monodromy power law.

No analytic modular-automorphism group is constructed here.  A concrete
Tomita/KMS module can instantiate the tick endomorphism once it has a genuine
operator-flow action on coefficients.
-/

noncomputable section

set_option autoImplicit false

namespace InfoGeometry.Categorical.FibonacciTimeModularClock

open InfoGeometry.Categorical.FibonacciSelfDualCarrier

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## Coefficient-time ticks on one semiring -/

/-- A discrete coefficient-time tick on the single semiring used by a carrier. -/
abbrev CoefficientTick (A : Type*) [Semiring A] :=
  A →+* A

/-- Apply a coefficient-time tick entrywise to a `2 × 2` observable. -/
def tickMatrix {A : Type*} [Semiring A]
    (σ : CoefficientTick A) (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix (Fin 2) (Fin 2) A :=
  M.map σ

/-- Iterate a coefficient-time tick on a `2 × 2` observable. -/
def tickMatrixIter {A : Type*} [Semiring A]
    (σ : CoefficientTick A) : Nat → Matrix (Fin 2) (Fin 2) A → Matrix (Fin 2) (Fin 2) A
  | 0, M => M
  | n + 1, M => tickMatrix σ (tickMatrixIter σ n M)

/-- A stabilized clock observable is fixed by one coefficient-time tick. -/
def StabilizedClock {A : Type*} [Semiring A]
    (σ : CoefficientTick A) (M : Matrix (Fin 2) (Fin 2) A) : Prop :=
  tickMatrix σ M = M

@[simp]
theorem tickMatrixIter_zero {A : Type*} [Semiring A]
    (σ : CoefficientTick A) (M : Matrix (Fin 2) (Fin 2) A) :
    tickMatrixIter σ 0 M = M :=
  rfl

@[simp]
theorem tickMatrixIter_succ {A : Type*} [Semiring A]
    (σ : CoefficientTick A) (n : Nat) (M : Matrix (Fin 2) (Fin 2) A) :
    tickMatrixIter σ (n + 1) M = tickMatrix σ (tickMatrixIter σ n M) :=
  rfl

/-- One-tick stabilization implies stabilization under every discrete tick. -/
theorem tickMatrixIter_eq_of_stabilized {A : Type*} [Semiring A]
    (σ : CoefficientTick A) {M : Matrix (Fin 2) (Fin 2) A}
    (hM : StabilizedClock σ M) :
    ∀ n : Nat, tickMatrixIter σ n M = M := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [tickMatrixIter_succ, ih]
      exact hM

/-! ## Carrier readouts for stabilized monodromy ticks -/

/-- Every ticked matrix observable preserves the installed self-dual cone. -/
theorem tickedObservable_mem_positiveCone {A : Type*} [Semiring A]
    (C : ActionModel (E := E) A)
    (σ : CoefficientTick A)
    (n : Nat) (M : Matrix (Fin 2) (Fin 2) A) {x : E}
    (hx : x ∈ (C.positiveCone.cone : Set E)) :
    C.limitObservableAction (tickMatrixIter σ n M) x ∈
      (C.positiveCone.cone : Set E) :=
  C.limitObservableAction_mem_positiveCone (tickMatrixIter σ n M) hx

/--
If the parabolic/monodromy clock observable is stabilized by one tick, then
the carrier action is pointwise unchanged by all discrete ticks.
-/
theorem stabilizedClock_action_eq {A : Type*} [Semiring A]
    (C : ActionModel (E := E) A)
    (σ : CoefficientTick A)
    {M : Matrix (Fin 2) (Fin 2) A}
    (hM : StabilizedClock σ M)
    (n : Nat) (x : E) :
    C.limitObservableAction (tickMatrixIter σ n M) x =
      C.limitObservableAction M x := by
  rw [tickMatrixIter_eq_of_stabilized σ hM n]

/--
Stabilized clocks preserve the cone after any number of monodromy ticks, read
as the original stabilized observable.
-/
theorem stabilizedClock_action_mem_positiveCone {A : Type*} [Semiring A]
    (C : ActionModel (E := E) A)
    (σ : CoefficientTick A)
    {M : Matrix (Fin 2) (Fin 2) A}
    (hM : StabilizedClock σ M)
    (n : Nat) {x : E}
    (hx : x ∈ (C.positiveCone.cone : Set E)) :
    C.limitObservableAction M x ∈ (C.positiveCone.cone : Set E) := by
  have htick := tickedObservable_mem_positiveCone C σ n M hx
  simpa [stabilizedClock_action_eq C σ hM n x] using htick

/-! ## Parabolic nilpotent clock law -/

/--
The repo-owned parabolic monodromy tick law: for a square-zero nilpotent `N`
commuting with `u`, powers of the Jordan/parabolic clock `u + N` have the exact
finite tick expansion.
-/
theorem parabolicClock_power
    {A : Type*} [Ring A]
    (u N : A)
    (h_comm : Commute u N)
    (h_nil : N * N = 0)
    (n : Nat) :
    (u + N) ^ (n + 1) = u ^ (n + 1) + (n + 1) • (u ^ n * N) :=
  InfoGeometry.QuantumMonodromy.nilpotent_jordan_power u N h_comm h_nil n

end InfoGeometry.Categorical.FibonacciTimeModularClock
