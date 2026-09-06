import InfoGeometry.Canonical.InductiveOperatorTaylorClosure
import InfoGeometry.Algebra.FiniteInductiveSUSY
import InfoGeometry.Foundations.NewtonKantorovichSequence
import InfoGeometry.Canonical.SinkhornFoundation

/-!
# InfoGeometry.Canonical.RecursiveClosureBridge

Common recursive-closure architecture.

This file packages the shared shape that appears across:

* finite inductive operator-Taylor prefixes,
* finite inductive SUSY closure chains,
* Newton-Kantorovich majorant sequences,
* Sinkhorn / convex normalization trajectories.

The point is structural: a stagewise invariant is proved at stage `0` and
propagated by a successor step.  No analytic continuation is involved.
-/

namespace InfoGeometry.Canonical.RecursiveClosureBridge

/-! ## Generic stagewise recursion skeleton -/

/--
A generic stagewise recursion schema.

This packages the common architecture:
`x₀` is invariant at stage `0`, and the stage update preserves invariance.
-/
structure RecursiveClosureSkeleton where
  /-- Stage family. -/
  State : Nat → Type u
  /-- Stage update. -/
  update : ∀ n : Nat, State n → State (n + 1)
  /-- Stagewise invariant predicate. -/
  invariant : ∀ n : Nat, State n → Prop
  /-- Initial stage. -/
  base : State 0
  /-- Initial invariant. -/
  base_ok : invariant 0 base
  /-- Invariant preservation under the successor update. -/
  step_ok : ∀ n : Nat, ∀ x : State n, invariant n x → invariant (n + 1) (update n x)

namespace RecursiveClosureSkeleton

variable (R : RecursiveClosureSkeleton)

/-- The recursively generated state sequence. -/
def state : ∀ n : Nat, R.State n
  | 0 => R.base
  | n + 1 => R.update n (state n)

@[simp]
theorem state_zero : R.state 0 = R.base := rfl

@[simp]
theorem state_succ (n : Nat) : R.state (n + 1) = R.update n (R.state n) := rfl

/-- Every stage of a recursive closure skeleton satisfies the invariant. -/
theorem invariant_all : ∀ n : Nat, R.invariant n (R.state n) := by
  intro n
  induction n with
  | zero =>
      simpa using R.base_ok
  | succ n ih =>
      simpa using R.step_ok n (R.state n) ih

end RecursiveClosureSkeleton

/-! ## Concrete recursive families already owned by the repo -/

section OperatorTaylor

/--
Finite operator-Taylor prefixes are recursive stagewise objects:
each successor stage is the previous prefix plus the next coefficient term.
-/
theorem operatorTaylorPrefix_succ_schema
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (c : ℕ → ℂ) (A : V →ₗ[ℂ] V) (N : ℕ) :
    InductiveOperatorTaylorClosure.operatorTaylorPrefix c (N + 1) A =
      InductiveOperatorTaylorClosure.operatorTaylorPrefix c N A +
        c N • (A ^ N) :=
  InductiveOperatorTaylorClosure.operatorTaylorPrefix_succ c N A

end OperatorTaylor

section FiniteSUSY

open InfoGeometry.Algebra.FiniteInductiveSUSY

/--
Finite inductive SUSY closure is the same stagewise shape:
the odd-odd anticommutator relation is preserved by each bonding map.
-/
theorem finiteInductiveSUSY_diracSquare_closure_chain
    {A : ℕ → Type*} [∀ n : ℕ, Ring (A n)]
    (φ : ∀ n : ℕ, A n →+* A (Nat.succ n))
    (Q R H Z : ∀ n : ℕ, A n)
    (hQ0 : Q 0 * Q 0 = 0)
    (hR0 : R 0 * R 0 = 0)
    (hclosure0 : anticomm (Q 0) (R 0) = H 0 + Z 0)
    (hQstep : ∀ n : ℕ, Q (Nat.succ n) = φ n (Q n))
    (hRstep : ∀ n : ℕ, R (Nat.succ n) = φ n (R n))
    (hHstep : ∀ n : ℕ, H (Nat.succ n) = φ n (H n))
    (hZstep : ∀ n : ℕ, Z (Nat.succ n) = φ n (Z n)) :
    ∀ n : ℕ, (Q n + R n) * (Q n + R n) = H n + Z n :=
  dirac_square_closure_chain φ Q R H Z hQ0 hR0 hclosure0 hQstep hRstep hHstep hZstep

end FiniteSUSY

section NewtonKantorovich

open InfoGeometry.Foundations.NewtonKantorovichSequence
open InfoGeometry.Foundations.NewtonKantorovichRoots

/--
Newton-Kantorovich majorant iteration is a recursive invariant system:
the iterate stays in the closed interval once the step is invariant.
-/
theorem newtonKantorovich_majorantSeq_invariant
    (L η : ℝ)
    (hη_mem : η ∈ Set.Icc 0 (tMinus L η))
    (hInv : ∀ t, t ∈ Set.Icc 0 (tMinus L η) →
      majorantStep L η t ∈ Set.Icc 0 (tMinus L η)) :
    ∀ n, majorantSeq L η (n + 1) ∈ Set.Icc 0 (tMinus L η) :=
  majorantSeq_mem_Icc_of_step_invariant L η hη_mem hInv

end NewtonKantorovich

section Sinkhorn

open InfoGeometry.Canonical.MoE

/--
Sinkhorn trajectories are recursive invariants too: each admissible step keeps
the barrier-aligned post-step objective controlled.
-/
theorem sinkhornTrajectory_phaseRNBarrier_monotone
    {n : Nat} (T : SinkhornTrajectory n) (k : Nat) :
    trajectoryRNBarrierNext n T k ≤ trajectoryRNBarrier n T k :=
  trajectoryRNBarrier_monotone (n := n) T k

end Sinkhorn

end InfoGeometry.Canonical.RecursiveClosureBridge
