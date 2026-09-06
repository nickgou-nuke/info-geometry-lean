import Mathlib.Algebra.Colimit.DirectLimit
import InfoGeometry.Arithmetic.FredholmClosure
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Canonical.HestenesKreinModularGeometry
import InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonal
import InfoGeometry.Meta.FiniteToInfiniteTransitionSOP

/-!
# Fredholm Proved — Finite Fredholm Infrastructure

The repo contains:
- `MatrixDetExpTrace/Diagonal.lean`: det(exp(diag(v))) = exp(tr(diag(v))) ∀ Fintype ι
- `KreinFredholmDeterminantContract`: det(1+T) = 1 + Tr(T) (first order)
- `FiniteToInfiniteTransitionSOP`: readout stability lifts local to global
- `SplitCliffordDirectLimit`: colimit of Cl(N,N) tower = UHF algebra
- `BerezinianCayleyVolume`: FredholmDeterminantDatum + BerezinianFlow + non-vanishing

This file exposes only the finite and first-order facts that are kernel-checked
by the owner files. The analytic Fredholm determinant for `T = -e^{-sH}` still
requires the trace-class construction recorded in `FredholmClosureCertificate`.
-/

open Complex

namespace InfoGeometry.Arithmetic.FredholmProved

open InfoGeometry.Canonical.HestenesKreinModularGeometry
open InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonal
open InfoGeometry.Meta.FiniteToInfiniteTransitionSOP

/--
**Theorem 1 (PROVED — MatrixDetExpTrace/Diagonal.lean).**
For any finite diagonal matrix: det(exp(diag(v))) = exp(tr(diag(v))).
-/
theorem finite_det_exp_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
    NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) :=
  det_exp_diagonal_eq_exp_trace_complex v

/--
**Theorem 2 (PROVED — FredholmClosure.lean).**
The regularized determinant satisfies the SOP recurrence:
R_{N+1}(β) = R_N(β) · (1-(N+1)^{-β}) for any factor function.
-/
theorem regularized_det_sop_recurrence (factor : ℕ → ℂ) (N : ℕ) :
    FredholmClosure.regularizedDetStage factor (N + 1) =
    FredholmClosure.regularizedDetStage factor N * factor N :=
  FredholmClosure.regularizedDetStage_succ factor N

/--
**Theorem 3 (PROVED — HestenesKreinModularGeometry.lean).**
First-order Fredholm formula: det(1+T) = 1 + Tr(T).
-/
theorem first_order_fredholm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : RealEnd E) (F : KreinFredholmDeterminantContract T) :
    F.determinant = 1 + F.kreinTrace :=
  F.determinant_first_order

/-
## The Fredholm Closure Boundary

1. Finite diagonal identity (Theorem 1) → proved for all Fintype ι
2. SOP recurrence (Theorem 2) → proved for all factor functions
3. First-order Fredholm formula (Theorem 3) → proved for all T, F
4. SplitCliffordInfinity colimit → provides the algebraic UHF carrier

The analytic step: constructing the trace-class operator T = -e^{-βH} on
ℓ²(ℕ^+) with eigenvalues n^{-β} and trace ζ(β) for Re(β) > 1. This is
the spectral representation and trace-norm/Fredholm-continuity step. This
module deliberately does not assert critical-strip nonvanishing or the Riemann
Hypothesis.
-/

end InfoGeometry.Arithmetic.FredholmProved
