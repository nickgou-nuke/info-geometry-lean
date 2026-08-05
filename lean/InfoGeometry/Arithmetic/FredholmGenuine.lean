import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Colimit.DirectLimit
import InfoGeometry.Arithmetic.SpectralDistance
import InfoGeometry.Arithmetic.FredholmClosure
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Canonical.HestenesKreinModularGeometry
import InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonal

/-!
# Fredholm Genuine — Data-Gated Analytic Boundary

This file records the strongest Lean-safe Fredholm endpoint currently available
in this repository. Finite determinant and recurrence identities are proved in
owner files. The infinite Fredholm determinant remains gated by the explicit
`FredholmClosureData` from `FredholmClosure.lean`.

## The Finite/Certificate Chain

1. **Finite identity** (MatrixDetExpTrace/Diagonal.lean, PROVED):
   det(exp(diag(v))) = exp(tr(diag(v))) for all Fintype ι.

2. **Regularized finite determinant** (FredholmClosure.lean, PROVED):
   R_N(β) = ∏_{n≤N} (1 - n^{-β}) with recurrence R_{N+1} = R_N · (1-(N+1)^{-β}).

3. **SOP lift** (FiniteToInfiniteTransitionSOP): the recurrence is stable
   under adding one mode, so it holds for every finite cutoff.

4. **Fredholm determinant identity** (KreinFredholmDeterminantContract):
   det(1+T) = 1 + Tr(T) at first order. For T = -e^{-βH}, this gives the
   linear approximation to the infinite product.

5. **Analytic closure**: trace-class convergence, Fredholm determinant
   continuity, and determinant/zeta calibration are explicit fields of
   `FredholmClosureData`; they are not manufactured here.

## What is PROVED vs Structural

- ✔ Finite determinant identity (all Fintype ι)
- ✔ Finite product recurrence (Finset.prod_range_succ)
- ✔ First-order Fredholm formula det(1+T) = 1 + Tr(T)
- ✔ Spectral contraction |n^{-s}| < 1 for Re(s) > 1/2, n ≥ 2
- ✔ Dikin positivity ω(t) > 0 for t > 0
- Certificate-gated: trace-norm convergence on `Re(β) > 1`
- Certificate-gated: embedding into a trace-class ideal rather than only compact operators
- Certificate-gated: Fredholm determinant continuity in trace norm
-/

open Complex

namespace InfoGeometry.Arithmetic.FredholmGenuine

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.HestenesKreinModularGeometry
open InfoGeometry.Cocycle.MatrixDetExpTrace.Diagonal

/- ## 1. The Directed System of Finite Matrix Algebras -/

/-
The directed system:
    A_1 → A_2 → A_3 → ... → lim_{→} A_N = SplitCliffordInfinity

where A_N = SplitClNNAlg N ≅ M_{2^N}(ℝ) (the split Clifford algebra Cl(N,N)).

The inclusion maps ι_{N,M}: A_N → A_M (for N ≤ M) are the splitCliffordMap
from SplitCliffordDirectLimit.lean. These are algebra homomorphisms preserving
the star operation.

The colimit SplitCliffordInfinity is the UHF algebra (uniformly hyperfinite)
of type 2^∞. Its spectrum is the Cantor set {0,1}^ℕ.

For the Fredholm determinant application:
- The finite operators T_N = -diag(n^{-β})_{n≤N} live in the diagonal
  subalgebra of M_N(ℂ).
- The inclusion ι_{N,N+1} adds one more prime mode: T_N ↦ diag(T_N, (N+1)^{-β}).
- The colimit T = lim T_N = -diag(n^{-β})_{n∈ℕ^+} is the diagonal operator
  on ℓ²(ℕ^+).
-/

/- ## 2. Trace-Norm Convergence -/

/-
For Re(β) > 1:
    ‖T - T_N‖₁ = Σ_{n=N+1}^∞ |n^{-β}| = Σ_{n=N+1}^∞ n^{-Re(β)} → 0 as N → ∞.

This is the tail of the convergent series Σ n^{-Re(β)} = ζ(Re(β)) < ∞.

The trace norm convergence is the analytic condition that makes the
colimit identity hold: because T_N → T in trace norm, and the Fredholm
determinant det(I+·) is continuous in trace norm, we have:

    det(I+T) = lim_{N→∞} det(I+T_N) = lim_{N→∞} ∏_{n≤N} (1-n^{-β})
             = ∏_{n=1}^∞ (1-n^{-β}) = 1/ζ(β)

The construction requires:
1. Defining the trace norm ‖·‖₁ on the algebra of trace-class operators B₁
2. Proving that T_N ∈ B₁ for each N (finite-rank → trace-class)
3. Proving that T ∈ B₁ for Re(β) > 1 (the eigenvalues are n^{-β}, summable)
4. Proving that ‖T - T_N‖₁ → 0 as N → ∞
5. Proving that det(I+·) is continuous on B₁

Steps 1-4 are functional-analysis obligations. Step 5 is a theorem about
the Fredholm determinant. The local mathlib snapshot does not expose a
ready-made trace-class Fredholm determinant API in the owner searches used for
this file, so this remains certificate data.

The repo already has:
- `FiniteToInfiniteTransitionSOP.lean`: the SOP for lifting readouts
- `KreinFredholmDeterminantContract`: det(1+T) = 1 + Tr(T) at first order
- `MatrixDetExpTrace/Diagonal.lean`: the finite diagonal identity

What's missing: the trace-norm topology, the trace-class inclusion, and the
continuity theorem as repo-owned Lean declarations.
-/

/- ## 3. The Certificate-Gated Theorem -/

/--
**Certificate-gated Fredholm determinant theorem.**

For Re(β) > 1:
    determinant(β) · ζ(β) = 1
    determinant(β) ≠ 0

Proof sketch:
1. Finite identity: R_N(β) = ∏_{n≤N} (1-n^{-β}) = det(I+T_N).
   This is the diagonal determinant formula, proved for all Fintype ι
   in MatrixDetExpTrace/Diagonal.lean.

2. SOP lift: R_{N+1}(β) = R_N(β) · (1-(N+1)^{-β}). Proved in
   FredholmClosure.lean (regularizedDetStage_succ).

3. Trace-norm convergence: ‖T - T_N‖₁ → 0 for Re(β) > 1.
   Supplied by `FredholmClosureData.traceNorm_cutoff_tendsto`.

4. Continuity of det: supplied by
   `FredholmClosureData.determinant_cutoff_tendsto`.

5. Universal property: lim_{N→∞} det(I+T_N) = det(I+lim_{N→∞} T_N).
   Follows from (3) + (4).

6. The Lean theorem below projects the determinant/zeta identity and
   nonvanishing from explicit `FredholmClosureData`.
-/
theorem genuine_fredholm_determinant
    (C : FredholmClosure.FredholmClosureData) {β : ℂ} (hβ : 1 < β.re) :
    C.determinant β * C.zeta β = 1 ∧ C.determinant β ≠ 0 :=
  ⟨FredholmClosure.fredholm_determinant_mul_zeta_eq_one C hβ,
    FredholmClosure.fredholm_closure_theorem C hβ⟩

end InfoGeometry.Arithmetic.FredholmGenuine
