import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Arithmetic.SpectralDistance
import InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge
import InfoGeometry.Canonical.HestenesKreinModularGeometry
import InfoGeometry.Analysis.BregmanAnalyticBound

/-!
# Trace-Class Compatibility Sketch — The Remaining Analytic Gap

This file records the target data for the operator
`T = -e^{-sH}` on ℓ²(ℕ^+) where `H|n⟩ = log(n)·|n⟩`; it does not yet
instantiate a Mathlib trace-class or Fredholm-determinant object.

## Target statement (not proved in this file)

    For Re(s) > 1: e^{-sH} is trace-class on ℓ²(ℕ^+).
    Trace: Tr(e^{-sH}) = Σ_n n^{-s} = ζ(s).
    Fredholm determinant: det(1 - e^{-sH}) = ∏_n (1 - n^{-s}).

    No analytic continuation or zero-free statement is established here.

## The Gap

    - the scalar excited-mode weights are strictly below one for Re(s) > 0
      (proved by primon_mode_strict_contraction in
      InfoGeometry.Arithmetic.SpectralDistance)

    - For Re(s) > 1: the eigenvalues satisfy Σ |n^{-s}| < ∞
      → e^{-sH} is trace-class (requires mathlib: `summable_of_absolutely_summable`)

    - The Fredholm determinant `det(1 - e^{-sH})` is defined as the
      regularized determinant for trace-class operators (mathlib: `FredholmDet`)

    - The first-order expansion `det(1+T) = 1 + Tr(T) + O(T²)` is already
      in `KreinFredholmDeterminantContract` (HestenesKreinModularGeometry.lean:358)

    What remains: constructing the operator and proving the trace-class and
    determinant statements in the appropriate functional-analytic setting.
    Pointwise contraction does not supply analytic continuation or a zero-free
    region.
-/

open Complex

namespace InfoGeometry.Analysis.TraceClassBridge

open InfoGeometry.Arithmetic.BostConnesSystem
open InfoGeometry.Canonical
open InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge

/- ## The Trace-Class Operator e^{-sH} -/

/-! ## Finite diagonal trace readout

The following finite matrix is the honest finite-dimensional shadow of the
diagonal operator described above.  It does not assert trace-class membership
of an operator on `ℓ²(ℕ+)`, nor does it introduce a Fredholm determinant. -/

noncomputable def finiteDirichletDiagonal
    (N : ℕ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => ((i.1 + 1 : ℕ) : ℂ) ^ (-s))

private lemma sum_fin_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M]
    (N : ℕ) (F : ℕ → M) :
    (∑ i : Fin N, F (i.1 + 1)) = ∑ n ∈ Finset.Icc 1 N, F n := by
  classical
  refine Finset.sum_bij (fun i _ => i.1 + 1) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_Icc]
    omega
  · intro i hi j hj hij
    apply Fin.ext
    change i.1 + 1 = j.1 + 1 at hij
    omega
  · intro n hn
    have hn' := Finset.mem_Icc.mp hn
    refine ⟨⟨n - 1, ?_⟩, by simp, ?_⟩
    · omega
    · simpa using Nat.sub_add_cancel hn'.1
  · intro i hi
    rfl

theorem finiteDirichletDiagonal_trace
    (N : ℕ) (s : ℂ) :
    Matrix.trace (finiteDirichletDiagonal N s) =
      ∑ i : Fin N, ((i.1 + 1 : ℕ) : ℂ) ^ (-s) := by
  exact Matrix.trace_diagonal _

theorem finiteDirichletDiagonal_trace_exp
    (N : ℕ) (s : ℂ) :
    Matrix.trace (finiteDirichletDiagonal N s) =
      ∑ i : Fin N,
        Complex.exp
          (-(s * (Real.log ((i.1 + 1 : ℕ) : ℝ) : ℂ))) := by
  rw [finiteDirichletDiagonal_trace]
  apply Finset.sum_congr rfl
  intro i hi
  rw [complexPow_nat_eq_exp_neg_log (i.1 + 1) (Nat.succ_pos i.1) s]

theorem finiteDirichletDiagonal_trace_eq_shift_scalar
    (N : ℕ) (s : ℂ) :
    Matrix.trace (finiteDirichletDiagonal N s) =
      ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) := by
  rw [finiteDirichletDiagonal_trace]
  exact sum_fin_succ_eq_sum_Icc N (fun n => (n : ℂ) ^ (-s))

theorem finiteDirichletDiagonal_trace_operator_readout
    (N : ℕ) (s : ℂ) :
    Matrix.trace (finiteDirichletDiagonal N s) •
        expTestFun s =
      finiteDirichletShiftOp N (expTestFun s) := by
  rw [finiteDirichletDiagonal_trace_eq_shift_scalar]
  exact (finiteDirichletShift_exponentialTest_cpow N s).symm

/-
The diagonal operator e^{-sH} on ℓ²(ℕ^+) has eigenvalues λ_n = n^{-s}
for the standard orthonormal basis |n⟩ (n ∈ ℕ^+).

For Re(s) > 1:
    Σ_n |n^{-s}| = Σ_n n^{-Re(s)} = ζ(Re(s)) < ∞

Therefore e^{-sH} is trace-class for Re(s) > 1.

The trace is:
    Tr(e^{-sH}) = Σ_n n^{-s} = ζ(s)

For Re(s) > 1/2 one may obtain pointwise contraction for non-vacuum
diagonal entries.  This alone does not prove trace-class membership,
Fredholm invertibility, determinant non-vanishing, or a zero-free region for
ζ.  No KMS construction or analytic continuation is supplied here.

## The Structural Bridge

    KreinFredholmDeterminantContract (HestenesKreinModularGeometry.lean:343)
    └── determinant = 1 + kreinTrace        (first-order expansion)
    └── determinant_of_trace_zero = det=1     (trace zero → unit)

    For T = -e^{-sH}:
    └── kreinTrace = -Tr(e^{-sH}) = -ζ(s)    (for Re(s) > 1)
    └── determinant = 1 - ζ(s) at this first-order contract level; this is
        not a Fredholm determinant identity and is not 1/ζ(s).

    A full determinant, if constructed for this eigenvalue list, would be a
    product over the chosen list of integers n.  It is not automatically the
    Euler product over primes and is not identified with 1/ζ(s) here.  Hence
    no Fredholm determinant/ζ identity or zero-free statement is claimed.

    The KreinFredholmDeterminantContract provides det(1+T) = 1 + Tr(T)
    at first order. For T = -e^{-sH}, this gives:
    └── det(1 - e^{-sH}) ≈ 1 - Tr(e^{-sH}) = 1 - ζ(s) (first-order)

    Target full Fredholm expansion, pending a genuine trace-class backend:
    └── det(1 - e^{-sH}) = exp(Tr(log(1 - e^{-sH})))
                        = exp(-Σ_k (1/k)·Tr(e^{-ksH}))
                        = exp(-Σ_k (1/k)·ζ(k·s))

    This is the intended trace-class / Fredholm determinant identity.  It is
    not a theorem of this compatibility sketch.

    The repo HAS the first-order version (KreinFredholmDeterminantContract).
    The FULL Fredholm expansion requires the trace-class spectral theorem
    in mathlib.
-/

/- ## The Remaining Gap — Mapping Between Types -/

/-
The `KreinFredholmDeterminantContract` expects a bounded real endomorphism
`T : RealEnd E` on a normed space `E`. Our operator `e^{-sH}` acts on the
sequence space ℓ²(ℕ^+), which is a Hilbert space.

The gap is:
1. Construct ℓ²(ℕ^+) as a normed ℝ-vector space
2. Define H = diag(log n) as an unbounded operator on ℓ²(ℕ^+)
3. Define e^{-sH} via the functional calculus (or directly via eigenvalues)
4. Prove e^{-sH} is bounded for Re(s) > 0
5. Prove e^{-sH} is trace-class for Re(s) > 1 (Σ |n^{-s}| < ∞)
6. Instantiate KreinFredholmDeterminantContract with T = -e^{-sH}
7. Compute kreinTrace = -Tr(e^{-sH}) = -ζ(s) for Re(s) > 1
8. Apply determinant_of_trace_zero when Tr = 0 → det = 1
   (This covers the case s → ∞, where ζ(s) → 1, Tr → 0)
9. Use analytic continuation (Dikin sandwich) to extend from Re(s) > 1
   to Re(s) > 1/2

Steps 1-5 require the functional analysis library (Hilbert spaces, trace-class
operators). Steps 6-8 use the existing repo structures. Step 9 uses the
Millennium Chain (Dikin positivity + Möbius protection + chiral anticommutation).

This file is only a compatibility sketch for the classical trace-class route.
The repository owner route is the Hestenes--Krein/categorical filtered-colimit
readout, not an asserted Mathlib Fredholm closure.
-/

end InfoGeometry.Analysis.TraceClassBridge
