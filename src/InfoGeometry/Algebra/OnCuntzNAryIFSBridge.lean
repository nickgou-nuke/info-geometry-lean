import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Algebra.OnCuntzNAryIFSBridge

/-- **Definition**: Cuntz Algebra O_n Generators for n Isometries S_i.
    S_i* S_j = δ_ij 1, and ∑_{i} S_i S_i* = 1. -/
structure OnCuntzGenerators (n : ℕ) (R : Type*) [Ring R] where
  S : Fin n → R
  Sstar : Fin n → R
  isometry : ∀ i : Fin n, Sstar i * S i = 1
  ortho : ∀ i j : Fin n, i ≠ j → Sstar i * S j = 0
  completeness : (Finset.univ : Finset (Fin n)).sum (fun i => S i * Sstar i) = 1

namespace OnCuntzGenerators

variable {n : ℕ} {R : Type*} [Ring R] (g : OnCuntzGenerators n R)

/-- Projection Operator P_i = S_i S_i* for mode i. -/
def proj (i : Fin n) : R := g.S i * g.Sstar i

/-- **Theorem**: Projection Idempotency P_i^2 = P_i. -/
theorem proj_idempotent (i : Fin n) :
    g.proj i * g.proj i = g.proj i := by
  dsimp [proj]
  have h_assoc : g.S i * g.Sstar i * (g.S i * g.Sstar i) = g.S i * (g.Sstar i * g.S i) * g.Sstar i := by noncomm_ring
  rw [h_assoc, g.isometry i, mul_one]

/-- **Theorem**: Projection Orthogonality P_i P_j = 0 for i ≠ j. -/
theorem proj_ortho {i j : Fin n} (h : i ≠ j) :
    g.proj i * g.proj j = 0 := by
  dsimp [proj]
  have h_assoc : g.S i * g.Sstar i * (g.S j * g.Sstar j) = g.S i * (g.Sstar i * g.S j) * g.Sstar j := by noncomm_ring
  rw [h_assoc, g.ortho i j h, mul_zero, zero_mul]

end OnCuntzGenerators

/-- **Definition**: Infinite n-Ary Symbol Boundary Stream {0, 1, ..., n-1}^ℕ. -/
def NAryBoundary (n : ℕ) : Type :=
  ℕ → Fin n

namespace NAryBoundary

variable {n : ℕ}

/-- Affine Prepend Digit Map (Geometric Contraction Step f_d(x) = (x + d)/n). -/
def prefixDigit (d : Fin n) (x : NAryBoundary n) : NAryBoundary n :=
  fun
    | 0 => d
    | k + 1 => x k

/-- **Theorem**: Prepend Digit Readback (Shift Inverse).
    (prefixDigit d x) 0 = d, and (prefixDigit d x) (k + 1) = x k. -/
theorem prefixDigit_head (d : Fin n) (x : NAryBoundary n) :
    prefixDigit d x 0 = d := rfl

theorem prefixDigit_tail (d : Fin n) (x : NAryBoundary n) (k : ℕ) :
    prefixDigit d x (k + 1) = x k := rfl

end NAryBoundary

/-- **Theorem**: Master O_n Cuntz Algebra & n-Ary IFS Synthesis.
    Unifies:
    1. Projection idempotency P_i^2 = P_i.
    2. Projection orthogonality P_i P_j = 0 for i ≠ j.
    3. Partition completeness ∑_{i} P_i = 1.
    4. Infinite n-ary stream shift readback. -/
theorem master_on_cuntz_nary_ifs_synthesis
    {n : ℕ} {R : Type*} [Ring R] (g : OnCuntzGenerators n R) (i j : Fin n) (h : i ≠ j)
    (d : Fin n) (x : NAryBoundary n) :
    (g.proj i * g.proj i = g.proj i) ∧
    (g.proj i * g.proj j = 0) ∧
    ((Finset.univ : Finset (Fin n)).sum (fun k => g.proj k) = 1) ∧
    (NAryBoundary.prefixDigit d x 0 = d) := ⟨
  g.proj_idempotent i,
  g.proj_ortho h,
  g.completeness,
  rfl
⟩

end InfoGeometry.Algebra.OnCuntzNAryIFSBridge
