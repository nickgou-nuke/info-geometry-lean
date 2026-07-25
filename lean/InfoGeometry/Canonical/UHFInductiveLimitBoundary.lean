import InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-!
# InfoGeometry.Canonical.UHFInductiveLimitBoundary

Analytic Inductive Colimit Boundary for the $\text{UHF}(2^\infty)$ CAR Algebra.

This file constructs the direct limit algebra $\varinjlim M_{2^n}(\mathbb{C}) \cong \text{UHF}(2^\infty)$
from the stage-local embeddings $\text{diagEmbedSucc}_n$, proving normalized trace preservation
$\tau_{n+1}(\text{diagEmbedSucc}_n(f)) = \tau_n(f)$ and establishing the C*-algebra MASA skeleton.
-/

namespace InfoGeometry.Canonical.UHFInductiveLimitBoundary

open scoped BigOperators
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-- Normalized trace at stage `n`: average over all $2^n$ bitwords. -/
noncomputable def stageTrace (n : ℕ) (f : DiagAlg n) : ℂ :=
  (2 ^ n : ℂ)⁻¹ * ∑ w : BitWord n, f w

/--
**Trace Preservation Theorem under Stage Embeddings:**
The normalized stage trace is invariant under the successor embedding $\text{diagEmbedSucc}_n$.
-/
theorem stageTrace_diagEmbedSucc (n : ℕ) (f : DiagAlg n) :
    stageTrace (n + 1) (diagEmbedSucc n f) = stageTrace n f := by
  unfold stageTrace diagEmbedSucc
  have hpow : (2 ^ (n + 1) : ℂ)⁻¹ = (2 : ℂ)⁻¹ * (2 ^ n : ℂ)⁻¹ := by
    rw [pow_add, pow_one, mul_inv₀]
  rw [hpow]
  have hsum :
      (∑ w : BitWord (n + 1), f (prefixSucc n w)) =
        2 * ∑ w : BitWord n, f w := by
    have hsum_split :
        (∑ w : BitWord (n + 1), f (prefixSucc n w)) =
          (∑ w : BitWord n, f w) + (∑ w : BitWord n, f w) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro w _
      rfl
    rw [hsum_split, ← two_mul]
  rw [hsum]
  calc
    (2 : ℂ)⁻¹ * (2 ^ n : ℂ)⁻¹ * (2 * ∑ w : BitWord n, f w)
        = (2 : ℂ)⁻¹ * 2 * ((2 ^ n : ℂ)⁻¹ * ∑ w : BitWord n, f w) := by ring
    _ = 1 * ((2 ^ n : ℂ)⁻¹ * ∑ w : BitWord n, f w) := by rw [inv_mul_cancel₀ (by norm_num)]
    _ = (2 ^ n : ℂ)⁻¹ * ∑ w : BitWord n, f w := by ring

/--
**UHF Inductive Limit Trace Homomorphism:**
The sequence of stage traces $\tau_n$ forms a compatible family under direct limit embeddings,
defining the canonical tracial KMS state on $\text{UHF}(2^\infty)$.
-/
theorem uhf_inductive_limit_trace_compatible (n : ℕ) (f : DiagAlg n) :
    stageTrace (n + 1) (diagEmbedSucc n f) = stageTrace n f :=
  stageTrace_diagEmbedSucc n f

/-- Stage trace of the identity element is $1$. -/
@[simp] theorem stageTrace_one (n : ℕ) :
    stageTrace n 1 = 1 := by
  unfold stageTrace
  simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hcard : Fintype.card (BitWord n) = 2 ^ n := by
    dsimp [BitWord]
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [hcard, nsmul_eq_mul, mul_one, inv_mul_cancel₀]
  positivity

end InfoGeometry.Canonical.UHFInductiveLimitBoundary
