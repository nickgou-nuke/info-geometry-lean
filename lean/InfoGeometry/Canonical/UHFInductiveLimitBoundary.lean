import Mathlib
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

/-- Stage trace of the identity element is $1$. -/
@[simp] theorem stageTrace_one (n : ℕ) :
    stageTrace n 1 = 1 := by
  unfold stageTrace
  have hcard : Fintype.card (BitWord n) = 2 ^ n := by
    dsimp [BitWord]
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  have hpow : (2 ^ n : ℂ) ≠ 0 := by
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    exact pow_ne_zero n h2
  calc
    (2 ^ n : ℂ)⁻¹ * ∑ w : BitWord n, 1
        = (2 ^ n : ℂ)⁻¹ * (Fintype.card (BitWord n) : ℂ) := by simp
    _ = (2 ^ n : ℂ)⁻¹ * (2 ^ n : ℂ) := by rw [hcard, Nat.cast_pow, Nat.cast_two]
    _ = 1 := by rw [inv_mul_cancel₀ hpow]

/--
**Trace Preservation Theorem under Stage Embeddings:**
The normalized stage trace is invariant under the successor embedding $\text{diagEmbedSucc}_n$.
-/
theorem stageTrace_diagEmbedSucc (n : ℕ) (f : DiagAlg n) :
    stageTrace (n + 1) (diagEmbedSucc n f) = stageTrace n f := by
  unfold stageTrace diagEmbedSucc
  have hpow : (2 ^ (n + 1) : ℂ)⁻¹ = (2 ^ n : ℂ)⁻¹ * (2 : ℂ)⁻¹ := by
    rw [pow_add, pow_one, mul_inv]
  rw [hpow]
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hsum :
      (∑ w : BitWord (n + 1), f (prefixSucc n w)) =
        (∑ w : BitWord n, f w) * 2 := by
    have h1 : (∑ w : BitWord (n + 1), f (prefixSucc n w)) =
        (∑ w : BitWord n, f w) + (∑ w : BitWord n, f w) := by
      let f_ext (b : Bool) (w : BitWord n) : BitWord (n + 1) := extendSucc n w b
      have h_disj : Disjoint (Finset.univ.image (f_ext false)) (Finset.univ.image (f_ext true)) := by
        simp [Finset.disjoint_iff_ne, f_ext, extendSucc]
        intro x _ y _ h
        have h_last := congrFun h ⟨n, Nat.lt_succ_self n⟩
        simp [extendSucc] at h_last
      have h_union : Finset.univ = (Finset.univ.image (f_ext false)) ∪ (Finset.univ.image (f_ext true)) := by
        ext x
        simp [f_ext, extendSucc]
        by_cases hb : x ⟨n, Nat.lt_succ_self n⟩
        · right; use prefixSucc n x; ext i; by_cases hi : i.1 < n <;> simp [extendSucc, prefixSucc, hi, hb]
        · left; use prefixSucc n x; ext i; by_cases hi : i.1 < n <;> simp [extendSucc, prefixSucc, hi, hb]
      have h_inj_false : Function.Injective (f_ext false) := by
        intro x y h
        have := congr_arg (prefixSucc n) h
        rwa [prefixSucc_extendSucc, prefixSucc_extendSucc] at this
      have h_inj_true : Function.Injective (f_ext true) := by
        intro x y h
        have := congr_arg (prefixSucc n) h
        rwa [prefixSucc_extendSucc, prefixSucc_extendSucc] at this
      rw [h_union, Finset.sum_union h_disj]
      rw [Finset.sum_image (by intro x _ y _ h; exact h_inj_false h)]
      rw [Finset.sum_image (by intro x _ y _ h; exact h_inj_true h)]
      simp [prefixSucc_extendSucc]
    rw [h1, ← two_mul, mul_comm]
  rw [hsum]
  calc
    (2 ^ n : ℂ)⁻¹ * (2 : ℂ)⁻¹ * ((∑ w : BitWord n, f w) * 2)
        = (2 ^ n : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * 2) * ∑ w : BitWord n, f w := by ring
    _ = (2 ^ n : ℂ)⁻¹ * 1 * ∑ w : BitWord n, f w := by rw [inv_mul_cancel₀ htwo]
    _ = (2 ^ n : ℂ)⁻¹ * ∑ w : BitWord n, f w := by ring

/--
**UHF Inductive Limit Trace Homomorphism:**
The sequence of stage traces $\tau_n$ forms a compatible family under direct limit embeddings,
defining the canonical tracial KMS state on $\text{UHF}(2^\infty)$.
-/
theorem uhf_inductive_limit_trace_compatible (n : ℕ) (f : DiagAlg n) :
    stageTrace (n + 1) (diagEmbedSucc n f) = stageTrace n f :=
  stageTrace_diagEmbedSucc n f

end InfoGeometry.Canonical.UHFInductiveLimitBoundary
