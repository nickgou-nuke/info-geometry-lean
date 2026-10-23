/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.DeterministicDrazinBridge

/-!
# Causal deterministic route dynamics

For every `f : Fin n → Fin n` with `f i ≤ i`, iteration reaches a fixed
point by step `n`. This is a sufficient bound, not a minimal-index claim.
The native deterministic attention matrix stabilizes at the same power;
that power is its canonical Drazin witness, regular projector, and core.
All statements include `n = 0`. Positive iterates have exactly the fixed
points of `f`, supplying a separate trace-consumer interface.
-/

namespace InfoGeometry.Canonical.Drazin

/-- One equality of consecutive powers forces the entire subsequent tail. -/
lemma pow_add_eq_of_stabilized {R : Type*} [Monoid R] {a : R} {k : ℕ}
    (h : a ^ (k + 1) = a ^ k) (t : ℕ) : a ^ (k + t) = a ^ k := by
  induction t with
  | zero => simp only [Nat.add_zero]
  | succ t ih =>
      calc
        a ^ (k + (t + 1)) = a ^ (k + t) * a := by
          rw [← Nat.add_assoc, pow_succ]
        _ = a ^ k * a := by rw [ih]
        _ = a ^ k := by rw [← pow_succ, h]

namespace IsDrazinInverse

/-- A stabilized power is a Drazin inverse, with the same valid index bound. -/
theorem of_stabilized_power {R : Type*} [Ring R] {a : R} {k : ℕ}
    (h : a ^ (k + 1) = a ^ k) : IsDrazinInverse a (a ^ k) k := by
  have hidem : a ^ k * a ^ k = a ^ k := by
    rw [← pow_add]
    exact pow_add_eq_of_stabilized h k
  refine mk ?_ ?_ ?_
  · exact (pow_succ' a k).symm.trans (pow_succ a k)
  · rw [← pow_succ, h, hidem]
  · rw [h, hidem]

/-- The regular projector of the stabilized-power witness is that power. -/
theorem projection_of_stabilized_power {R : Type*} [Ring R] {a : R} {k : ℕ}
    (h : a ^ (k + 1) = a ^ k) : projection a (a ^ k) = a ^ k := by
  change a * a ^ k = a ^ k
  rw [← pow_succ', h]

/-- The native core also equals the stabilized power. -/
theorem core_of_stabilized_power {R : Type*} [Ring R] {a : R} {k : ℕ}
    (h : a ^ (k + 1) = a ^ k) : core a (a ^ k) = a ^ k := by
  change a * a * a ^ k = a ^ k
  rw [mul_assoc, ← pow_succ', h, ← pow_succ', h]

end IsDrazinInverse
end InfoGeometry.Canonical.Drazin

namespace InfoGeometry.Routing.CausalRouteDynamics

variable {n : ℕ} (f : Fin n → Fin n) (hf : ∀ i, f i ≤ i)
include hf

/-- Every iterate lies below its starting point; monotonicity of `f` is unnecessary. -/
lemma iterate_le_self (m : ℕ) (i : Fin n) : f^[m] i ≤ i := by
  induction m generalizing i with
  | zero => exact le_refl i
  | succ m ih =>
      rw [Function.iterate_succ_apply]
      exact le_trans (ih (f i)) (hf i)

/-- A positive iterate introduces no additional fixed points for a causal route. -/
theorem iterate_fixed_iff {m : ℕ} (hm : 0 < m) (i : Fin n) :
    f^[m] i = i ↔ f i = i := by
  constructor
  · intro hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    have hle : f^[j + 1] i ≤ f i := by
      rw [Function.iterate_succ_apply]
      exact iterate_le_self f hf j (f i)
    rw [hi] at hle
    exact le_antisymm (hf i) hle
  · intro hi
    exact Function.iterate_fixed hi m

/-- Until fixed, the natural-number rank pays for every iteration step. -/
lemma iterate_fixed_or_rank_bound (m : ℕ) (i : Fin n) :
    f (f^[m] i) = f^[m] i ∨ (f^[m] i).val + m ≤ i.val := by
  induction m with
  | zero => right; simp only [Function.iterate_zero_apply, Nat.add_zero, le_refl]
  | succ m ih =>
      by_cases hfix : f (f^[m] i) = f^[m] i
      · left
        simp only [Function.iterate_succ_apply', hfix]
      · right
        have hb := ih.resolve_left hfix
        have hle : (f (f^[m] i)).val ≤ (f^[m] i).val := hf (f^[m] i)
        have hne : (f (f^[m] i)).val ≠ (f^[m] i).val := by
          intro he
          exact hfix (Fin.ext he)
        rw [Function.iterate_succ_apply']
        omega

/-- At most `n` steps suffice for every causal route on `Fin n`. -/
theorem iterate_n_fixed (i : Fin n) : f (f^[n] i) = f^[n] i := by
  rcases iterate_fixed_or_rank_bound f hf n i with hfix | hb
  · exact hfix
  · have hi := i.isLt
    omega

theorem iterate_n_succ : f^[n + 1] = f^[n] := by
  funext i
  rw [Function.iterate_succ_apply']
  exact iterate_n_fixed f hf i

/-- The entire route-function tail stabilizes, not just one consecutive pair. -/
theorem iterate_n_add (t : ℕ) : f^[n + t] = f^[n] := by
  funext i
  rw [Nat.add_comm n t, Function.iterate_add_apply]
  exact Function.iterate_fixed (iterate_n_fixed f hf i) t

end InfoGeometry.Routing.CausalRouteDynamics

namespace InfoGeometry.Routing.AttentionPolytope

open DeterministicArgmaxAttention
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Routing.CausalRouteDynamics

variable {n : ℕ} (f : Fin n → Fin n)

/-- Matrix powers implement route iteration, with the native composition convention. -/
theorem deterministic_pow (m : ℕ) :
    deterministicAttention f ^ m = deterministicAttention (f^[m]) := by
  induction m with
  | zero => simpa only [pow_zero, Function.iterate_zero] using (deterministic_id (n := n)).symm
  | succ m ih =>
      rw [pow_succ, ih, deterministic_mul, ← Function.iterate_succ']

variable (hf : ∀ i, f i ≤ i)
include hf

theorem causal_deterministic_pow_stabilizes :
    deterministicAttention f ^ (n + 1) = deterministicAttention f ^ n := by
  rw [deterministic_pow, deterministic_pow, iterate_n_succ f hf]

theorem causal_deterministic_pow_tail (t : ℕ) :
    deterministicAttention f ^ (n + t) = deterministicAttention f ^ n := by
  exact pow_add_eq_of_stabilized (causal_deterministic_pow_stabilizes f hf) t

/-- The eventual routing matrix itself supplies the native Drazin inverse. -/
theorem causal_deterministic_drazin :
    IsDrazinInverse (deterministicAttention f) (deterministicAttention f ^ n) n := by
  exact of_stabilized_power (causal_deterministic_pow_stabilizes f hf)

theorem causal_deterministic_projection :
    projection (deterministicAttention f) (deterministicAttention f ^ n) =
      deterministicAttention f ^ n := by
  exact projection_of_stabilized_power (causal_deterministic_pow_stabilizes f hf)

theorem causal_deterministic_core :
    core (deterministicAttention f) (deterministicAttention f ^ n) =
      deterministicAttention f ^ n := by
  exact core_of_stabilized_power (causal_deterministic_pow_stabilizes f hf)

end InfoGeometry.Routing.AttentionPolytope
