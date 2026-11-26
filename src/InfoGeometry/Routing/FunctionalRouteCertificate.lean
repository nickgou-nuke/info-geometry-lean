/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.FunctionalRouteCore

/-!
# Local finite-route certificates

Local finite graph data and local recurrence equations suffice; no Drazin law
or assumed eventual-entry theorem is used. Rank descent proves the exact
entry time. The existing synchronized-retraction owner then gives a Drazin
witness, and the matrix power equation proves minimality when the bound is
attained. A Python exporter supplies concrete data; Lean checks the local
finite equations by kernel reduction. This is not a proof of Kahn's algorithm.
-/
namespace InfoGeometry.Routing.FunctionalRouteCertificate

open Matrix DeterministicArgmaxAttention
open InfoGeometry.Routing.AttentionPolytope
open InfoGeometry.Routing.FunctionalRouteCore
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse

variable {n c : ℕ}

variable {f : Fin n → Fin n} {embed : Fin c → Fin n}
variable {sigma : Equiv.Perm (Fin c)} {rho : Fin n → Fin c} {depth : Fin n → ℕ}

/-- A single transition decreases positive depth by one and preserves zero. -/
theorem depth_next
    (h_cycle : ∀ j, f (embed j) = embed (sigma j))
    (h_core_depth : ∀ j, depth (embed j) = 0)
    (h_zero_depth : ∀ i, depth i = 0 → ∃ j, i = embed j)
    (h_descent : ∀ i, 0 < depth i → depth (f i) + 1 = depth i)
    (i : Fin n) : depth (f i) = depth i - 1 := by
  by_cases hi : depth i = 0
  · obtain ⟨j, rfl⟩ := h_zero_depth i hi
    rw [h_cycle, h_core_depth, h_core_depth]
  · have hs := h_descent i (by omega)
    omega

theorem iterate_depth
    (h_cycle : ∀ j, f (embed j) = embed (sigma j))
    (h_core_depth : ∀ j, depth (embed j) = 0)
    (h_zero_depth : ∀ i, depth i = 0 → ∃ j, i = embed j)
    (h_descent : ∀ i, 0 < depth i → depth (f i) + 1 = depth i)
    (r : ℕ) (i : Fin n) : depth (f^[r] i) = depth i - r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', depth_next h_cycle h_core_depth h_zero_depth h_descent, ih]
      omega

/-- Exact first entry, derived from local equations rather than assumed. -/
theorem recurrent_entry_iff
    (h_cycle : ∀ j, f (embed j) = embed (sigma j))
    (h_core_depth : ∀ j, depth (embed j) = 0)
    (h_zero_depth : ∀ i, depth i = 0 → ∃ j, i = embed j)
    (h_descent : ∀ i, 0 < depth i → depth (f i) + 1 = depth i)
    (r : ℕ) (i : Fin n) : (∃ j, f^[r] i = embed j) ↔ depth i ≤ r := by
  constructor
  · rintro ⟨j, hj⟩
    have hz : depth (f^[r] i) = 0 := by rw [hj, h_core_depth]
    rw [iterate_depth h_cycle h_core_depth h_zero_depth h_descent] at hz
    omega
  · intro hi
    apply h_zero_depth
    rw [iterate_depth h_cycle h_core_depth h_zero_depth h_descent]
    omega

/-- The original Drazin owner consumes the derived eventual-entry condition. -/
theorem certified_drazin
    (h_retract : ∀ j, rho (embed j) = j)
    (h_cycle : ∀ j, f (embed j) = embed (sigma j))
    (h_sync : ∀ i, rho (f i) = sigma (rho i))
    (h_core_depth : ∀ j, depth (embed j) = 0)
    (h_zero_depth : ∀ i, depth i = 0 → ∃ j, i = embed j)
    (h_descent : ∀ i, 0 < depth i → depth (f i) + 1 = depth i)
    (k : ℕ) (hk : ∀ i, depth i ≤ k) :
    IsDrazinInverse (deterministicAttention f)
      (deterministicAttention (inverseRoute embed sigma rho)) k := by
  exact drazin_of_synchronized_retraction f embed sigma rho k
    h_retract h_cycle h_sync
    (fun i => (recurrent_entry_iff h_cycle h_core_depth h_zero_depth h_descent k i).mpr (hk i))

/-- The deterministic matrix representation distinguishes all route functions. -/
theorem routing_representation_injective {p q : ℕ} :
    Function.Injective (deterministicAttention (N := p) (M := q)) := by
  intro u v huv
  funext i
  by_contra hi
  have he := congrArg (fun A : Matrix (Fin p) (Fin q) ℝ => A i (u i)) huv
  simp [deterministicAttention, hi] at he

/-- For the certified inverse, the Drazin power equation is exactly the entry bound. -/
theorem power_equation_iff_depth_bound
    (h_retract : ∀ j, rho (embed j) = j)
    (h_cycle : ∀ j, f (embed j) = embed (sigma j))
    (h_sync : ∀ i, rho (f i) = sigma (rho i))
    (h_core_depth : ∀ j, depth (embed j) = 0)
    (h_zero_depth : ∀ i, depth i = 0 → ∃ j, i = embed j)
    (h_descent : ∀ i, 0 < depth i → depth (f i) + 1 = depth i)
    (r : ℕ) :
    deterministicAttention f ^ (r + 1) *
      deterministicAttention (inverseRoute embed sigma rho) =
      deterministicAttention f ^ r ↔ ∀ i, depth i ≤ r := by
  constructor
  · intro hp i
    rw [deterministic_pow, deterministic_pow, deterministic_mul] at hp
    have he := congrFun (routing_representation_injective hp) i
    have hpoint : embed (rho (f^[r] i)) = f^[r] i := by
      simpa only [Function.comp_apply, Function.iterate_succ_apply', inverseRoute,
        h_sync, Equiv.symm_apply_apply] using he
    exact (recurrent_entry_iff h_cycle h_core_depth h_zero_depth h_descent r i).mp ⟨rho (f^[r] i), hpoint.symm⟩
  · intro hr
    exact (certified_drazin h_retract h_cycle h_sync h_core_depth h_zero_depth h_descent r hr).power

/-- No exponent below a certified entry depth can be a Drazin witness. -/
theorem any_witness_depth_bound
    (h_retract : ∀ j, rho (embed j) = j)
    (h_cycle : ∀ j, f (embed j) = embed (sigma j))
    (h_sync : ∀ i, rho (f i) = sigma (rho i))
    (h_core_depth : ∀ j, depth (embed j) = 0)
    (h_zero_depth : ∀ i, depth i = 0 → ∃ j, i = embed j)
    (h_descent : ∀ i, 0 < depth i → depth (f i) + 1 = depth i)
    (k : ℕ) (hk : ∀ i, depth i ≤ k)
    {B : Matrix (Fin n) (Fin n) ℝ} {r : ℕ}
    (hB : IsDrazinInverse (deterministicAttention f) B r) :
    ∀ i, depth i ≤ r := by
  have hsame := unique_of_indices hB
    (certified_drazin h_retract h_cycle h_sync h_core_depth h_zero_depth h_descent k hk)
  have hp := hB.power
  rw [hsame] at hp
  exact (power_equation_iff_depth_bound h_retract h_cycle h_sync h_core_depth h_zero_depth h_descent r).mp hp

/-- An attained depth bound is the least possible Drazin witness exponent. -/
theorem minimum_witness_index
    (h_retract : ∀ j, rho (embed j) = j)
    (h_cycle : ∀ j, f (embed j) = embed (sigma j))
    (h_sync : ∀ i, rho (f i) = sigma (rho i))
    (h_core_depth : ∀ j, depth (embed j) = 0)
    (h_zero_depth : ∀ i, depth i = 0 → ∃ j, i = embed j)
    (h_descent : ∀ i, 0 < depth i → depth (f i) + 1 = depth i)
    (k : ℕ) (hk : ∀ i, depth i ≤ k) (hmax : ∃ i, depth i = k)
    {B : Matrix (Fin n) (Fin n) ℝ} {r : ℕ}
    (hB : IsDrazinInverse (deterministicAttention f) B r) : k ≤ r := by
  obtain ⟨i, hi⟩ := hmax
  have hb := any_witness_depth_bound
    h_retract h_cycle h_sync h_core_depth h_zero_depth h_descent k hk hB i
  simpa only [hi] using hb

end InfoGeometry.Routing.FunctionalRouteCertificate
