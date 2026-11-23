/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Canonical.SouriauMetriplecticAttentionCasimirPoset

/-!
# Gradient (steepest-ascent) structure of the Brockett–Souriau dissipation

Carrier: an arbitrary noncommutative ring `B`; for the Cauchy–Schwarz part a star `ℝ`-algebra
with an `ℝ`-linear cyclic functional `τ` that is real (`τ (X⋆) = τ X`) and positive.

Tangent directions to the (inner) isospectral orbit through `W` are the inner derivations
`[K, W]`. The first-order rate of the Lyapunov function `τ (W H)` in direction `[K, W]` is

  `τ ([K, W] H) = τ (K [W, H]) = ⟨K*, K⟩`,  where `K* = [H, W]` and `⟨X, Y⟩ = τ (X⋆ Y)`.

* `orbit_rate_eq` – the rate identity `τ ([K, W] H) = τ (K [W, H])` (cyclicity only).
* `brockett_flow_eq_orbit` – the dissipative term is the orbit direction of `K* = [H, W]`:
  `dW = [Ω, W] + [K*, W]`.
* `orbit_rate_eq_pairing` – for self-adjoint `W, H`: rate `= ⟨K*, K⟩`.
* `pairing_cauchy_schwarz` – `⟨X, Y⟩² ≤ ⟨X, X⟩ ⟨Y, Y⟩`.
* `brockett_steepest_ascent` – `rate(K)² ≤ ⟨K, K⟩ ⟨K*, K*⟩` and `rate(K*) = ⟨K*, K*⟩`:
  among generators of equal `⟨·,·⟩`-length, `K*` maximises the Lyapunov rate.
-/

namespace SouriauMetriplecticAttentionCasimirPoset.Gradient

section RingLevel

variable {B : Type*} [Ring B] {R : Type*} [CommRing R]

/-- Rate of `τ (W H)` along the orbit direction `[K, W]`. -/
theorem orbit_rate_eq (τ : B →+ R) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x)) (K W H : B) :
    τ (comm K W * H) = τ (K * comm W H) := by
  simp only [comm, sub_mul, mul_sub, map_sub, mul_assoc]
  rw [h_cyc W (K * H), mul_assoc]

/-- The double bracket is an orbit direction: `[W, [W, H]] = [[H, W], W]`. -/
lemma dissipative_term_eq_orbit (W H : B) : comm W (comm W H) = comm (comm H W) W := by
  simp only [comm]
  noncomm_ring

/-- The Brockett–Souriau flow is the orbit direction of `Ω + [H, W]`. -/
theorem brockett_flow_eq_orbit (Ω H W : B) :
    brockettSouriauWeightFlow Ω H W = comm Ω W + comm (comm H W) W := by
  rw [brockettSouriauWeightFlow, dissipative_term_eq_orbit]

/-- For self-adjoint `W, H` the orbit rate is the pairing with `K* = [H, W]`. -/
theorem orbit_rate_eq_pairing [StarRing B] (τ : B →+ R)
    (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x)) {W H : B}
    (hW : star W = W) (hH : star H = H) (K : B) :
    τ (comm K W * H) = τ (star (comm H W) * K) := by
  have hs : star (comm H W) = comm W H := by
    simp only [comm, star_sub, star_mul, hW, hH]
  rw [orbit_rate_eq τ h_cyc, hs, h_cyc]

end RingLevel

section RealStar

variable {B : Type*} [Ring B] [Algebra ℝ B] [StarRing B] [StarModule ℝ B]

/-- Cauchy–Schwarz for the trace pairing `⟨X, Y⟩ = τ (X⋆ Y)` of a real positive functional. -/
theorem pairing_cauchy_schwarz (τ : B →ₗ[ℝ] ℝ) (hτs : ∀ X : B, τ (star X) = τ X)
    (hpos : ∀ Y : B, 0 ≤ τ (star Y * Y)) (X Y : B) :
    τ (star X * Y) ^ 2 ≤ τ (star X * X) * τ (star Y * Y) := by
  have hsym : τ (star Y * X) = τ (star X * Y) := by
    rw [← hτs (star X * Y), star_mul, star_star]
  have hq : ∀ x : ℝ,
      0 ≤ τ (star Y * Y) * (x * x) + (2 * τ (star X * Y)) * x + τ (star X * X) := by
    intro x
    have h := hpos (X + x • Y)
    simp only [star_add, star_smul, star_trivial, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, map_add, map_smul, smul_eq_mul, hsym] at h
    nlinarith [h]
  have hd := discrim_le_zero hq
  simp only [discrim] at hd
  nlinarith [hd]

/-- **Steepest ascent**: for self-adjoint `W, H`, every orbit generator `K` satisfies
`τ ([K, W] H)² ≤ ⟨K, K⟩ ⟨K*, K*⟩` with `K* = [H, W]`, and `K*` attains
`τ ([K*, W] H) = ⟨K*, K*⟩`. Hence the dissipative term `[W, [W, H]] = [K*, W]` is the
direction of maximal increase of `τ (W H)` among generators of the same length. -/
theorem brockett_steepest_ascent (τ : B →ₗ[ℝ] ℝ)
    (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x)) (hτs : ∀ X : B, τ (star X) = τ X)
    (hpos : ∀ Y : B, 0 ≤ τ (star Y * Y)) {W H : B}
    (hW : star W = W) (hH : star H = H) (K : B) :
    τ (comm K W * H) ^ 2 ≤ τ (star K * K) * τ (star (comm H W) * comm H W) ∧
    τ (comm (comm H W) W * H) = τ (star (comm H W) * comm H W) := by
  have hrate : ∀ K' : B, τ (comm K' W * H) = τ (star (comm H W) * K') :=
    orbit_rate_eq_pairing τ.toAddMonoidHom h_cyc hW hH
  refine ⟨?_, hrate _⟩
  rw [hrate, mul_comm]
  exact pairing_cauchy_schwarz τ hτs hpos (comm H W) K

end RealStar

end SouriauMetriplecticAttentionCasimirPoset.Gradient
