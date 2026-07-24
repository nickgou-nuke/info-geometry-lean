import InfoGeometry.Canonical.BostConnesKMS
import Mathlib

/-!
# Conditional Graded Trace Compatibility

The `hTrace` theorem derives a scalar normalization identity from the explicit
fields of `GradedTraceDatum`.  This file does not construct the Sugawara trace
or prove those fields for a concrete operator representation.

## Convention

  τL0(A) = normalized Sugawara graded trace = Tr(q^{L₀}·A) / Tr(q^{L₀})

Then:
  τL0(1) = 1
  τL0(S_n·S*_n) = n^{-β}    (L₀ shifted by log n)

The Bost-Connes KMS projection readout:
  Φ.φ(S_n·S*_m) = δ_{n,m}·n^{-β}/ζβ

where ζβ = Σ_k k^{-β} is the partition function.

The bridge: ζβ·Φ.φ = τL0. This is the structural identity.
-/

noncomputable section

namespace InfoGeometry.Canonical.GradedTraceBridge

open BostConnesKMS

variable (Op : Type*) [Ring Op] [StarRing Op]
variable (C : BostConnesCuntzSystem Op)

/--
**Normalized Sugawara graded trace datum.**

τL0(A) = Tr(q^{L₀}·A) / Tr(q^{L₀})

Properties:
  τL0(1) = 1                    (normalized)
  τL0(S_n·S*_n) = n^{-β}         (L₀ shift by log n)
  τL0(S_n·S*_m) = 0 for n ≠ m    (diagonal matrix-coefficient readout)
-/
structure GradedTraceDatum (β : ℝ) where
  τL0 : Op → ℝ
  τL0_one : τL0 1 = 1
  τL0_diag : ∀ n : ℕ+, τL0 (S C n * star (S C n)) = ((n : ℕ) : ℝ) ^ (-β)
  τL0_off_diag : ∀ n m : ℕ+, n ≠ m → τL0 (S C n * star (S C m)) = 0

/--
**The structural bridge: ζβ = partition value.**

ζβ = Σ_{k≥1} k^{-β} is the Riemann zeta partition function.
The normalization convention sets τL0(1) = 1, so ζβ appears
only in the KMS projection readout Φ.φ = τL0 / ζβ.

The bridge identity:
  ζβ · Φ.φ(S_n·S*_m) = τL0(S_n·S*_m)
-/
def hTrace (τ : GradedTraceDatum Op C β) (ζβ : ℝ) (hζβ_pos : 0 < ζβ) :
    ∀ n m : ℕ+, (ζβ * kmsProjectionReadout β ζβ n m) = τ.τL0 (S C n * star (S C m)) := by
  intro n m
  by_cases hnm : n = m
  · subst hnm
    have hζβ_ne : ζβ ≠ 0 := ne_of_gt hζβ_pos
    rw [kmsProjectionReadout_self, τ.τL0_diag]
    field_simp [hζβ_ne]
  · rw [kmsProjectionReadout_ne hnm, τ.τL0_off_diag n m hnm]
    simp

/--
**The bridge is immediate from the structure definitions.**

For the KMSProjectionState Φ with partition ζβ:
  Φ.φ = kmsProjectionReadout β ζβ

And GradedTraceDatum gives:
  τL0(S_n·S*_m) = n^{-β} (diagonal) or 0 (off-diagonal)

Recalling that:
  kmsProjectionReadout β ζβ n n = n^{-β}/ζβ

We have:
  Φ.φ(S_n·S*_n) = n^{-β}/ζβ
  τL0(S_n·S*_n) = n^{-β}

  ζβ · Φ.φ(S_n·S*_n) = ζβ · n^{-β}/ζβ = n^{-β} = τL0(S_n·S*_n)

And for n ≠ m both are 0.

This is NOT debt — it's the STRUCTURAL IDENTITY defining ζβ as the
ratio between the normalized τL0 and the KMS projection readout.
-/
theorem structural_bridge_is_identity
    (τ : GradedTraceDatum Op C β) (ζβ : ℝ) (hζβ_pos : 0 < ζβ) (Φ : KMSProjectionState C)
    (hΦ_β : Φ.β = β) (hΦ_ζβ : Φ.ζβ = ζβ)
    (n m : ℕ+) :
    τ.τL0 (S C n * star (S C m)) =
      ζβ * Φ.φ (S C n * star (S C m)) := by
  subst hΦ_β; subst hΦ_ζβ
  rw [Φ.eval_projection n m]
  exact (hTrace Op C τ Φ.ζβ hζβ_pos n m).symm

end InfoGeometry.Canonical.GradedTraceBridge
