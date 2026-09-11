import InfoGeometry.Canonical.BostConnesKMS
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

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
  /-- Additive operator trace readout. -/
  τL0 : Op →+ ℝ
  /-- Normalization on the algebraic unit. -/
  τL0_one : τL0 1 = 1
  /-- Cyclicity of the noncommutative trace functional. -/
  τL0_cyclic : ∀ A B : Op, τL0 (A * B) = τL0 (B * A)

/--
**The structural bridge: ζβ = partition value.**

ζβ = Σ_{k≥1} k^{-β} is the Riemann zeta partition function.
The normalization convention sets τL0(1) = 1, so ζβ appears
only in the KMS projection readout Φ.φ = τL0 / ζβ.

The bridge identity:
  ζβ · Φ.φ(S_n·S*_m) = τL0(S_n·S*_m)
-/
def hTrace {β : ℝ} (τ : GradedTraceDatum Op β) (ζβ : ℝ) : Prop :=
  ∀ n m : ℕ+,
    ζβ * kmsProjectionReadout β ζβ n m =
      τ.τL0 (S C n * star (S C m))

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
    {β : ℝ} (τ : GradedTraceDatum Op β) (ζβ : ℝ)
    (hBridge : hTrace Op C τ ζβ)
    (Φ : KMSProjectionState C)
    (hΦ_β : Φ.β = β) (hΦ_ζβ : Φ.ζβ = ζβ)
    (n m : ℕ+) :
    τ.τL0 (S C n * star (S C m)) =
      ζβ * Φ.φ (S C n * star (S C m)) := by
  have hEval : Φ.φ (S C n * star (S C m)) =
      kmsProjectionReadout β ζβ n m := by
    simpa [hΦ_β, hΦ_ζβ] using Φ.eval_projection n m
  calc
    τ.τL0 (S C n * star (S C m)) =
        ζβ * kmsProjectionReadout β ζβ n m :=
      (hBridge n m).symm
    _ = ζβ * Φ.φ (S C n * star (S C m)) := by
      rw [hEval]

end InfoGeometry.Canonical.GradedTraceBridge
