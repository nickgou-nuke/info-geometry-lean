import InfoGeometry.AsanoRuelle.TopologicalEndpoint
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Bornology.BoundedOperation
import InfoGeometry.Canonical.LeeYangAsanoNativeCore

/-!
# Möbius pole blow-up for the nondegenerate Asano branch

This owner isolates the analytic ingredient needed by the remaining Asano
endpoint argument.  The fractional-linear root tends to the cobounded filter
as the left denominator pole is approached through nonzero increments.

It does not assert the endpoint absorption theorem itself: boundedness of the
target set and zero-freeness still have to be combined with this filter fact.
-/

noncomputable section

open scoped Topology
open Filter
open Pointwise Bornology

namespace InfoGeometry.AsanoRuelle

open InfoGeometry.Canonical.LeeYangAsanoNativeCore

/-! ## Multiplicative scale coordinates at the pole -/

/-- Affine dilation about a chosen centre. -/
def poleScale (p : ℂ) (lam : ℝ) (z : ℂ) : ℂ :=
  p + (lam : ℂ) * (z - p)

@[simp] theorem poleScale_one (p z : ℂ) :
    poleScale p 1 z = z := by
  simp [poleScale]

@[simp] theorem poleScale_fixed (p : ℂ) (lam : ℝ) :
    poleScale p lam p = p := by
  simp [poleScale]

theorem poleScale_mul (p z : ℂ) (lam mu : ℝ) :
    poleScale p lam (poleScale p mu z) = poleScale p (lam * mu) z := by
  simp only [poleScale, Complex.ofReal_mul]
  ring

@[simp] theorem poleScale_zero (p z : ℂ) :
    poleScale p 0 z = p := by
  simp [poleScale]

theorem poleScale_inv (p z : ℂ) {lam : ℝ} (hlam : lam ≠ 0) :
    poleScale p lam⁻¹ (poleScale p lam z) = z := by
  rw [poleScale_mul]
  simp [hlam]

/-- The point at scale `λ` in direction `v` from the Möbius pole `-C / D`. -/
def poleScalePoint (C D : ℂ) (lam : ℝ) (v : ℂ) : ℂ :=
  -(C / D) + (lam : ℂ) * v

/-- The exact pole-coordinate identity for a fractional-linear map. -/
theorem mobius_pole_identity
    (A B C D ε : ℂ) (hD : D ≠ 0) (hε : ε ≠ 0) :
    -(A + B * (-C / D + ε)) /
        (C + D * (-C / D + ε)) =
      -(A * D - B * C) / (D ^ 2 * ε) - B / D := by
  field_simp [hD, hε]
  ring

theorem poleScalePoint_mul_direction
    (C D : ℂ) (lam mu : ℝ) (v : ℂ) :
    poleScalePoint C D lam ((mu : ℂ) * v) =
      poleScalePoint C D (lam * mu) v := by
  simp only [poleScalePoint, Complex.ofReal_mul]
  ring

theorem poleScalePoint_one (C D v : ℂ) :
    poleScalePoint C D 1 v = -(C / D) + v := by
  norm_num [poleScalePoint]

theorem poleScalePoint_sub_pole (C D : ℂ) (lam : ℝ) (v : ℂ) :
    poleScalePoint C D lam v - (-(C / D)) = (lam : ℂ) * v := by
  simp only [poleScalePoint, neg_div]
  abel

theorem norm_poleScalePoint_sub_pole
    (C D : ℂ) {lam : ℝ} (hlam : 0 ≤ lam) (v : ℂ) :
    ‖poleScalePoint C D lam v - (-(C / D))‖ = lam * ‖v‖ := by
  rw [poleScalePoint_sub_pole, norm_mul]
  simp [Complex.norm_real, abs_of_nonneg hlam]

theorem mobiusRoot_at_poleScale
    (A B C D : ℂ) (lam : ℝ) (v : ℂ)
    (hD : D ≠ 0)
    (hlam : (lam : ℂ) ≠ 0)
    (hv : v ≠ 0) :
    -(A + B * poleScalePoint C D lam v) /
        (C + D * poleScalePoint C D lam v) =
      -(A * D - B * C) / (D ^ 2 * (lam : ℂ) * v) - B / D := by
  simpa [poleScalePoint, neg_div, mul_assoc] using
    (mobius_pole_identity A B C D ((lam : ℂ) * v) hD
      (mul_ne_zero hlam hv))

theorem mobiusRoot_at_poleScale_inverse_scale
    (A B C D : ℂ) (lam : ℝ) (v : ℂ)
    (hD : D ≠ 0)
    (hlam : (lam : ℂ) ≠ 0)
    (hv : v ≠ 0) :
    -(A + B * poleScalePoint C D lam v) /
        (C + D * poleScalePoint C D lam v) =
      (lam : ℂ)⁻¹ *
          (-(A * D - B * C) / (D ^ 2 * v)) - B / D := by
  rw [mobiusRoot_at_poleScale A B C D lam v hD hlam hv]
  field_simp [hlam, hD, hv]

theorem poleBlowupCoefficient_ne_zero
    (A B C D v : ℂ)
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0)
    (hv : v ≠ 0) :
    -(A * D - B * C) / (D ^ 2 * v) ≠ 0 := by
  exact div_ne_zero (neg_ne_zero.mpr hdet)
    (mul_ne_zero (pow_ne_zero 2 hD) hv)

/-- The Möbius root evaluated at the left pole plus an increment. -/
def mobiusPolePath (A B C D ε : ℂ) : ℂ :=
  -(A + B * (-C / D + ε)) / (C + D * (-C / D + ε))

theorem mobiusPolePath_scale_transport
    (A B C D : ℂ) (lam : ℝ) (v : ℂ)
    (hD : D ≠ 0)
    (hlam : (lam : ℂ) ≠ 0)
    (hv : v ≠ 0) :
    mobiusPolePath A B C D ((lam : ℂ) * v) =
      (lam : ℂ)⁻¹ *
          (-(A * D - B * C) / (D ^ 2 * v)) - B / D := by
  unfold mobiusPolePath
  rw [mobius_pole_identity A B C D ((lam : ℂ) * v) hD
    (mul_ne_zero hlam hv)]
  field_simp [hlam, hD, hv]

/-- Nonzero determinant forces the Möbius root to escape every bounded set at
the denominator pole. -/
theorem mobiusPolePath_tendsto_cobounded
    (A B C D : ℂ)
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0) :
    Tendsto (mobiusPolePath A B C D) (𝓝[≠] 0) (Bornology.cobounded ℂ) := by
  have hcoef : -(A * D - B * C) / D ^ 2 ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hdet) (pow_ne_zero 2 hD)
  have hinv : Tendsto (fun ε : ℂ => ε⁻¹) (𝓝[≠] 0)
      (Bornology.cobounded ℂ) := tendsto_inv₀_nhdsNE_zero
  have hmul : Tendsto
      (fun ε : ℂ => (-(A * D - B * C) / D ^ 2) * ε⁻¹)
      (𝓝[≠] 0) (Bornology.cobounded ℂ) :=
    (tendsto_mul_left_cobounded hcoef).comp hinv
  have hadd : Tendsto
      (fun ε : ℂ => (-(A * D - B * C) / D ^ 2) * ε⁻¹ - B / D)
      (𝓝[≠] 0) (Bornology.cobounded ℂ) := by
    simpa [Function.comp_def, sub_eq_add_neg, neg_div] using
      (tendsto_add_const_cobounded (-B / D)).comp hmul
  refine hadd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := by simpa using hε
  rw [mobiusPolePath, mobius_pole_identity A B C D ε hD hε0]
  field_simp [hD, hε0]

/-! A bounded target cannot contain this pole path on a punctured
neighborhood.  This is the boundedness half of the endpoint argument; the
zero-free hypothesis is deliberately not folded into this lemma. -/

theorem mobiusPolePath_not_eventually_mem_bounded
    (A B C D : ℂ)
    (hD : D ≠ 0)
    (hdet : A * D - B * C ≠ 0)
    {K : Set ℂ}
    (hK_bdd : Bornology.IsBounded K) :
    ¬ (∀ᶠ ε in 𝓝[≠] 0, mobiusPolePath A B C D ε ∈ K) := by
  letI : NeBot (𝓝[≠] (0 : ℂ)) := inferInstance
  intro hmem
  have hcompl : Kᶜ ∈ Bornology.cobounded ℂ :=
    Bornology.isBounded_def.mp hK_bdd
  have hescape : ∀ᶠ ε in 𝓝[≠] 0,
      mobiusPolePath A B C D ε ∈ Kᶜ :=
    (mobiusPolePath_tendsto_cobounded A B C D hD hdet).eventually hcompl
  rcases (hmem.and hescape).exists with ⟨ε, hεK, hεKc⟩
  exact hεKc hεK

end InfoGeometry.AsanoRuelle
