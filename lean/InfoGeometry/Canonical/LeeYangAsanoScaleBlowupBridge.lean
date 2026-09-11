import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.LeeYangAsanoNativeCore

/-!
# Affine scale blow-up for the nondegenerate Asano root map

This owner isolates the exact algebraic scale calculation at a Möbius pole.
For `p = -C / D`, the map

`z ↦ p + λ (z - p)`

is a multiplicative positive-real dilation about `p`.  Substitution into the
Asano root map gives an explicit inverse-scale term.  No topology, limit,
compactification, or Weyl-gauge interpretation is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangAsanoScaleBlowupBridge

open InfoGeometry.Canonical.LeeYangAsanoNativeCore

/-! ## The affine dilation action about the pole -/

def poleScale (C D : ℂ) (lam : ℝ) (z : ℂ) : ℂ :=
  -(C / D) + (lam : ℂ) * (z + C / D)

def poleScalePoint (C D : ℂ) (lam : ℝ) (v : ℂ) : ℂ :=
  -(C / D) + (lam : ℂ) * v

theorem poleScale_eq_poleScalePoint (C D : ℂ) (lam : ℝ) (v : ℂ) :
    poleScale C D lam (poleScalePoint C D 1 v) =
      poleScalePoint C D lam v := by
  simp [poleScale, poleScalePoint]

theorem poleScale_one (C D z : ℂ) :
    poleScale C D 1 z = z := by
  simp [poleScale]

theorem poleScale_fixed (C D : ℂ) (lam : ℝ) :
    poleScale C D lam (-(C / D)) = -(C / D) := by
  simp [poleScale]

theorem poleScale_mul (C D : ℂ) (lam mu : ℝ) (z : ℂ) :
    poleScale C D (lam * mu) z =
      poleScale C D lam (poleScale C D mu z) := by
  simp only [poleScale]
  push_cast
  ring

theorem poleScale_inv
    {C D z : ℂ} {lam : ℝ} (hlam : lam ≠ 0) :
    poleScale C D lam⁻¹ (poleScale C D lam z) = z := by
  simpa [inv_mul_cancel₀ hlam, poleScale_one] using
    (poleScale_mul C D lam⁻¹ lam z).symm

theorem poleScale_denominator
    {C D v : ℂ} {lam : ℝ} (hD : D ≠ 0) :
    C + D * poleScalePoint C D lam v =
      (lam : ℂ) * D * v := by
  unfold poleScalePoint
  field_simp [hD]
  ring

theorem poleScalePoint_ne_pole
    {C D v : ℂ} {lam : ℝ}
    (hv : v ≠ 0) (hlam : lam ≠ 0) :
    poleScalePoint C D lam v ≠ -(C / D) := by
  intro h
  simp only [poleScalePoint] at h
  have hmul : (lam : ℂ) * v = 0 := by
    calc
      (lam : ℂ) * v = (-(C / D) + (lam : ℂ) * v) - (-(C / D)) := by ring
      _ = (-(C / D)) - (-(C / D)) := by rw [h]
      _ = 0 := by ring
  exact hv (by
    apply (mul_eq_zero.mp hmul).resolve_left
    exact_mod_cast hlam)

/-! ## Exact inverse-scale root readout -/

theorem asanoRootMap_poleScale
    {A B C D v : ℂ} {lam : ℝ}
    (hD : D ≠ 0) (hv : v ≠ 0) (hlam : lam ≠ 0) :
    asanoRootMap A B C D (poleScalePoint C D lam v) =
      -((A * D - B * C) /
        (D ^ 2 * (lam : ℂ) * v)) - B / D := by
  unfold asanoRootMap poleScalePoint
  have hlamC : (lam : ℂ) ≠ 0 := by
    exact_mod_cast hlam
  field_simp [hD, hv, hlamC]
  ring

theorem asanoRootMap_poleScale_eq_inverseScale
    {A B C D v : ℂ} {lam : ℝ}
    (hD : D ≠ 0) (hv : v ≠ 0) (hlam : lam ≠ 0) :
    asanoRootMap A B C D (poleScalePoint C D lam v) =
      (-(A * D - B * C) / (D ^ 2 * v)) / (lam : ℂ) - B / D := by
  rw [asanoRootMap_poleScale hD hv hlam]
  field_simp [hD, hv]

theorem asanoRootMap_poleScale_coefficient_ne_zero
    {A B C D v : ℂ}
    (hD : D ≠ 0) (hv : v ≠ 0)
    (hNondeg : A * D - B * C ≠ 0) :
    -(A * D - B * C) / (D ^ 2 * v) ≠ 0 := by
  apply div_ne_zero
  · exact neg_ne_zero.mpr hNondeg
  · exact mul_ne_zero (pow_ne_zero 2 hD) hv

end InfoGeometry.Canonical.LeeYangAsanoScaleBlowupBridge
