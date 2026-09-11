import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.AsanoRuelle.MobiusPoleScaleAction
import InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint
import InfoGeometry.Canonical.LeeYangAsanoEndpointNative
import InfoGeometry.Canonical.LeeYangAsanoScaleBlowupBridge
import InfoGeometry.Canonical.LeeYangAsanoScaleBoundedEscapeBridge
import InfoGeometry.Stratum.Gauge

/-!
# Metric neighborhoods for the Asano pole scale

This owner packages the concrete source neighborhoods used by the explicit
scale argument.  It proves only metric-ball nesting and membership of a
scaled point.  It does not introduce a categorical colimit, a projective
compactification, or a Weyl-gauge action.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangAsanoScaleNeighborhood

open InfoGeometry.Canonical.LeeYangAsanoScaleBlowupBridge
open InfoGeometry.Canonical.LeeYangAsanoScaleBoundedEscapeBridge
open InfoGeometry.Canonical.LeeYangAsanoNativeCore

noncomputable def posGaugeToRealUnits :
    InfoGeometry.Stratum.PosGauge →* ℝˣ where
  toFun c := Units.mk0 c.1 c.property.ne'
  map_one' := by
    apply Units.ext
    rfl
  map_mul' a b := by
    apply Units.ext
    rfl

noncomputable def posGaugePoleScaleAction (C D : ℂ) :
    InfoGeometry.Stratum.PosGauge →* Equiv.Perm ℂ :=
  (InfoGeometry.AsanoRuelle.poleScaleAction (-(C / D))).comp
    posGaugeToRealUnits

@[simp] theorem posGaugePoleScaleAction_apply
    (C D : ℂ) (c : InfoGeometry.Stratum.PosGauge) (z : ℂ) :
    posGaugePoleScaleAction C D c z =
      InfoGeometry.AsanoRuelle.poleScale
        (-(C / D)) c.1 z := by
  rfl

theorem posGaugePoleScaleAction_polePoint
    (C D : ℂ) (c : InfoGeometry.Stratum.PosGauge) (v : ℂ) :
    posGaugePoleScaleAction C D c (-(C / D) + v) =
      InfoGeometry.Canonical.LeeYangAsanoScaleBlowupBridge.poleScalePoint
        C D c.1 v := by
  simpa [posGaugePoleScaleAction, posGaugeToRealUnits] using
    (InfoGeometry.AsanoRuelle.poleScaleAction_polePoint
      C D (posGaugeToRealUnits c) v)

/-- The radius-`delta` source neighborhood around the Möbius pole. -/
def poleScaleNeighborhood (C D : ℂ) (delta : ℝ) : Set ℂ :=
  Metric.ball (-(C / D)) delta

theorem poleScaleNeighborhood_subset
    {C D : ℂ} {delta₁ delta₂ : ℝ} (hdelta : delta₁ ≤ delta₂) :
    poleScaleNeighborhood C D delta₁ ⊆
      poleScaleNeighborhood C D delta₂ := by
  intro z hz
  exact Metric.ball_subset_ball hdelta hz

theorem poleScalePoint_mem_poleScaleNeighborhood
    {C D v : ℂ} {lam delta : ℝ}
    (hlam : 0 < lam) (hlamdelta : lam < delta)
    (hv : ‖v‖ = 1) :
    poleScalePoint C D lam v ∈ poleScaleNeighborhood C D delta := by
  rw [poleScaleNeighborhood, Metric.mem_ball]
  rw [dist_eq_norm]
  simp [poleScalePoint, abs_of_pos hlam, hv]
  exact hlamdelta

theorem poleScalePoint_one_mem_poleScaleNeighborhood
    {C D : ℂ} {lam delta : ℝ}
    (hlam : 0 < lam) (hlamdelta : lam < delta) :
    poleScalePoint C D lam (1 : ℂ) ∈
      poleScaleNeighborhood C D delta := by
  exact poleScalePoint_mem_poleScaleNeighborhood hlam hlamdelta norm_one

theorem asanoRootMap_poleScaleAction_inverse_scale
    {A B C D v : ℂ} (lam : ℝˣ)
    (hD : D ≠ 0) (hv : v ≠ 0) :
    asanoRootMap A B C D
        (InfoGeometry.AsanoRuelle.poleScaleAction
          (-(C / D)) lam (-(C / D) + v)) =
      (-(A * D - B * C) / (D ^ 2 * v)) / (lam : ℂ) - B / D := by
  rw [InfoGeometry.AsanoRuelle.poleScaleAction_polePoint]
  exact asanoRootMap_poleScale_eq_inverseScale
    hD hv (by exact_mod_cast Units.ne_zero lam)

/-! ## Explicit-scale transport to the Asano endpoint API -/

theorem asano_endpoint_disjunction_left_of_explicit_scale
    (A B C D : ℂ) (K1 K2 : Set ℂ)
    (hD : D ≠ 0)
    (hNondeg : A * D - B * C ≠ 0)
    (hK1_closed : IsClosed K1)
    (hK2_bdd : Bornology.IsBounded K2)
    (hK1_no_zero : (0 : ℂ) ∉ K1)
    (h_zerofree : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 →
      A + B * z1 + C * z2 + D * z1 * z2 ≠ 0) :
    (C ≠ 0 ∧ -(C / D) ∈ K1) ∨ (B ≠ 0 ∧ -(B / D) ∈ K2) := by
  have hpole_raw : (-C / D) ∈ K1 :=
    asano_left_pole_in_K1_of_explicit_scale
      A B C D K1 K2 hD hNondeg hK1_closed hK2_bdd h_zerofree
  have hpole : -(C / D) ∈ K1 := by
    convert hpole_raw using 1 <;> ring
  exact Or.inl ⟨
    InfoGeometry.Canonical.AsanoRuelleTopologicalEndpoint.left_pole_nonzero
      C D K1 hK1_no_zero hpole_raw,
    hpole⟩

theorem asano_nondegenerate_root_mem_negProductSet_of_explicit_scale
    {K1 K2 : Set ℂ} {A B C D z : ℂ}
    (h0K1 : (0 : ℂ) ∉ K1)
    (h0K2 : (0 : ℂ) ∉ K2)
    (hD : D ≠ 0)
    (hK1_closed : IsClosed K1)
    (hK2_bdd : Bornology.IsBounded K2)
    (hNondeg : A * D - B * C ≠ 0)
    (hPhi : ∀ z1 z2 : ℂ, z1 ∉ K1 → z2 ∉ K2 →
      asanoPhi A B C D z1 z2 ≠ 0)
    (hroot : A + D * z = 0) :
    z ∈ negProductSet K1 K2 := by
  exact
    asano_nondegenerate_root_mem_negProductSet_of_endpoint
      h0K1 h0K2 hD hPhi hroot
      (asano_endpoint_disjunction_left_of_explicit_scale
        A B C D K1 K2 hD hNondeg hK1_closed hK2_bdd h0K1 hPhi)

end InfoGeometry.Canonical.LeeYangAsanoScaleNeighborhood
