/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import InfoGeometry.Thermodynamics.SouriauFoliation
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Differential.PoincareFisherRao
import InfoGeometry.Canonical.YangBaxterProof

namespace InfoGeometry.Thermodynamics.SouriauApolloniusFoliation

open Real Complex Matrix
open InfoGeometry.Thermodynamics.SouriauFoliation
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Differential.PoincareFisherRao
open InfoGeometry.Canonical.YangBaxterProof

noncomputable section

/-!
# Souriau Thermodynamic Foliation & Apollonius Entropy Leaves

We formalize the bridge connecting:
1. Souriau symplectic thermodynamic leaves and temperature affine forms.
2. The Möbius-Apollonius foliation parameterizing the critical line Re(s) = 1/2.
3. The Souriau entropy functional and its vanishing drift on the critical leaf.
4. The Fisher-Rao / Poincaré Riemannian metric on the leaf parameter space.
-/

/-- The Souriau affine temperature parameter derived from the Apollonius difference:
    β_Souriau(σ) = -4σ + 2. -/
def souriauApolloniusBeta (sigma : ℝ) : ℝ :=
  -4 * sigma + 2

/-- The Apollonian leaf carrier in the (σ, t) parameter space for ratio λ > 0. -/
def apolloniusLeafCarrier (lambda_ratio : ℝ) : Set (ℝ × ℝ) :=
  { p : ℝ × ℝ | apolloniusNumerator p.1 p.2 = lambda_ratio * apolloniusDenominator p.1 p.2 }

/-- 🏆 THEOREM 1: The Souriau temperature parameter vanishes identically on the critical line σ = 1/2. -/
theorem souriau_beta_zero_iff_critical_half (sigma : ℝ) :
    souriauApolloniusBeta sigma = 0 ↔ sigma = 1 / 2 := by
  unfold souriauApolloniusBeta
  constructor
  · intro h
    linarith
  · intro h
    subst h
    ring

/-- 🏆 THEOREM 2: The Souriau temperature parameter is strictly negative on the subharmonic disk domain σ > 1/2. -/
theorem souriau_beta_neg_iff_disk_domain (sigma : ℝ) :
    souriauApolloniusBeta sigma < 0 ↔ 1 / 2 < sigma := by
  unfold souriauApolloniusBeta
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- 🏆 THEOREM 3: The Souriau temperature parameter is strictly positive on the exterior domain σ < 1/2. -/
theorem souriau_beta_pos_iff_exterior_domain (sigma : ℝ) :
    0 < souriauApolloniusBeta sigma ↔ sigma < 1 / 2 := by
  unfold souriauApolloniusBeta
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- 🏆 THEOREM 4: The unitary Apollonius leaf (λ = 1) is the critical line σ = 1/2. -/
theorem unitary_apollonius_leaf_eq_critical_line (p : ℝ × ℝ) :
    p ∈ apolloniusLeafCarrier 1 ↔ p.1 = 1 / 2 := by
  unfold apolloniusLeafCarrier
  simp only [Set.mem_setOf_eq, one_mul]
  exact apollonius_unitary_level_set_iff p.1 p.2

/-- A concrete Souriau Symplectic Leaf on the critical line σ = 1/2. -/
def criticalLineSouriauLeaf : SymplecticLeaf (ℝ × ℝ) where
  carrier := { p : ℝ × ℝ | p.1 = 1 / 2 }
  entropyReadout := fun p => souriauApolloniusBeta p.1
  weylScaleReadout := fun p => apolloniusNumerator p.1 p.2 - apolloniusDenominator p.1 p.2
  leafEntropy := 0
  leafWeylScale := 0
  entropy_constant := by
    intro p hp
    dsimp [souriauApolloniusBeta]
    have hp_half : p.1 = 1 / 2 := hp
    rw [hp_half]
    ring
  weylScale_constant := by
    intro p hp
    have hp_half : p.1 = 1 / 2 := hp
    rw [apollonius_difference p.1 p.2, hp_half]
    ring

/-- 🏆 GRAND CAPSTONE THEOREM: Full Synthesis of Souriau Foliation, Apollonius Leaves & Poincaré Geometry -/
theorem grand_souriau_apollonius_foliation_synthesis
    (sigma t : ℝ) (p_point : UpperHalfPlanePoint) (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    (souriauApolloniusBeta (1 / 2) = 0) ∧
    (souriauApolloniusBeta sigma = 0 ↔ sigma = 1 / 2) ∧
    (apolloniusNumerator sigma t - apolloniusDenominator sigma t = -4 * sigma + 2) ∧
    (apolloniusNumerator sigma t = apolloniusDenominator sigma t ↔ sigma = 1 / 2) ∧
    (fisherMetricMatrix p_point 0 0 = 1 / p_point.y ^ 2) ∧
    ((fisherMetricMatrix p_point).det = 1 / p_point.y ^ 4) ∧
    (0 < dotProduct (mulVec (fisherMetricMatrix p_point) v) v) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨by unfold souriauApolloniusBeta; ring,
   souriau_beta_zero_iff_critical_half sigma,
   apollonius_difference sigma t,
   apollonius_unitary_level_set_iff sigma t,
   rfl,
   fisher_metric_det p_point,
   fisher_metric_pos_def p_point v hv,
   F_sq,
   F_B_F_eq_R⟩

end

end InfoGeometry.Thermodynamics.SouriauApolloniusFoliation
