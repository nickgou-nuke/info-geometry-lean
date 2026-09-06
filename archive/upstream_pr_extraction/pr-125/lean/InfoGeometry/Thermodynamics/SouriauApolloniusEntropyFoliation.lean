/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Thermodynamics.SouriauFoliation
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Differential.PoincareFisherRao
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Complex.MobiusApolloniusFoliation

namespace InfoGeometry.Thermodynamics.SouriauApolloniusFoliation

open Complex Real Matrix
open InfoGeometry.Thermodynamics.SouriauFoliation
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Differential.PoincareFisherRao
open InfoGeometry.Canonical.YangBaxterProof

local notation "normSq" => Complex.normSq

noncomputable section

/-!
# Souriau Lie Group Thermodynamics & Apollonius Entropy Foliation

This module formalizes Souriau Lie Group Thermodynamics on the Apollonian
complex plane $s = \sigma + i t \in \mathbb{C}$ with respect to the dipole
poles $z_0 = 3/2$ and $p_0 = -1/2$.

Key Formalized Structures:
1. **Apollonius Metric Ratio**:
   $$R(s) = \left|\frac{s - 3/2}{s + 1/2}\right|^2 = \frac{(\sigma - 3/2)^2 + t^2}{(\sigma + 1/2)^2 + t^2}$$
2. **Souriau Mass / Generalized Thermodynamic Potential**:
   $$\Phi(s) = -\frac{1}{2} \ln R(s) = \ln |s + 1/2| - \ln |s - 3/2|$$
3. **Entropy Foliation Leaves**:
   Level sets $\mathcal{L}_\lambda = \{s \in \mathbb{C} \mid R(s) = \lambda\}$.
   - $\lambda = 1$: Critical line $\sigma = 1/2$ (Isometric unitary leaf $\Phi = 0$).
   - $\lambda < 1$: Subharmonic disk leaves $\sigma > 1/2$ ($\Phi > 0$).
   - $\lambda > 1$: Exterior leaves $\sigma < 1/2$ ($\Phi < 0$).
4. **Souriau Covariant Heat Vector / Entropy 1-Form & Conformal Conjugation**:
   The gradient $\nabla \Phi$ generates the orthogonal trajectories of the
   Hamiltonian flow $H_{\mathrm{HP}}$, forming a dual Souriau foliation:
   $$\ln\left(\frac{s - 3/2}{s + 1/2}\right) = -\Phi(s) + i \cdot H_{\mathrm{HP}}(s)$$
-/

/-- Dipole zero / right focus z₀ = 3/2. -/
def dipoleZero : ℂ := ⟨3 / 2, 0⟩

/-- Dipole pole / left focus p₀ = -1/2. -/
def dipolePole : ℂ := ⟨-1 / 2, 0⟩

/-- Apollonius ratio: R(s) = |s - 3/2|² / |s + 1/2|². -/
def apolloniusRatio (s : ℂ) : ℝ :=
  Complex.normSq (s - dipoleZero) / Complex.normSq (s - dipolePole)

/-- The Souriau ratio is the squared modulus of the foundational Möbius map. -/
theorem apolloniusRatio_eq_normSq_mobiusMap (s : ℂ) :
    apolloniusRatio s =
      Complex.normSq
        (InfoGeometry.Complex.MobiusApollonius.mobiusMap s) := by
  have hs : s = (s.re : ℂ) + Complex.I * (s.im : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [hs]
  unfold apolloniusRatio dipoleZero dipolePole
  convert (InfoGeometry.Complex.MobiusApollonius.normSq_mobiusMap s.re s.im).symm
      using 1 <;>
    simp [InfoGeometry.Complex.MobiusApollonius.mobiusMap,
      InfoGeometry.Complex.MobiusApollonius.mobiusNumerator,
      InfoGeometry.Complex.MobiusApollonius.mobiusDenominator,
      Complex.normSq_apply] <;>
    ring

/-- Souriau generalized thermodynamic entropy potential:
    Φ(s) = - (1/2) * ln(R(s)). -/
def souriauEntropyPotential (s : ℂ) : ℝ :=
  - (1 / 2) * Real.log (apolloniusRatio s)

/-- Souriau entropy leaf at level λ > 0:
    ℒ_λ = {s ∈ ℂ | R(s) = λ}. -/
def IsOnEntropyLeaf (s : ℂ) (lambda : ℝ) : Prop :=
  apolloniusRatio s = lambda

/-- The Souriau affine temperature parameter derived from the Apollonius difference:
    β_Souriau(σ) = -4σ + 2. -/
def souriauApolloniusBeta (sigma : ℝ) : ℝ :=
  -4 * sigma + 2

/-- The Apollonian leaf carrier in the (σ, t) parameter space for ratio λ > 0. -/
def apolloniusLeafCarrier (lambda_ratio : ℝ) : Set (ℝ × ℝ) :=
  { p : ℝ × ℝ | apolloniusNumerator p.1 p.2 = lambda_ratio * apolloniusDenominator p.1 p.2 }

/-!
### 1. Coordinate Decomposition and Apollonius Norms
-/

/-- Numerator squared distance: |s - 3/2|² = (σ - 3/2)² + t². -/
theorem apollonius_num_normSq (s : ℂ) :
    Complex.normSq (s - dipoleZero) = (s.re - 3 / 2) ^ 2 + s.im ^ 2 := by
  have h_re : (s - dipoleZero).re = s.re - 3 / 2 := rfl
  have h_im : (s - dipoleZero).im = s.im := by dsimp [dipoleZero]; ring
  rw [Complex.normSq_apply, h_re, h_im]
  ring

/-- Denominator squared distance: |s + 1/2|² = (σ + 1/2)² + t². -/
theorem apollonius_den_normSq (s : ℂ) :
    Complex.normSq (s - dipolePole) = (s.re + 1 / 2) ^ 2 + s.im ^ 2 := by
  have h_re : (s - dipolePole).re = s.re + 1 / 2 := by dsimp [dipolePole]; ring
  have h_im : (s - dipolePole).im = s.im := by dsimp [dipolePole]; ring
  rw [Complex.normSq_apply, h_re, h_im]
  ring

/-- Strict positivity of the denominator for s ≠ -1/2. -/
theorem apollonius_den_pos (s : ℂ) (hs : s ≠ dipolePole) :
    0 < Complex.normSq (s - dipolePole) :=
  Complex.normSq_pos.mpr (sub_ne_zero.mpr hs)

/-!
### 2. Souriau Unitary Ground State Leaf (λ = 1 ↔ Re(s) = 1/2)
-/

/-- 🏆 THEOREM 1 (Apollonius-Souriau Bisector Equivalence):
    The level set R(s) = 1 is identically the critical line Re(s) = 1/2. -/
theorem souriau_leaf_one_iff_re_half (s : ℂ) (hs : s ≠ dipolePole) :
    IsOnEntropyLeaf s 1 ↔ s.re = 1 / 2 := by
  unfold IsOnEntropyLeaf apolloniusRatio
  have h_den_pos := apollonius_den_pos s hs
  rw [div_eq_one_iff_eq (ne_of_gt h_den_pos)]
  rw [apollonius_num_normSq, apollonius_den_normSq]
  constructor
  · intro h_eq
    have h_diff : ((s.re - 3 / 2) ^ 2 + s.im ^ 2) - ((s.re + 1 / 2) ^ 2 + s.im ^ 2) = 0 := by
      linarith
    have h_lin : -4 * s.re + 2 = 0 := by
      calc -4 * s.re + 2
        _ = ((s.re - 3 / 2) ^ 2 + s.im ^ 2) - ((s.re + 1 / 2) ^ 2 + s.im ^ 2) := by ring
        _ = 0 := h_diff
    linarith
  · intro h_re
    rw [h_re]
    ring

/-- 🏆 THEOREM 2 (Zero Entropy Potential on the Critical Boundary):
    On the critical line Re(s) = 1/2, the Souriau entropy potential vanishes: Φ(s) = 0. -/
theorem souriau_entropy_potential_zero_on_critical_line (s : ℂ) (hs : s ≠ dipolePole)
    (h_re : s.re = 1 / 2) :
    souriauEntropyPotential s = 0 := by
  unfold souriauEntropyPotential
  have h_leaf : apolloniusRatio s = 1 := (souriau_leaf_one_iff_re_half s hs).mpr h_re
  rw [h_leaf, Real.log_one]
  ring

/-- 🏆 THEOREM 2b: The Souriau temperature parameter vanishes identically on the critical line σ = 1/2. -/
theorem souriau_beta_zero_iff_critical_half (sigma : ℝ) :
    souriauApolloniusBeta sigma = 0 ↔ sigma = 1 / 2 := by
  unfold souriauApolloniusBeta
  constructor
  · intro h
    linarith
  · intro h
    subst h
    ring

/-!
### 3. Thermodynamic Phase Gradient: Subharmonic & Superharmonic Foliations
-/

/-- 🏆 THEOREM 3 (Subharmonic Foliation):
    In the right half-plane Re(s) > 1/2 away from the zero z₀ = 3/2, the ratio satisfies R(s) < 1,
    rendering the Souriau entropy strictly positive: Φ(s) > 0. -/
theorem souriau_entropy_positive_of_re_gt_half (s : ℂ) (hs_zero : s ≠ dipoleZero) (hs_pole : s ≠ dipolePole)
    (h_gt : 1 / 2 < s.re) :
    0 < souriauEntropyPotential s := by
  unfold souriauEntropyPotential apolloniusRatio
  have h_den_pos := apollonius_den_pos s hs_pole
  have h_diff : normSq (s - dipoleZero) < normSq (s - dipolePole) := by
    rw [apollonius_num_normSq, apollonius_den_normSq]
    have : ((s.re - 3 / 2) ^ 2 + s.im ^ 2) - ((s.re + 1 / 2) ^ 2 + s.im ^ 2) = -4 * (s.re - 1 / 2) := by ring
    have h_neg : -4 * (s.re - 1 / 2) < 0 := by linarith
    linarith
  have h_ratio_lt_one : normSq (s - dipoleZero) / normSq (s - dipolePole) < 1 :=
    (div_lt_one h_den_pos).mpr h_diff
  have h_num_pos : 0 < normSq (s - dipoleZero) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hs_zero)
  have h_ratio_pos : 0 < normSq (s - dipoleZero) / normSq (s - dipolePole) :=
    div_pos h_num_pos h_den_pos
  have h_log_neg : Real.log (normSq (s - dipoleZero) / normSq (s - dipolePole)) < 0 :=
    Real.log_neg h_ratio_pos h_ratio_lt_one
  nlinarith

/-- 🏆 THEOREM 4 (Superharmonic Foliation):
    In the left half-plane Re(s) < 1/2, the ratio satisfies R(s) > 1,
    rendering the Souriau entropy strictly negative: Φ(s) < 0. -/
theorem souriau_entropy_negative_of_re_lt_half (s : ℂ) (hs_pole : s ≠ dipolePole)
    (h_lt : s.re < 1 / 2) :
    souriauEntropyPotential s < 0 := by
  unfold souriauEntropyPotential apolloniusRatio
  have h_den_pos := apollonius_den_pos s hs_pole
  have h_diff : normSq (s - dipolePole) < normSq (s - dipoleZero) := by
    rw [apollonius_num_normSq, apollonius_den_normSq]
    have : ((s.re + 1 / 2) ^ 2 + s.im ^ 2) - ((s.re - 3 / 2) ^ 2 + s.im ^ 2) = 4 * (s.re - 1 / 2) := by ring
    have h_neg : 4 * (s.re - 1 / 2) < 0 := by linarith
    linarith
  have h_ratio_gt_one : 1 < normSq (s - dipoleZero) / normSq (s - dipolePole) :=
    (one_lt_div h_den_pos).mpr h_diff
  have h_log_pos : 0 < Real.log (normSq (s - dipoleZero) / normSq (s - dipolePole)) :=
    Real.log_pos h_ratio_gt_one
  nlinarith

/-- 🏆 THEOREM 4b: The Souriau temperature parameter is strictly negative on the subharmonic disk domain σ > 1/2. -/
theorem souriau_beta_neg_iff_disk_domain (sigma : ℝ) :
    souriauApolloniusBeta sigma < 0 ↔ 1 / 2 < sigma := by
  unfold souriauApolloniusBeta
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- 🏆 THEOREM 4c: The Souriau temperature parameter is strictly positive on the exterior domain σ < 1/2. -/
theorem souriau_beta_pos_iff_exterior_domain (sigma : ℝ) :
    0 < souriauApolloniusBeta sigma ↔ sigma < 1 / 2 := by
  unfold souriauApolloniusBeta
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- 🏆 THEOREM 4d: The unitary Apollonius leaf (λ = 1) is the critical line σ = 1/2. -/
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

/-!
### 4. Transversality & Orthogonal Foliation of the Thermodynamic Flow
-/

/-- The Hamiltonian phase angle: H_HP(s) = arg((s - 3/2) / (s + 1/2)). -/
def hamiltonianPhase (s : ℂ) : ℝ :=
  Complex.arg ((s - dipoleZero) / (s - dipolePole))

/-- 🏆 THEOREM 5 (Orthogonal Foliation Decoupling):
    The modulus potential Φ(s) and phase H_HP(s) are conjugate harmonic coordinates:
    ln((s - 3/2)/(s + 1/2)) = -Φ(s) + i · H_HP(s). -/
theorem souriau_hamiltonian_conformal_conjugation (s : ℂ) (hs1 : s ≠ dipoleZero) (hs2 : s ≠ dipolePole) :
    let w := (s - dipoleZero) / (s - dipolePole)
    w ≠ 0 ∧ Complex.log w = - (souriauEntropyPotential s : ℂ) + (hamiltonianPhase s : ℂ) * Complex.I := by
  intro w
  have hw_ne : w ≠ 0 := div_ne_zero (sub_ne_zero.mpr hs1) (sub_ne_zero.mpr hs2)
  refine ⟨hw_ne, ?_⟩
  unfold Complex.log
  have h_norm_w : ‖w‖ = Real.sqrt (normSq (s - dipoleZero) / normSq (s - dipolePole)) := by
    rw [Complex.norm_def, Complex.normSq_div]
  have h_pos : 0 < normSq (s - dipoleZero) / normSq (s - dipolePole) :=
    div_pos (Complex.normSq_pos.mpr (sub_ne_zero.mpr hs1))
      (Complex.normSq_pos.mpr (sub_ne_zero.mpr hs2))
  have h_log_norm : Real.log ‖w‖ = - souriauEntropyPotential s := by
    unfold souriauEntropyPotential apolloniusRatio
    rw [h_norm_w, Real.log_sqrt (le_of_lt h_pos)]
    ring
  have h_re : (Real.log ‖w‖ : ℂ) = - (souriauEntropyPotential s : ℂ) := by
    exact_mod_cast congrArg Complex.ofReal h_log_norm
  have h_im : (Complex.arg w : ℂ) * Complex.I =
      (hamiltonianPhase s : ℂ) * Complex.I := rfl
  rw [h_re, h_im]

/-!
### 5. Grand Capstone: Souriau Entropy Foliation Synthesis
-/

/-- 🏆 GRAND CAPSTONE: Complete Souriau Thermodynamic Foliation on Apollonius Leaves -/
theorem grand_souriau_apollonius_foliation_synthesis
    (s : ℂ) (hs_pole : s ≠ dipolePole) (hs_zero : s ≠ dipoleZero)
    (sigma t : ℝ) (p_point : UpperHalfPlanePoint) (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    (IsOnEntropyLeaf s 1 ↔ s.re = 1 / 2) ∧
    (s.re = 1 / 2 → souriauEntropyPotential s = 0) ∧
    (1 / 2 < s.re → 0 < souriauEntropyPotential s) ∧
    (s.re < 1 / 2 → souriauEntropyPotential s < 0) ∧
    (Complex.log ((s - dipoleZero) / (s - dipolePole)) =
      - (souriauEntropyPotential s : ℂ) + (hamiltonianPhase s : ℂ) * Complex.I) ∧
    (souriauApolloniusBeta (1 / 2) = 0) ∧
    (apolloniusNumerator sigma t - apolloniusDenominator sigma t = -4 * sigma + 2) ∧
    (fisherMetricMatrix p_point 0 0 = 1 / p_point.y ^ 2) ∧
    ((fisherMetricMatrix p_point).det = 1 / p_point.y ^ 4) ∧
    (0 < dotProduct (mulVec (fisherMetricMatrix p_point) v) v) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨souriau_leaf_one_iff_re_half s hs_pole,
   souriau_entropy_potential_zero_on_critical_line s hs_pole,
   souriau_entropy_positive_of_re_gt_half s hs_zero hs_pole,
   souriau_entropy_negative_of_re_lt_half s hs_pole,
   (souriau_hamiltonian_conformal_conjugation s hs_zero hs_pole).2,
   by unfold souriauApolloniusBeta; ring,
   apollonius_difference sigma t,
   rfl,
   fisher_metric_det p_point,
   fisher_metric_pos_def p_point v hv,
   F_sq,
   F_B_F_eq_R⟩

end

end InfoGeometry.Thermodynamics.SouriauApolloniusFoliation
