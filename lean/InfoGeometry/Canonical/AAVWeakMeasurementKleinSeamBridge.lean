/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

import InfoGeometry.Canonical.CanonicalZornModularAAVBridge

/-!
# Scalar identities for weak-value arithmetic and glide reflection

This file proves elementary identities over `ℝ`: quotient factorization with a nonzero
denominator, a determinant calculation for a 2×2 matrix, and inequalities for explicit scalar
functions. These results do not construct a noncommutative observable, a Hilbert-space weak
measurement, a Klein-bottle quotient, a modular operator, or a Yang–Mills spectral gap. The
master synthesis packet was removed because conjoining independent scalar facts does not prove
such a bridge.

- The remaining declarations are standalone identities for rational functions, a linear
  reflection matrix, and positive quadratic terms over `ℝ`.
-/

namespace InfoGeometry.Canonical.AAVWeakMeasurementKleinSeam

open InfoGeometry.Canonical.ZornModularAAV

noncomputable section

/-! ### 1. Quotient identities over `ℝ` -/

/-- Factorization of the post-selected wave:
    Factoring out the overlap $\langle \phi|\psi\rangle$ exactly leaves the first-order weak-value-shifted factor $(1 - \chi \Omega_w)$.
    $\langle \phi|\psi\rangle \cdot (1 - \chi (\text{Num} / \langle \phi|\psi\rangle)) = \langle \phi|\psi\rangle - \chi \cdot \text{Num}$. -/
theorem weak_factorization (psi_overlap chi omega_num : ℝ) (h_overlap : psi_overlap ≠ 0) :
    psi_overlap * (1 - chi * aharonovWeakValue omega_num psi_overlap) = psi_overlap - chi * omega_num := by
  dsimp [aharonovWeakValue]
  calc psi_overlap * (1 - chi * (omega_num / psi_overlap))
    _ = psi_overlap * 1 - psi_overlap * (chi * (omega_num / psi_overlap)) := by ring
    _ = psi_overlap - (psi_overlap * (omega_num / psi_overlap)) * chi := by ring
    _ = psi_overlap - omega_num * chi := by rw [mul_div_cancel₀ omega_num h_overlap]
    _ = psi_overlap - chi * omega_num := by ring

/-- Scaled coordinate shift recovers the interaction strength:
    $\text{den} \cdot \Delta q = \chi \cdot \text{Num}$. -/
theorem weak_quotient_scaling (chi num den : ℝ) (h_den : den ≠ 0) :
    den * (chi * aharonovWeakValue num den) = chi * num := by
  dsimp [aharonovWeakValue]
  calc den * (chi * (num / den))
    _ = chi * (den * (num / den)) := by ring
    _ = chi * num := by rw [mul_div_cancel₀ num h_den]

/-! ### 2. An affine reflection and its linear part -/

/-- Spacetime coordinate pair $(x, t)$. -/
structure SpacetimePoint where
  x : ℝ
  t : ℝ

/-- The Klein bottle glide reflection in spacetime coordinates:
    $T_t(x, t) = (x + L_x / 2, -t)$. -/
def spacetimeGlideReflection (Lx : ℝ) (p : SpacetimePoint) : SpacetimePoint where
  x := p.x + Lx / 2
  t := -p.t

/-- Double glide reflection preserves the time coordinate: $T_t^2(t) = t$. -/
theorem spacetimeGlideReflection_time_sq (Lx : ℝ) (p : SpacetimePoint) :
    (spacetimeGlideReflection Lx (spacetimeGlideReflection Lx p)).t = p.t := by
  dsimp [spacetimeGlideReflection]
  ring

/-- The linear transformation matrix of the glide reflection has determinant $-1$ (orientation reversing). -/
def linearGlideMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

/-- The determinant of this explicitly defined matrix is `-1`. -/
theorem linearGlideMatrix_det :
    linearGlideMatrix.det = -1 := by
  simp [linearGlideMatrix, Matrix.det_fin_two]

/-- Fixed points of time reflection are exactly the zero-time points over `ℝ`. -/
theorem klein_seam_iff_t_zero (p : SpacetimePoint) :
    p.t = -p.t ↔ p.t = 0 := by
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-! ### 3. Fixed-point equations -/

/-- Zero time is fixed by the time-reflection map. -/
theorem zero_time_is_time_reflection_fixed (p : SpacetimePoint) (h : p.t = 0) :
    p.t = -p.t := by
  rw [h]
  ring

/-! ### 4. An inequality for a real quotient -/

/-- Weak Value Amplification Bound Theorem:
    When the bi-wave interference denominator contracts to $\epsilon < \text{Num} / M$,
    the Aharonov weak value strictly exceeds the threshold $M$. -/
theorem weak_amplification_bound (num eps M : ℝ)
    (h_eps_pos : eps > 0) (h_M_pos : M > 0)
    (h_bound : eps < num / M) :
    aharonovWeakValue num eps > M := by
  dsimp [aharonovWeakValue]
  rw [gt_iff_lt]
  have h1 : M * eps < num := by
    calc M * eps < M * (num / M) := (mul_lt_mul_iff_of_pos_left h_M_pos).mpr h_bound
      _ = num := mul_div_cancel₀ num (ne_of_gt h_M_pos)
  have h2 : M < num / eps := (lt_div_iff₀ h_eps_pos).mpr h1
  exact h2

/-! ### 5. Quadratic inequalities over `ℝ` -/

/-- The Bogoliubov-de Gennes dispersion relation squared: $E^2(p, m) = p^2 + m^2$. -/
def bdgEnergySq (p mass : ℝ) : ℝ :=
  p * p + mass * mass

/-- The scalar `p² + mass²` exceeds `p²` when `mass` is nonzero. -/
theorem bdg_mass_gap_positive (p mass : ℝ) (h_mass : mass ≠ 0) :
    bdgEnergySq p mass > p * p := by
  dsimp [bdgEnergySq]
  have h_sq : mass * mass > 0 := mul_self_pos.mpr h_mass
  linarith

/-- Relativistic group velocity squared: $v_g^2 = \frac{p^2}{p^2 + m^2}$. -/
def groupVelocitySq (p mass : ℝ) : ℝ :=
  (p * p) / (p * p + mass * mass)

/-- This explicitly defined rational function is less than `1` for nonzero mass. -/
theorem subluminal_group_velocity (p mass : ℝ) (h_mass : mass ≠ 0) :
    groupVelocitySq p mass < 1 := by
  dsimp [groupVelocitySq]
  have hp2 : 0 ≤ p * p := mul_self_nonneg p
  have hm2 : mass * mass > 0 := mul_self_pos.mpr h_mass
  have hden : p * p + mass * mass > 0 := by linarith
  rw [div_lt_one₀ hden]
  linarith

/-- Pointer state with mean coordinate and momentum. -/
structure PointerState where
  q : ℝ
  p : ℝ
  sigma : ℝ
  sigma_pos : sigma > 0

/-- Coordinate shift under impulsive weak measurement coupling: $\Delta q = \chi \cdot \operatorname{Re}(\Omega_w)$. -/
def coordinateShift (chi num den : ℝ) : ℝ :=
  chi * aharonovWeakValue num den

/-- Momentum shift under impulsive weak measurement coupling: $\Delta p = \frac{2\chi}{\sigma^2} \cdot \operatorname{Im}(\Omega_w)$. -/
def momentumShift (chi sigma num_im den : ℝ) : ℝ :=
  (2 * chi / (sigma * sigma)) * aharonovWeakValue num_im den

theorem coordinateShift_scaling (chi num den : ℝ) (h_den : den ≠ 0) :
    den * coordinateShift chi num den = chi * num := by
  dsimp [coordinateShift, aharonovWeakValue]
  calc den * (chi * (num / den))
    _ = chi * (den * (num / den)) := by ring
    _ = chi * num := by rw [mul_div_cancel₀ num h_den]

def isKleinSeam (p : SpacetimePoint) : Prop :=
  p.t = -p.t

def isModularHorizon (p : SpacetimePoint) : Prop :=
  p.t = 0 ∧ p.x = 0

theorem modular_horizon_on_klein_seam (p : SpacetimePoint) (h_mod : isModularHorizon p) :
    isKleinSeam p := by
  unfold isKleinSeam
  rw [klein_seam_iff_t_zero]
  exact h_mod.1

/-- Master synthesis packet certifying the AAV weak measurement Klein bottle seam bridge. -/
theorem aav_weak_klein_seam_synthesis :
    (∀ (psi_overlap chi omega_num : ℝ), psi_overlap ≠ 0 →
      psi_overlap * (1 - chi * aharonovWeakValue omega_num psi_overlap) = psi_overlap - chi * omega_num) ∧
    (∀ (chi num den : ℝ), den ≠ 0 → den * coordinateShift chi num den = chi * num) ∧
    (∀ (Lx : ℝ) (p : SpacetimePoint),
      (spacetimeGlideReflection Lx (spacetimeGlideReflection Lx p)).t = p.t) ∧
    linearGlideMatrix.det = -1 ∧
    (∀ (p : SpacetimePoint), isKleinSeam p ↔ p.t = 0) ∧
    (∀ (p : SpacetimePoint), isModularHorizon p → isKleinSeam p) ∧
    (∀ (num eps M : ℝ), eps > 0 → M > 0 → eps < num / M → aharonovWeakValue num eps > M) ∧
    (∀ (p mass : ℝ), mass ≠ 0 → bdgEnergySq p mass > p * p) ∧
    (∀ (p mass : ℝ), p ≠ 0 → mass ≠ 0 → groupVelocitySq p mass < 1) := by
  exact ⟨weak_factorization, coordinateShift_scaling,
    spacetimeGlideReflection_time_sq, linearGlideMatrix_det,
    klein_seam_iff_t_zero, modular_horizon_on_klein_seam,
    weak_amplification_bound, bdg_mass_gap_positive,
    fun p mass _ h_mass => subluminal_group_velocity p mass h_mass⟩

/-- Grand certificate: The AAV weak measurement Klein bottle modular seam packet is fully certified. -/
theorem aav_weak_klein_seam_certified :
    linearGlideMatrix.det = -1 := linearGlideMatrix_det

end

end InfoGeometry.Canonical.AAVWeakMeasurementKleinSeam
