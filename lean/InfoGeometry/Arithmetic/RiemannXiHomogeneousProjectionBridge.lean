/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates
import InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge

/-! Genuine projection identities on the repository-native homogeneous carrier. -/

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannXiHomogeneousProjectionBridge

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge
open InfoGeometry.Arithmetic.CompletedXiHestenesHomogeneousCoordinates
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

theorem projectiveRatio_eq_cayleyToFugacity_projectiveS
    (X : HomogeneousCoord) (hq : X.2 ≠ 0)
    (hsum : X.1 + X.2 ≠ 0) :
    projectiveRatio X = cayleyToFugacity (projectiveS X) := by
  rcases X with ⟨p, q⟩
  change q ≠ 0 at hq
  change p + q ≠ 0 at hsum
  unfold projectiveRatio projectiveS cayleyToFugacity
  have hden : 1 - p / (p + q) ≠ 0 := by
    have h : 1 - p / (p + q) = q / (p + q) := by
      field_simp [hsum]
      ring
    rw [h]
    exact div_ne_zero hq hsum
  field_simp [hq, hsum, hden]
  ring

theorem cayleyToTemperature_projectiveRatio_eq_projectiveS
    (X : HomogeneousCoord) (hq : X.2 ≠ 0)
    (hsum : X.1 + X.2 ≠ 0) :
    cayleyToTemperature (projectiveRatio X) = projectiveS X := by
  rcases X with ⟨p, q⟩
  change q ≠ 0 at hq
  change p + q ≠ 0 at hsum
  unfold projectiveRatio projectiveS cayleyToTemperature
  have hden : 1 + p / q ≠ 0 := by
    have h : 1 + p / q = (p + q) / q := by
      field_simp [hq]
      ring
    rw [h]
    exact div_ne_zero hsum hq
  field_simp [hq, hsum, hden]
  ring_nf
  field_simp [hsum]
  ring

theorem projectiveS_homogeneousCoord (s : ℂ) :
    projectiveS (homogeneousCoord s) = s := by
  unfold projectiveS homogeneousCoord
  simp

@[simp] theorem projectiveRatio_homogeneousCoord (s : ℂ) :
    projectiveRatio (homogeneousCoord s) = cayleyToFugacity s :=
  tau_eq_cayleyToFugacity s

theorem cartanFlow_second_ne_zero
    (t : ℝ) {X : HomogeneousCoord} (hq : X.2 ≠ 0) :
    (cartanFlow t X).2 ≠ 0 := by
  rcases X with ⟨p, q⟩
  change q ≠ 0 at hq
  change (Real.exp (-t) : ℂ) * q ≠ 0
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hq

theorem projectiveRatio_cartanFlow_intertwining
    (t : ℝ) (X : HomogeneousCoord) (hq : X.2 ≠ 0) :
    projectiveRatio (cartanFlow t X) =
      (Real.exp (2 * t) : ℂ) * projectiveRatio X := by
  exact projectiveRatio_cartanFlow t hq

theorem cayley_projectiveS_cartanFlow_intertwining
    (t : ℝ) (X : HomogeneousCoord) (hq : X.2 ≠ 0)
    (hsum : X.1 + X.2 ≠ 0)
    (hsumFlow : (cartanFlow t X).1 + (cartanFlow t X).2 ≠ 0) :
    cayleyToFugacity (projectiveS (cartanFlow t X)) =
      (Real.exp (2 * t) : ℂ) * cayleyToFugacity (projectiveS X) := by
  rw [← projectiveRatio_eq_cayleyToFugacity_projectiveS
      (cartanFlow t X) (cartanFlow_second_ne_zero t hq) hsumFlow]
  rw [projectiveRatio_cartanFlow_intertwining t X hq]
  rw [projectiveRatio_eq_cayleyToFugacity_projectiveS X hq hsum]

theorem homogeneousXi_eq_riemannXiCayley_projectiveRatio
    (X : HomogeneousCoord) (hq : X.2 ≠ 0)
    (hsum : X.1 + X.2 ≠ 0) :
    homogeneousFunction riemannXi X =
      riemannXiCayley (projectiveRatio X) := by
  unfold homogeneousFunction riemannXiCayley
  rw [cayleyToTemperature_projectiveRatio_eq_projectiveS X hq hsum]

theorem riemannZeta_zero_iff_homogeneousXi_zero_of_strip
    {s : ℂ} (hRe : 0 < s.re) (hRe' : s.re < 1) :
    riemannZeta s = 0 ↔
      homogeneousFunction riemannXi (homogeneousCoord s) = 0 := by
  rw [show homogeneousFunction riemannXi (homogeneousCoord s) = riemannXi s by
    unfold homogeneousFunction
    rw [projectiveS_homogeneousCoord]]
  exact (riemannXi_eq_zero_iff_riemannZeta_eq_zero_of_strip hRe hRe').symm

theorem homogeneousXi_zero_iff_riemannXiCayley_zero
    (X : HomogeneousCoord) (hq : X.2 ≠ 0)
    (hsum : X.1 + X.2 ≠ 0) :
    homogeneousFunction riemannXi X = 0 ↔
      riemannXiCayley (projectiveRatio X) = 0 := by
  rw [homogeneousXi_eq_riemannXiCayley_projectiveRatio X hq hsum]

theorem riemannZeta_zero_iff_projectiveCayleyXi_zero_of_strip
    {s : ℂ} (hRe : 0 < s.re) (hRe' : s.re < 1) :
    riemannZeta s = 0 ↔
      riemannXiCayley (projectiveRatio (homogeneousCoord s)) = 0 := by
  rw [projectiveRatio_homogeneousCoord]
  exact riemannXiCayley_zero_iff_riemannZeta_zero_of_strip hRe hRe'

theorem homogeneous_projection_functional_reflection (s : ℂ) :
    homogeneousCoord (1 - s) = hestenesSwap (homogeneousCoord s) :=
  homogeneousCoord_one_sub s

theorem homogeneous_projection_swap_cayley_inversion (s : ℂ) :
    projectiveRatio (homogeneousCoord (1 - s)) =
      (projectiveRatio (homogeneousCoord s))⁻¹ := by
  change tau (1 - s) = (tau s)⁻¹
  exact tau_one_sub_eq_inv s

theorem homogeneousXi_swap_invariant
    (X : HomogeneousCoord) (hsum : X.1 + X.2 ≠ 0) :
    homogeneousFunction riemannXi (hestenesSwap X) =
      homogeneousFunction riemannXi X :=
  completedXi_homogeneousFunction_swap X hsum

theorem projectiveS_hestenesSwap
    (X : HomogeneousCoord) (hsum : X.1 + X.2 ≠ 0) :
    projectiveS (hestenesSwap X) = 1 - projectiveS X := by
  rcases X with ⟨p, q⟩
  change p + q ≠ 0 at hsum
  have hsum' : q + p ≠ 0 := by simpa [add_comm] using hsum
  unfold projectiveS hestenesSwap
  apply (div_eq_iff hsum').2
  field_simp [hsum]
  ring

theorem projectiveS_cartanFlow_eq_cayleyToTemperature_scaled
    (t : ℝ) (X : HomogeneousCoord) (hq : X.2 ≠ 0)
    (hsumFlow : (cartanFlow t X).1 + (cartanFlow t X).2 ≠ 0) :
    projectiveS (cartanFlow t X) =
      cayleyToTemperature
        ((Real.exp (2 * t) : ℂ) * projectiveRatio X) := by
  rw [← cayleyToTemperature_projectiveRatio_eq_projectiveS
      (cartanFlow t X) (cartanFlow_second_ne_zero t hq) hsumFlow]
  rw [projectiveRatio_cartanFlow_intertwining t X hq]

theorem homogeneousXi_cartanFlow_eq_riemannXiCayley_scaled
    (t : ℝ) (X : HomogeneousCoord) (hq : X.2 ≠ 0)
    (hsumFlow : (cartanFlow t X).1 + (cartanFlow t X).2 ≠ 0) :
    homogeneousFunction riemannXi (cartanFlow t X) =
      riemannXiCayley
        ((Real.exp (2 * t) : ℂ) * projectiveRatio X) := by
  rw [homogeneousXi_eq_riemannXiCayley_projectiveRatio
      (cartanFlow t X) (cartanFlow_second_ne_zero t hq) hsumFlow]
  rw [projectiveRatio_cartanFlow_intertwining t X hq]

theorem projectiveS_criticalLine_iff_projectiveRatio_unitCircle
    (X : HomogeneousCoord) (hq : X.2 ≠ 0)
    (hsum : X.1 + X.2 ≠ 0) :
    OnCriticalLine (projectiveS X) ↔
      OnLeeYangCircle (projectiveRatio X) := by
  rw [projectiveRatio_eq_cayleyToFugacity_projectiveS X hq hsum]
  exact criticalLine_iff_cayley_unitCircle (projectiveS X)

theorem homogeneous_swap_projection_intertwining
    (X : HomogeneousCoord) (hp : X.1 ≠ 0) (hq : X.2 ≠ 0)
    (hsum : X.1 + X.2 ≠ 0) :
    projectiveS (hestenesSwap X) = 1 - projectiveS X ∧
    projectiveRatio (hestenesSwap X) = (projectiveRatio X)⁻¹ := by
  constructor
  · exact projectiveS_hestenesSwap X hsum
  · rcases X with ⟨p, q⟩
    exact projectiveRatio_hestenesSwap hp hq

end InfoGeometry.Arithmetic.RiemannXiHomogeneousProjectionBridge
