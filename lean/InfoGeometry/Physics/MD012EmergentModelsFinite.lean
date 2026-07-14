import Mathlib
import InfoGeometry.Physics.MD011StatisticalInfoGeometry
import InfoGeometry.Physics.Section38StressEnergyDomainSeparation

/-!
# Repaired MD 012: finite shadows of emergent-spacetime models

Source: `github-nick:nickgou-nuke/MD`, file `012.md`.

Chapter 12 describes three model families for emergent spacetime: Lorentzian
signature from biquaternion statistics, density-matrix stress tensors, and
quaternionic condensate/torsion dynamics.  The continuum and gravitational
claims are hypotheses in the manuscript, not finite Lean theorems.

This owner formalizes only the finite algebraic socket:

* an eight-component diagonal covariance table with two time-sector entries and
  six space-sector entries, together with its diagonal inverse;
* extraction of four-component diagonal covariance/sign tables and their
  finite inverse relation;
* symmetry/reduction of the density-matrix stress shadow by reusing the Section
  38 owner;
* a finite torsion-from-spin source table and the zero-spin/zero-torsion
  algebraic implication.

No theorem here asserts Gaussian analytic continuation, maximum-entropy
existence, Lorentzian spacetime emergence, action variation, Einstein equations,
Dirac equations, ECSK dynamics, or geometric torsion of a connection.
-/

noncomputable section

namespace MD012EmergentModelsFinite

set_option linter.unusedSimpArgs false

open Matrix
open InfoGeometry.Physics.Section34StrengthenedFormalism
open InfoGeometry.Physics.Section38StressEnergyDomainSeparation

/-- Eight real coordinates used by the source's biquaternion-statistics model. -/
abbrev BiquatStatIndex := Fin 8

/-- Four selected spacetime-like coordinates in the finite sign table. -/
abbrev ModelSpacetimeIndex := Fin 4

/-- Generic diagonal matrix constructor. -/
def diagMatrix {n : Type} [DecidableEq n] (d : n → ℝ) : Matrix n n ℝ :=
  fun i j => if i = j then d i else 0

/-- Diagonal covariance entries: two positive time-sector and six negative space-sector entries. -/
def lorentzCovDiagEntry (beta tau kappa : ℝ) (i : BiquatStatIndex) : ℝ :=
  if (i : Nat) < 2 then 1 / (beta * tau) else - (1 / (beta * kappa))

/-- Diagonal inverse-covariance/stiffness entries. -/
def lorentzInvDiagEntry (beta tau kappa : ℝ) (i : BiquatStatIndex) : ℝ :=
  if (i : Nat) < 2 then beta * tau else - (beta * kappa)

/-- Finite covariance table for the repaired statistical model. -/
def lorentzCovariance8 (beta tau kappa : ℝ) : Matrix BiquatStatIndex BiquatStatIndex ℝ :=
  diagMatrix (lorentzCovDiagEntry beta tau kappa)

/-- Finite inverse-covariance table for the repaired statistical model. -/
def lorentzInverseCovariance8 (beta tau kappa : ℝ) : Matrix BiquatStatIndex BiquatStatIndex ℝ :=
  diagMatrix (lorentzInvDiagEntry beta tau kappa)

/-- The diagonal inverse covariance is a left inverse to the diagonal covariance. -/
theorem lorentzInverseCovariance8_mul_covariance8
    (beta tau kappa : ℝ) (ht : beta * tau ≠ 0) (hk : beta * kappa ≠ 0) :
    lorentzInverseCovariance8 beta tau kappa * lorentzCovariance8 beta tau kappa = 1 := by
  have hbeta : beta ≠ 0 := (mul_ne_zero_iff.mp ht).1
  have htau : tau ≠ 0 := (mul_ne_zero_iff.mp ht).2
  have hkappa : kappa ≠ 0 := (mul_ne_zero_iff.mp hk).2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzInverseCovariance8, lorentzCovariance8, diagMatrix,
      lorentzInvDiagEntry, lorentzCovDiagEntry, Matrix.mul_apply]
  all_goals field_simp [hbeta, htau, hkappa]

/-- The diagonal covariance is also a right inverse to the inverse covariance. -/
theorem lorentzCovariance8_mul_inverseCovariance8
    (beta tau kappa : ℝ) (ht : beta * tau ≠ 0) (hk : beta * kappa ≠ 0) :
    lorentzCovariance8 beta tau kappa * lorentzInverseCovariance8 beta tau kappa = 1 := by
  have hbeta : beta ≠ 0 := (mul_ne_zero_iff.mp ht).1
  have htau : tau ≠ 0 := (mul_ne_zero_iff.mp ht).2
  have hkappa : kappa ≠ 0 := (mul_ne_zero_iff.mp hk).2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzInverseCovariance8, lorentzCovariance8, diagMatrix,
      lorentzInvDiagEntry, lorentzCovDiagEntry, Matrix.mul_apply]
  all_goals field_simp [hbeta, htau, hkappa]

/-- Four-coordinate diagonal covariance table extracted from the eight-coordinate covariance. -/
def lorentzCovMetric4 (beta tau kappa : ℝ) : Matrix ModelSpacetimeIndex ModelSpacetimeIndex ℝ :=
  fun i j => if i = j then (if i = 0 then 1 / (beta * tau) else - (1 / (beta * kappa))) else 0

/-- Four-coordinate diagonal sign/stiffness table extracted from the inverse covariance. -/
def lorentzSignMetric4 (beta tau kappa : ℝ) : Matrix ModelSpacetimeIndex ModelSpacetimeIndex ℝ :=
  fun i j => if i = j then (if i = 0 then beta * tau else - (beta * kappa)) else 0

/-- The finite time-sector diagonal entry. -/
theorem lorentzSignMetric4_time_entry (beta tau kappa : ℝ) :
    lorentzSignMetric4 beta tau kappa 0 0 = beta * tau := by
  simp [lorentzSignMetric4]

/-- A representative finite space-sector diagonal entry. -/
theorem lorentzSignMetric4_space1_entry (beta tau kappa : ℝ) :
    lorentzSignMetric4 beta tau kappa 1 1 = - (beta * kappa) := by
  simp [lorentzSignMetric4]

/-- The extracted finite sign/stiffness table is symmetric. -/
theorem lorentzSignMetric4_symmetric (beta tau kappa : ℝ) :
    lorentzSignMetric4 beta tau kappa = (lorentzSignMetric4 beta tau kappa)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lorentzSignMetric4]

/-- The extracted finite covariance table is symmetric. -/
theorem lorentzCovMetric4_symmetric (beta tau kappa : ℝ) :
    lorentzCovMetric4 beta tau kappa = (lorentzCovMetric4 beta tau kappa)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lorentzCovMetric4]

/-- The four-coordinate sign/stiffness table is inverse to the extracted covariance table. -/
theorem lorentzSignMetric4_mul_covMetric4
    (beta tau kappa : ℝ) (ht : beta * tau ≠ 0) (hk : beta * kappa ≠ 0) :
    lorentzSignMetric4 beta tau kappa * lorentzCovMetric4 beta tau kappa = 1 := by
  have hbeta : beta ≠ 0 := (mul_ne_zero_iff.mp ht).1
  have htau : tau ≠ 0 := (mul_ne_zero_iff.mp ht).2
  have hkappa : kappa ≠ 0 := (mul_ne_zero_iff.mp hk).2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzSignMetric4, lorentzCovMetric4, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals field_simp [hbeta, htau, hkappa]

/-- The extracted covariance table is also inverse to the four-coordinate sign table. -/
theorem lorentzCovMetric4_mul_signMetric4
    (beta tau kappa : ℝ) (ht : beta * tau ≠ 0) (hk : beta * kappa ≠ 0) :
    lorentzCovMetric4 beta tau kappa * lorentzSignMetric4 beta tau kappa = 1 := by
  have hbeta : beta ≠ 0 := (mul_ne_zero_iff.mp ht).1
  have htau : tau ≠ 0 := (mul_ne_zero_iff.mp ht).2
  have hkappa : kappa ≠ 0 := (mul_ne_zero_iff.mp hk).2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzSignMetric4, lorentzCovMetric4, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals field_simp [hbeta, htau, hkappa]

/-- If the source parameters are positive, the selected time-sector entry is positive. -/
theorem lorentzSignMetric4_time_positive
    (beta tau kappa : ℝ) (hbeta : 0 < beta) (htau : 0 < tau) :
    0 < lorentzSignMetric4 beta tau kappa 0 0 := by
  simp [lorentzSignMetric4]
  exact mul_pos hbeta htau

/-- If `beta` and `kappa` are positive, a selected space-sector entry is negative. -/
theorem lorentzSignMetric4_space1_negative
    (beta tau kappa : ℝ) (hbeta : 0 < beta) (hkappa : 0 < kappa) :
    lorentzSignMetric4 beta tau kappa 1 1 < 0 := by
  simp [lorentzSignMetric4]
  exact mul_pos hbeta hkappa

/-- Finite ECSK-style torsion source table: torsion is scalar-coupled spin density. -/
def torsionFromSpin (kap : ℝ)
    (spin : ModelSpacetimeIndex → ModelSpacetimeIndex → ModelSpacetimeIndex → ℝ) :
    ModelSpacetimeIndex → ModelSpacetimeIndex → ModelSpacetimeIndex → ℝ :=
  fun a b c => kap * spin a b c

/-- Zero spin-source table gives zero finite torsion-source table. -/
theorem torsionFromSpin_zero_of_spin_zero (kap : ℝ)
    (spin : ModelSpacetimeIndex → ModelSpacetimeIndex → ModelSpacetimeIndex → ℝ)
    (hspin : ∀ a b c, spin a b c = 0) :
    ∀ a b c, torsionFromSpin kap spin a b c = 0 := by
  intro a b c
  simp [torsionFromSpin, hspin a b c]

/-- Finite contortion-style algebraic table built from a supplied torsion table. -/
def contortionShadow
    (T : ModelSpacetimeIndex → ModelSpacetimeIndex → ModelSpacetimeIndex → ℝ) :
    ModelSpacetimeIndex → ModelSpacetimeIndex → ModelSpacetimeIndex → ℝ :=
  fun a b c => (1 / 2 : ℝ) * (T a b c + T b a c + T c a b)

/-- If the supplied finite torsion table is zero, the contortion shadow is zero. -/
theorem contortionShadow_zero_of_torsion_zero
    (T : ModelSpacetimeIndex → ModelSpacetimeIndex → ModelSpacetimeIndex → ℝ)
    (hT : ∀ a b c, T a b c = 0) :
    ∀ a b c, contortionShadow T a b c = 0 := by
  intro a b c
  simp [contortionShadow, hT]

/-- Repaired theorem-safe Chapter 12 finite model packet. -/
theorem repaired_MD012_finite_model_packet
    (beta tau kappa : ℝ) (ht : beta * tau ≠ 0) (hk : beta * kappa ≠ 0)
    (D : DomainSeparatedStressDatum)
    (hmetric : ∀ mu nu, D.metric mu nu = D.metric nu mu)
    (hconn : ∀ mu nu, D.connectionVariation mu nu = D.connectionVariation nu mu)
    (hzero : ∀ mu nu, D.connectionVariation mu nu = 0)
    (kap : ℝ) (spin : ModelSpacetimeIndex → ModelSpacetimeIndex → ModelSpacetimeIndex → ℝ)
    (hspin : ∀ a b c, spin a b c = 0) :
    lorentzInverseCovariance8 beta tau kappa * lorentzCovariance8 beta tau kappa = 1 ∧
    lorentzCovariance8 beta tau kappa * lorentzInverseCovariance8 beta tau kappa = 1 ∧
    lorentzSignMetric4 beta tau kappa = (lorentzSignMetric4 beta tau kappa)ᵀ ∧
    lorentzCovMetric4 beta tau kappa = (lorentzCovMetric4 beta tau kappa)ᵀ ∧
    lorentzSignMetric4 beta tau kappa * lorentzCovMetric4 beta tau kappa = 1 ∧
    (∀ mu nu, D.fullStress mu nu = D.fullStress nu mu) ∧
    (∀ mu nu, D.fullStress mu nu = D.compactStress mu nu) ∧
    (∀ a b c, torsionFromSpin kap spin a b c = 0) := by
  exact ⟨lorentzInverseCovariance8_mul_covariance8 beta tau kappa ht hk,
    lorentzCovariance8_mul_inverseCovariance8 beta tau kappa ht hk,
    lorentzSignMetric4_symmetric beta tau kappa,
    lorentzCovMetric4_symmetric beta tau kappa,
    lorentzSignMetric4_mul_covMetric4 beta tau kappa ht hk,
    (repaired_section38_stress_domain_packet D hmetric hconn hzero).1,
    (repaired_section38_stress_domain_packet D hmetric hconn hzero).2,
    torsionFromSpin_zero_of_spin_zero kap spin hspin⟩

end MD012EmergentModelsFinite

end noncomputable section
