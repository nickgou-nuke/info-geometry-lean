import Mathlib.Tactic
import InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry

/-!
# Finite real statistical-family readouts

This owner formalizes only the algebraic real core of the FD/MB/BE
parameterization.  The Bose expression is stated on the domain where its
denominator is positive.  No complex logarithm branch, Euler product, or
physical Riemann-hypothesis claim is introduced here.
-/

noncomputable section

namespace InfoGeometry.Clifford.ThermodynamicZetaGeometry

open InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry

inductive StatFamily where
  | FD
  | MB
  | BE

def kappa : StatFamily → ℝ
  | .FD => 1
  | .MB => 0
  | .BE => -1

@[simp] theorem kappa_FD : kappa .FD = 1 := rfl
@[simp] theorem kappa_MB : kappa .MB = 0 := rfl
@[simp] theorem kappa_BE : kappa .BE = -1 := rfl

/-- Unified real occupation number, totalized at a zero denominator. -/
def occupation (f : StatFamily) (θ : ℝ) : ℝ :=
  Real.exp θ / (1 + kappa f * Real.exp θ)

@[simp] theorem occupation_FD (θ : ℝ) :
    occupation .FD θ = fermiSimplexCoordinate θ := by
  simp [occupation, fermiSimplexCoordinate, add_comm]

@[simp] theorem occupation_MB (θ : ℝ) :
    occupation .MB θ = Real.exp θ := by
  simp [occupation]

@[simp] theorem occupation_BE (θ : ℝ) :
    occupation .BE θ = Real.exp θ / (1 - Real.exp θ) := by
  unfold occupation
  rw [kappa_BE]
  congr 1
  ring

theorem occupation_FD_pos (θ : ℝ) :
    0 < occupation .FD θ := by
  rw [occupation_FD]
  exact fermiSimplexCoordinate_pos θ

theorem occupation_FD_lt_one (θ : ℝ) :
    occupation .FD θ < 1 := by
  rw [occupation_FD]
  exact fermiSimplexCoordinate_lt_one θ

theorem occupation_MB_pos (θ : ℝ) :
    0 < occupation .MB θ := by
  rw [occupation_MB]
  exact Real.exp_pos _

theorem occupation_BE_denominator_pos_of_neg {θ : ℝ} (hθ : θ < 0) :
    0 < 1 - Real.exp θ := by
  have hexp : Real.exp θ < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hθ
  linarith

theorem occupation_BE_pos_of_neg {θ : ℝ} (hθ : θ < 0) :
    0 < occupation .BE θ := by
  rw [occupation_BE]
  exact div_pos (Real.exp_pos _) (occupation_BE_denominator_pos_of_neg hθ)

theorem occupation_fluctuation_identity
    (f : StatFamily) (θ : ℝ)
    (hden : 1 + kappa f * Real.exp θ ≠ 0) :
    occupation f θ * (1 - kappa f * occupation f θ) =
      Real.exp θ / (1 + kappa f * Real.exp θ) ^ 2 := by
  unfold occupation
  have hden' : 1 + Real.exp θ * kappa f ≠ 0 := by
    simpa [mul_comm] using hden
  field_simp [hden, hden']
  ring

theorem occupation_FD_fluctuation (θ : ℝ) :
    occupation .FD θ * (1 - occupation .FD θ) =
      Real.exp θ / (1 + Real.exp θ) ^ 2 := by
  have hden : 1 + kappa .FD * Real.exp θ ≠ 0 := by
    simp [kappa_FD]
    positivity
  simpa [kappa_FD] using occupation_fluctuation_identity .FD θ hden

theorem occupation_MB_fluctuation (θ : ℝ) :
    occupation .MB θ =
      Real.exp θ / (1 + (0 : ℝ) * Real.exp θ) ^ 2 := by
  simp [occupation_MB]

theorem occupation_BE_fluctuation {θ : ℝ} (hθ : θ < 0) :
    occupation .BE θ * (1 + occupation .BE θ) =
      Real.exp θ / (1 - Real.exp θ) ^ 2 := by
  have hden : 1 + kappa .BE * Real.exp θ ≠ 0 := by
    have hpos := occupation_BE_denominator_pos_of_neg hθ
    simpa using ne_of_gt hpos
  have h := occupation_fluctuation_identity .BE θ hden
  simpa [kappa_BE, sub_eq_add_neg] using h

@[simp] theorem occupation_FD_zero :
    occupation .FD 0 = 1 / 2 := by
  rw [occupation_FD]
  exact fermiSimplexCoordinate_zero

theorem deriv_occupation_FD (θ : ℝ) :
    deriv (occupation .FD) θ =
      occupation .FD θ * (1 - occupation .FD θ) := by
  unfold occupation
  simp only [kappa_FD, one_mul]
  change deriv (fun x : ℝ => Real.exp x / (1 + Real.exp x)) θ =
    (Real.exp θ / (1 + Real.exp θ)) *
      (1 - Real.exp θ / (1 + Real.exp θ))
  have hexp : HasDerivAt Real.exp (Real.exp θ) θ :=
    Real.hasDerivAt_exp θ
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 θ :=
    hasDerivAt_const θ 1
  have hden : HasDerivAt (fun x : ℝ => 1 + Real.exp x)
      (Real.exp θ) θ := by
    convert hconst.add hexp using 1 <;> simp
  have hne : 1 + Real.exp θ ≠ 0 := by positivity
  change deriv (Real.exp / (fun x : ℝ => 1 + Real.exp x)) θ = _
  rw [(hexp.div hden hne).deriv]
  field_simp [hne]

def massieuFugacityFD (z : ℝ) : ℝ :=
  Real.log (1 + z)

def massieuFugacityBE (z : ℝ) : ℝ :=
  -Real.log (1 - z)

theorem primon_supersymmetry_fugacity
    (z : ℝ) (hz : 0 < 1 + z) :
    massieuFugacityFD z + massieuFugacityBE (-z) = 0 := by
  unfold massieuFugacityFD massieuFugacityBE
  rw [show 1 - (-z) = 1 + z by ring]
  ring

end InfoGeometry.Clifford.ThermodynamicZetaGeometry
