import InfoGeometry.Thermo.GenericMetriplecticFlow
import Mathlib

/-!
# Two-dimensional skew-Casimir obstruction

For the two-coordinate real carrier `(eta,theta)`, let

`L : V* -> V`

be skew with respect to covector evaluation.  If the nonzero coordinate
covector `deta` lies in `ker L`, then `L` is identically zero.  Thus a
nontrivial reversible operator with `deta` as a Casimir cannot live on this
particular two-dimensional carrier.

This theorem supplies the exact finite-dimensional reason for adjoining the
third auxiliary coordinate in `BipolarGENERICThreeCoordinateModel`.
-/

noncomputable section

namespace InfoGeometry.Thermo.BipolarTwoDimensionalSkewObstruction

open InfoGeometry.Thermo.GenericMetriplecticFlow

/-- Two-coordinate state carrier `(eta,theta)`. -/
abbrev State2 := Fin 2 → ℝ

/-- Coordinate vector in the eta direction. -/
def etaBasis2 : State2 := ![1, 0]

/-- Coordinate vector in the theta direction. -/
def thetaBasis2 : State2 := ![0, 1]

/-- Coordinate covector `deta`. -/
def etaCovector2 : Covector State2 where
  toFun x := x 0
  map_add' x y := by simp
  map_smul' c x := by simp

/-- Coordinate covector `dtheta`. -/
def thetaCovector2 : Covector State2 where
  toFun x := x 1
  map_add' x y := by simp
  map_smul' c x := by simp

@[simp] theorem etaCovector2_etaBasis2 : etaCovector2 etaBasis2 = 1 := by
  simp [etaCovector2, etaBasis2]

@[simp] theorem etaCovector2_thetaBasis2 : etaCovector2 thetaBasis2 = 0 := by
  simp [etaCovector2, thetaBasis2]

@[simp] theorem thetaCovector2_etaBasis2 : thetaCovector2 etaBasis2 = 0 := by
  simp [thetaCovector2, etaBasis2]

@[simp] theorem thetaCovector2_thetaBasis2 : thetaCovector2 thetaBasis2 = 1 := by
  simp [thetaCovector2, thetaBasis2]

/-- Coordinate decomposition of every vector. -/
theorem state2_coordinate_decomposition (x : State2) :
    x = x 0 • etaBasis2 + x 1 • thetaBasis2 := by
  ext i
  fin_cases i <;> simp [etaBasis2, thetaBasis2]

/-- Coordinate decomposition of every linear covector. -/
theorem covector2_coordinate_decomposition (α : Covector State2) :
    α = α etaBasis2 • etaCovector2 +
      α thetaBasis2 • thetaCovector2 := by
  apply LinearMap.ext
  intro x
  rw [state2_coordinate_decomposition x]
  simp only [map_add, map_smul]
  simp [etaBasis2, thetaBasis2, etaCovector2, thetaCovector2]

/-- The eta coordinate covector is nonzero. -/
theorem etaCovector2_ne_zero : etaCovector2 ≠ 0 := by
  intro h
  have hη := congrArg (fun α : Covector State2 => α etaBasis2) h
  simp at hη

/-- A skew operator that kills `deta` must also kill `dtheta`. -/
theorem theta_kernel_of_skew_eta_kernel
    (L : Covector State2 →ₗ[ℝ] State2)
    (hskew : ∀ α β : Covector State2,
      α (L β) = -β (L α))
    (heta : L etaCovector2 = 0) :
    L thetaCovector2 = 0 := by
  have h0 : etaCovector2 (L thetaCovector2) = 0 := by
    calc
      etaCovector2 (L thetaCovector2)
          = -thetaCovector2 (L etaCovector2) :=
        hskew etaCovector2 thetaCovector2
      _ = 0 := by rw [heta]; simp
  have h1eq :
      thetaCovector2 (L thetaCovector2) =
        -thetaCovector2 (L thetaCovector2) :=
    hskew thetaCovector2 thetaCovector2
  have h1 : thetaCovector2 (L thetaCovector2) = 0 := by
    linarith
  ext i
  fin_cases i
  · simpa [etaCovector2] using h0
  · simpa [thetaCovector2] using h1

/-- Main obstruction: skewness and the nontrivial eta Casimir force the entire
two-dimensional operator to vanish. -/
theorem skew_operator_eq_zero_of_eta_casimir
    (L : Covector State2 →ₗ[ℝ] State2)
    (hskew : ∀ α β : Covector State2,
      α (L β) = -β (L α))
    (heta : L etaCovector2 = 0) :
    L = 0 := by
  have htheta : L thetaCovector2 = 0 :=
    theta_kernel_of_skew_eta_kernel L hskew heta
  ext α i
  rw [covector2_coordinate_decomposition α]
  simp [heta, htheta]

/-- Therefore a nonzero reversible theta lane is incompatible with an eta
Casimir in two dimensions. -/
theorem no_nontrivial_theta_lane_in_two_dimensions
    (L : Covector State2 →ₗ[ℝ] State2)
    (hskew : ∀ α β : Covector State2,
      α (L β) = -β (L α))
    (heta : L etaCovector2 = 0)
    (htheta : L thetaCovector2 ≠ 0) : False := by
  have hL : L = 0 := skew_operator_eq_zero_of_eta_casimir L hskew heta
  apply htheta
  rw [hL]
  simp

/-- Compact obstruction packet. -/
theorem bipolar_two_dimensional_obstruction_packet
    (L : Covector State2 →ₗ[ℝ] State2)
    (hskew : ∀ α β : Covector State2,
      α (L β) = -β (L α))
    (heta : L etaCovector2 = 0) :
    etaCovector2 ≠ 0 ∧ L thetaCovector2 = 0 ∧ L = 0 := by
  exact ⟨etaCovector2_ne_zero,
    theta_kernel_of_skew_eta_kernel L hskew heta,
    skew_operator_eq_zero_of_eta_casimir L hskew heta⟩

end InfoGeometry.Thermo.BipolarTwoDimensionalSkewObstruction
