import InfoGeometry.Geometry.RindlerLapseCalculus
import InfoGeometry.Clifford.Cl11Matrix
import Mathlib

/-!
# Coordinate Cartan identities for the flat Rindler coframe

The metric convention is diag(-1,1). The mixed Lorentz connection is symmetric
off diagonal: omega^0_1 = omega^1_0 = a*dt. Its lowered-index matrix is
antisymmetric. The torsion and curvature checks are coordinate identities;
no global manifold connection or spinor normalization is silently assumed.
-/

namespace InfoGeometry.Geometry.RindlerCartanFrame

noncomputable section

open InfoGeometry.Geometry.RindlerLapseCalculus
open InfoGeometry.Clifford.Cl11Matrix

abbrev Tangent := ℝ × ℝ

def area : LinearMap.BilinForm ℝ Tangent where
  toFun u :=
    { toFun v := u.1 * v.2 - u.2 * v.1
      map_add' v w := by dsimp; ring
      map_smul' c v := by dsimp; ring }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    change (u.1 + v.1) * w.2 - (u.2 + v.2) * w.1 =
      (u.1 * w.2 - u.2 * w.1) + (v.1 * w.2 - v.2 * w.1)
    ring
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    change (c * u.1) * v.2 - (c * u.2) * v.1 =
      c * (u.1 * v.2 - u.2 * v.1)
    ring

theorem area_alternating (v : Tangent) : area v v = 0 := by
  dsimp [area]
  ring

/-- de^0 = N'(x) dx wedge dt; the exterior sign is explicit. -/
def dCoframeTime (a x : ℝ) : LinearMap.BilinForm ℝ Tangent :=
  -(deriv (lapse a) x) • area

/-- omega^0_1 wedge e^1 = a dt wedge dx. -/
def timeConnectionTerm (a : ℝ) : LinearMap.BilinForm ℝ Tangent := a • area

theorem cartan_time_torsion_zero (a x : ℝ) :
    dCoframeTime a x + timeConnectionTerm a = 0 := by
  rw [dCoframeTime, timeConnectionTerm, (hasDerivAt_lapse a x).deriv]
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  dsimp [area]
  ring

/-- omega^1_0 wedge e^0 vanishes because both factors are multiples of dt. -/
theorem cartan_space_connection_zero (a x : ℝ) (v w : Tangent) :
    (a * v.1) * (lapse a x * w.1) - (a * w.1) * (lapse a x * v.1) = 0 := by
  ring

def metricMatrix : Mat2 := -Eplus

def connectionForm (a : ℝ) : Tangent →ₗ[ℝ] Mat2 where
  toFun v := (a * v.1) • J1
  map_add' v w := by simp [mul_add, add_smul]
  map_smul' c v := by
    simp [smul_smul]
    congr 1
    ring

/-- Metric compatibility is Lorentz-skewness, not Euclidean transpose-skewness. -/
theorem connection_lorentz_skew (a : ℝ) (v : Tangent) :
    (connectionForm a v).transpose * metricMatrix + metricMatrix * connectionForm a v = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [connectionForm, metricMatrix, Eplus, J1, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two] <;> ring

/-- Curvature d(omega)+omega wedge omega in the coordinate (t,x) plane. -/
def curvatureTX (a : ℝ) (p : Tangent) : Mat2 :=
  (fderiv ℝ (fun _ : Tangent => connectionForm a (0, 1)) p) (1, 0) -
    (fderiv ℝ (fun _ : Tangent => connectionForm a (1, 0)) p) (0, 1) +
    connectionForm a (1, 0) * connectionForm a (0, 1) -
    connectionForm a (0, 1) * connectionForm a (1, 0)

theorem rindler_connection_flat (a : ℝ) (p : Tangent) : curvatureTX a p = 0 := by
  simp [curvatureTX, connectionForm]

/-- The frame connection has coefficient a even when proper acceleration varies in space. -/
theorem frame_to_stationary_acceleration (a x : ℝ) (hx : lapse a x ≠ 0) :
    stationaryAcceleration a x * lapse a x = a := by
  exact div_mul_cancel₀ a hx

end
end InfoGeometry.Geometry.RindlerCartanFrame
