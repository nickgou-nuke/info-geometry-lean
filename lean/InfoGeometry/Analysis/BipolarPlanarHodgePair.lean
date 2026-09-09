import InfoGeometry.Analysis.BipolarBoundaryTrace
import InfoGeometry.Analysis.BipolarLogDifferential
import InfoGeometry.Analysis.BipolarLocalConformalCoordinate
import Mathlib.Tactic

noncomputable section
namespace InfoGeometry.Analysis.BipolarPlanarHodgePair

abbrev PlaneCovector := Fin 2 → ℝ

def hodgeRotate (v : PlaneCovector) : PlaneCovector := ![-v 1, v 0]

@[simp] theorem hodgeRotate_apply_zero (v : PlaneCovector) : hodgeRotate v 0 = -v 1 := rfl
@[simp] theorem hodgeRotate_apply_one (v : PlaneCovector) : hodgeRotate v 1 = v 0 := rfl

theorem hodgeRotate_sq (v : PlaneCovector) : hodgeRotate (hodgeRotate v) = -v := by
  funext i
  fin_cases i <;> simp [hodgeRotate]

def dPhiCoeff (x y : ℝ) : PlaneCovector :=
  ![x / (x ^ 2 + y ^ 2) - (x - 1) / ((x - 1) ^ 2 + y ^ 2),
    y / (x ^ 2 + y ^ 2) - y / ((x - 1) ^ 2 + y ^ 2)]

def dPsiCoeff (x y : ℝ) : PlaneCovector :=
  ![-y / (x ^ 2 + y ^ 2) + y / ((x - 1) ^ 2 + y ^ 2),
    x / (x ^ 2 + y ^ 2) - (x - 1) / ((x - 1) ^ 2 + y ^ 2)]

/-- The planar gradient coefficients are the real-coordinate readout of
the branch-independent logarithmic differential, with the complex-linear sign. -/
theorem dlog01_eq_dPhiCoeff (x y : ℝ) :
    BipolarLogDifferential.dlog01 ⟨x, y⟩ =
      ⟨dPhiCoeff x y 0, -dPhiCoeff x y 1⟩ := by
  have hs : (1 - x) * (1 - x) = (x - 1) ^ 2 := by ring
  apply Complex.ext <;>
    simp [BipolarLogDifferential.dlog01,
      Complex.normSq_apply, dPhiCoeff, hs, ← sq] <;> ring

/-- The globally defined planar gradient has no zero on the punctured domain. -/
theorem dPhiCoeff_ne_zero {x y : ℝ}
    (hs : (⟨x, y⟩ : ℂ) ∈ BipolarCrossRatioLog.punctured01) :
    dPhiCoeff x y ≠ 0 := by
  intro h
  apply BipolarLocalConformalCoordinate.dlog01_ne_zero hs
  rw [dlog01_eq_dPhiCoeff, h]
  apply Complex.ext <;> simp

/-- Along an affine line the derivative of the potential is evaluation of
the planar differential on the direction vector. -/
theorem hasDerivAt_phiXY_line {x y : ℝ}
    (h0 : x ^ 2 + y ^ 2 ≠ 0) (h1 : (x - 1) ^ 2 + y ^ 2 ≠ 0)
    (u v : ℝ) :
    HasDerivAt (fun t => BipolarBoundaryTrace.phiXY (x + t * u) (y + t * v))
      (dPhiCoeff x y 0 * u + dPhiCoeff x y 1 * v) 0 := by
  have hx (a : ℝ) : HasDerivAt (fun t : ℝ => a + t * u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).const_add a
  have hy : HasDerivAt (fun t : ℝ => y + t * v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v).const_add y
  have hg0 := ((hx x).pow 2).add (hy.pow 2)
  have hg1 := (((hx x).sub_const 1).pow 2).add (hy.pow 2)
  have hl0 := hg0.log (by simpa using h0)
  have hl1 := hg1.log (by simpa using h1)
  have hm := (hl0.const_mul (1 / 2 : ℝ)).sub (hl1.const_mul (1 / 2 : ℝ))
  convert hm using 1; simp [dPhiCoeff]; ring

theorem dPsiCoeff_eq_hodgeRotate_dPhiCoeff (x y : ℝ) :
    dPsiCoeff x y = hodgeRotate (dPhiCoeff x y) := by
  ext i
  fin_cases i <;> simp [dPsiCoeff, dPhiCoeff, hodgeRotate]; ring

theorem hodgeRotate_dPsiCoeff (x y : ℝ) :
    hodgeRotate (dPsiCoeff x y) = -dPhiCoeff x y := by
  rw [dPsiCoeff_eq_hodgeRotate_dPhiCoeff, hodgeRotate_sq]

theorem deriv_phiXY_eq_dPhiCoeff_zero
    {x y : ℝ}
    (h0 : x ^ 2 + y ^ 2 ≠ 0)
    (h1 : (x - 1) ^ 2 + y ^ 2 ≠ 0) :
    deriv (fun t => BipolarBoundaryTrace.phiXY t y) x = dPhiCoeff x y 0 := by
  exact (BipolarBoundaryTrace.hasDerivAt_phiXY h0 h1).deriv

theorem dPhiCoeff_half_tangent_zero (y : ℝ) : dPhiCoeff (1 / 2) y 1 = 0 := by
  simp [dPhiCoeff]
  ring

theorem dPhiCoeff_half_normal (y : ℝ) :
    dPhiCoeff (1 / 2) y 0 = 1 / ((1 / 4 : ℝ) + y ^ 2) := by
  have hp : 0 < (1 / 4 : ℝ) + y ^ 2 := by nlinarith [sq_nonneg y]
  simp [dPhiCoeff]
  field_simp [ne_of_gt hp]
  ring

theorem dPsiCoeff_half_normal_zero (y : ℝ) :
    dPsiCoeff (1 / 2) y 0 = 0 := by
  rw [dPsiCoeff_eq_hodgeRotate_dPhiCoeff]
  change -dPhiCoeff (1 / 2) y 1 = 0
  rw [dPhiCoeff_half_tangent_zero]
  simp

theorem dPsiCoeff_half_tangent (y : ℝ) :
    dPsiCoeff (1 / 2) y 1 = 1 / ((1 / 4 : ℝ) + y ^ 2) := by
  rw [dPsiCoeff_eq_hodgeRotate_dPhiCoeff]
  change dPhiCoeff (1 / 2) y 0 = 1 / ((1 / 4 : ℝ) + y ^ 2)
  exact dPhiCoeff_half_normal y

theorem planar_hodge_packet (x y : ℝ) :
    dPsiCoeff x y = hodgeRotate (dPhiCoeff x y) ∧
      hodgeRotate (dPsiCoeff x y) = -dPhiCoeff x y :=
  ⟨dPsiCoeff_eq_hodgeRotate_dPhiCoeff x y, hodgeRotate_dPsiCoeff x y⟩

end InfoGeometry.Analysis.BipolarPlanarHodgePair
