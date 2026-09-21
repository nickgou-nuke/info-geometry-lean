import InfoGeometry.Canonical.NavierStokesShearReconstruction
import InfoGeometry.Canonical.EnstrophyDivergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A forced shear with finite-time regional enstrophy divergence

The velocity is `u(t,x) = (0, x₀/(T-t), 0)`, with pressure zero and
`f(t,x) = (0, x₀/(T-t)², 0)`. Every derivative in the PDE is computed.
The vorticity is spatially constant, so the enstrophy on the open unit cube
is exactly `(T-t)⁻²` and tends to infinity as `t ↑ T`.

The forcing itself is singular at `T`; the velocity also grows at spatial
infinity. Thus this local example does not satisfy the global forcing and
finite-energy hypotheses of a Clay breakdown alternative.
-/

noncomputable section

namespace InfoGeometry.Canonical.ReciprocalShearFlow

open NavierStokesShearReconstruction MeasureTheory Set Filter
open scoped Topology ENNReal

def profile (T t r : ℝ) : ℝ := (T - t)⁻¹ * r
def forcingProfile (T t r : ℝ) : ℝ := ((T - t) ^ 2)⁻¹ * r
def velocity (T : ℝ) : Velocity := shear (profile T)
def forcing (T : ℝ) : Velocity := shear (forcingProfile T)

theorem hasDerivAt_profile_space (T t r : ℝ) :
    HasDerivAt (profile T t) (T - t)⁻¹ r := by
  simpa [profile] using (hasDerivAt_id r).const_mul (T - t)⁻¹

@[simp] theorem deriv_profile_space (T t : ℝ) :
    deriv (profile T t) = (fun _ => (T - t)⁻¹) :=
  funext (fun r => (hasDerivAt_profile_space T t r).deriv)

theorem hasDerivAt_reciprocal_time (T t : ℝ) (ht : t ≠ T) :
    HasDerivAt (fun s => (T - s)⁻¹) ((T - t) ^ 2)⁻¹ t := by
  have hn : T - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  simpa using ((hasDerivAt_id t).const_sub T).inv hn

theorem hasDerivAt_profile_time (T t r : ℝ) (ht : t ≠ T) :
    HasDerivAt (fun s => profile T s r) (forcingProfile T t r) t :=
  (hasDerivAt_reciprocal_time T t ht).mul_const r

/-- A pointwise classical PDE identity on the open time domain `t ≠ T`. -/
theorem satisfiesAt_velocity (ν T t : ℝ) (ht : t ≠ T) (x : Space) :
    SatisfiesAt ν (velocity T) (fun _ _ => 0) (forcing T) t x := by
  rw [velocity, forcing, satisfiesAt_shear_iff]
  rw [(hasDerivAt_profile_time T t (x 0) ht).deriv, deriv_profile_space]
  simp

theorem curl_velocity (T t : ℝ) (x : Space) :
    curl (velocity T t) x = ![0, 0, (T - t)⁻¹] := by
  simp [velocity, curl_shear]

/-- Sum of squared Cartesian components, the Euclidean vorticity norm squared. -/
def vorticitySq (v : Space → Space) (x : Space) : ℝ :=
  ∑ i, (curl v x i) ^ 2

theorem vorticitySq_eq_norm_sq (v : Space → Space) (x : Space) :
    vorticitySq v x = ‖(WithLp.toLp 2 (curl v x) : EuclideanSpace ℝ (Fin 3))‖ ^ 2 := by
  simp [vorticitySq, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs]

/-- Extended nonnegative integral: divergent enstrophy is represented by `∞`. -/
def enstrophy (μ : Measure Space) (v : Space → Space) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (vorticitySq v x) ∂μ

theorem vorticitySq_velocity (T t : ℝ) (x : Space) :
    vorticitySq (velocity T t) x = ((T - t)⁻¹) ^ 2 := by
  simp [vorticitySq, curl_velocity, Fin.sum_univ_succ]

def unitCube : Set Space := pi univ (fun _ => Ioo (0 : ℝ) 1)
def cubeVolume : Measure Space := volume.restrict unitCube

theorem cubeVolume_univ : cubeVolume univ = 1 := by
  simp [cubeVolume, unitCube, Real.volume_pi_Ioo]

theorem enstrophy_velocity (μ : Measure Space) (hμ : μ univ = 1) (T t : ℝ) :
    enstrophy μ (velocity T t) = ENNReal.ofReal (((T - t)⁻¹) ^ 2) := by
  simp only [enstrophy, vorticitySq_velocity]
  exact EnstrophyDivergence.uniform_enstrophy μ hμ _

/-- Actual regional enstrophy of the reconstructed three-dimensional flow. -/
theorem cube_enstrophy_tendsto_top (T : ℝ) :
    Tendsto (fun t => enstrophy cubeVolume (velocity T t)) (𝓝[<] T) (𝓝 ∞) := by
  simp only [enstrophy, vorticitySq_velocity]
  exact EnstrophyDivergence.reciprocal_time_enstrophy_tendsto_top
    cubeVolume cubeVolume_univ T

/-- The driving force is also unbounded: smooth forcing through `T` is absent. -/
theorem forcing_component_tendsto_atTop (T : ℝ) :
    Tendsto (fun t => forcing T t ![1, 0, 0] 1) (𝓝[<] T) atTop := by
  have h := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
    (EnstrophyDivergence.reciprocal_time_tendsto_atTop T)
  simpa [forcing, shear, forcingProfile, inv_pow, Function.comp_def] using h

end InfoGeometry.Canonical.ReciprocalShearFlow
