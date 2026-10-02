import InfoGeometry.Canonical.TwoStateMomentumShear
import InfoGeometry.Canonical.ReciprocalShearFlow

/-!
# Exact momentum reconstruction and regional enstrophy divergence

This module connects the explicit smooth two-state fields to an actual
three-dimensional forced Navier–Stokes shear. Units are chosen so that the
momentum-to-velocity factor is one. Every momentum component uses the native
derivative along its spatial coordinate; no PDE projection is assumed.

The reconstructed forcing diverges at the same terminal time. This is an
exact local example, not a smooth-forcing global breakdown alternative or a
wave evolution theorem. The existing `weakValue?` guard excludes zero overlap.
-/

noncomputable section

namespace InfoGeometry.Canonical.TwoStateNavierStokesReconstruction

open NavierStokesShearReconstruction TwoStateMomentumShear
open MeasureTheory Filter
open scoped Topology ContDiff ENNReal

def preparation (x : Space) : Spinor := pre (x 1)
def postselection (T t : ℝ) (x : Space) : Spinor := post (T - t) (x 0) (x 1)

/-- Actual spatial momentum, `-i ∂ᵢ`, applied to the preparation. -/
def spatialMomentum (x : Space) (i : Fin 3) : Spinor :=
  (-Complex.I) • deriv (fun r => preparation (Function.update x i r)) (x i)

/-- Totalized expression; its physical domain is fixed by `regular_readout`. -/
def reconstructed (T : ℝ) : Velocity := fun t x i =>
  (inner ℂ (postselection T t x) (spatialMomentum x i) /
    inner ℂ (postselection T t x) (preparation x)).re

theorem spatialMomentum_eq (x : Space) :
    spatialMomentum x = ![0, momentum (x 1), 0] := by
  funext i
  fin_cases i <;> simp [spatialMomentum, preparation, momentum_eq_actual_derivative]

theorem transition_amplitude (T t : ℝ) (x : Space) :
    inner ℂ (postselection T t x) (preparation x) = ((T - t : ℝ) : ℂ) :=
  overlap_eq (T - t) (x 0) (x 1)

/-- Exact equality with the independently differentiated shear field. -/
theorem reconstructed_eq_velocity (T : ℝ) : reconstructed T = ReciprocalShearFlow.velocity T := by
  funext t x i
  fin_cases i
  · simp [reconstructed, spatialMomentum_eq, ReciprocalShearFlow.velocity, shear]
  · simp only [reconstructed, spatialMomentum_eq]
    change weakReadout (T - t) (x 0) (x 1) = (T - t)⁻¹ * x 0
    rw [weakReadout_eq, div_eq_mul_inv, mul_comm]
  · simp [reconstructed, spatialMomentum_eq, ReciprocalShearFlow.velocity, shear]

/-- The existing finite boundary guard agrees with the spatial derivative
readout on this preparation family, throughout `t ≠ T`. -/
theorem regular_readout (T t : ℝ) (ht : t ≠ T) (x : Space) :
    SarsModularWeakValue.weakValue? momentumMatrix (rawPre (x 1))
      (rawPost (T - t) (x 0) (x 1)) = some ((reconstructed T t x 1 : ℝ) : ℂ) := by
  rw [reconstructed_eq_velocity]
  simpa [ReciprocalShearFlow.velocity, shear, ReciprocalShearFlow.profile,
    div_eq_mul_inv, mul_comm] using
    guarded_readout (sub_ne_zero.mpr (Ne.symm ht)) (x 0) (x 1)

theorem readout_guard_at_terminal_time (T : ℝ) (x : Space) :
    SarsModularWeakValue.weakValue? momentumMatrix (rawPre (x 1))
      (rawPost (T - T) (x 0) (x 1)) = none := by
  simpa using guarded_readout_at_zero (x 0) (x 1)

theorem reconstructed_satisfiesAt (ν T t : ℝ) (ht : t ≠ T) (x : Space) :
    SatisfiesAt ν (reconstructed T) (fun _ _ => 0)
      (ReciprocalShearFlow.forcing T) t x := by
  rw [reconstructed_eq_velocity]
  exact ReciprocalShearFlow.satisfiesAt_velocity ν T t ht x

theorem reconstructed_cube_enstrophy_tendsto_top (T : ℝ) :
    Tendsto (fun t => ReciprocalShearFlow.enstrophy ReciprocalShearFlow.cubeVolume
      (reconstructed T t)) (𝓝[<] T) (𝓝 ∞) := by
  rw [reconstructed_eq_velocity]
  exact ReciprocalShearFlow.cube_enstrophy_tendsto_top T

/-- Smoothness of the state in time includes the zero-overlap time itself. -/
theorem contDiff_postselection_time (T : ℝ) (x : Space) :
    ContDiff ℝ ∞ (fun t => postselection T t x) := by
  exact contDiff_post.comp ((contDiff_const.sub contDiff_id).prodMk
    (contDiff_const.prodMk contDiff_const))

/-- On the integration region, zero overlap occurs between two nonzero states. -/
theorem terminal_states_ne_zero (T : ℝ) (x : Space)
    (hx : x ∈ ReciprocalShearFlow.unitCube) :
    preparation x ≠ 0 ∧ postselection T T x ≠ 0 := by
  refine ⟨pre_ne_zero (x 1), ?_⟩
  have hx0 : 0 < x 0 := (hx 0 (Set.mem_univ 0)).1
  simpa [postselection] using post_at_node_ne_zero (ne_of_gt hx0) (x 1)

end InfoGeometry.Canonical.TwoStateNavierStokesReconstruction
