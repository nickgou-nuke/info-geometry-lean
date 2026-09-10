import InfoGeometry.Canonical.WeakValueEnstrophy
import InfoGeometry.Streaming.WeakValueBoundary

/-!
# An explicit weak-state reconstruction satisfying a forced NS equation

u(t,x) = (0, x_0 / (T-t), 0), p = 0,
f(t,x) = (0, x_0 / (T-t)^2, 0).

The bounded Pauli probe and affine post-state give the nonzero velocity
component exactly as a weak readout. The state is continuous through T; the
guarded readout is undefined there. On t < T, the coordinate PDE holds for
every viscosity. The forcing is singular at T and the shear is not globally
finite-energy on R^3. This is not the OpenAI admissible-forcing theorem, a
periodic solution, or the unforced regularity problem.
-/

noncomputable section
namespace InfoGeometry.Canonical.WeakValueForcedShear

open scoped BigOperators Topology
open MeasureTheory Filter
open WeakValueSpatialReconstruction WeakValueEnstrophy
open SarsModularWeakValue
open InfoGeometry.Physics.NuclearWignerSupermultiplet

def velocity (T t : ℝ) : Field := fun x => ![0, x 0 / (T - t), 0]
def forcing (T t : ℝ) : Field := fun x => ![0, x 0 / (T - t) ^ 2, 0]
def current : Field := fun x => ![0, x 0, 0]

theorem velocity_reconstruction (T t : ℝ) :
    velocity T t = reconstruct current (fun _ => T - t) := by
  funext x i
  fin_cases i <;> simp [velocity, reconstruct, current]

theorem current_curl (x : Space) : curl current x = ![0, 0, 1] := by
  funext i
  fin_cases i <;> simp [curl, current, partial, coordinate]

theorem current_curlEnergy (x : Space) : curlEnergy current x = 1 := by
  simp [curlEnergy, current_curl, Fin.sum_univ_succ]

theorem current_enstrophy (mu : Measure Space) [IsProbabilityMeasure mu] :
    enstrophy mu current = 1 := by
  simp [enstrophy, current_curlEnergy]

theorem velocity_enstrophy (mu : Measure Space) [IsProbabilityMeasure mu] (T t : ℝ) :
    enstrophy mu (velocity T t) = 1 / (T - t) ^ 2 := by
  rw [velocity_reconstruction, enstrophy_reconstruct_uniform, current_enstrophy]

theorem velocity_enstrophy_blowup (mu : Measure Space) [IsProbabilityMeasure mu]
    (T : ℝ) :
    Tendsto (fun t => enstrophy mu (velocity T t)) (𝓝[<] T) atTop := by
  have he : (fun t => enstrophy mu (velocity T t)) =
      fun t => 1 / (T - t) ^ 2 := by
    funext t
    exact velocity_enstrophy mu T t
  rw [he]
  exact inverse_square_tendsto 1 T zero_lt_one

def postState (T t : ℝ) (x : Space) : State2 :=
  ![((T - t : ℝ) : ℂ), ((x 0 : ℝ) : ℂ)]

theorem postState_continuous (T : ℝ) (x : Space) :
    Continuous (fun t => postState T t x) := by
  unfold postState
  fun_prop

theorem post_overlap (T t : ℝ) (x : Space) :
    weakDenominator ket0 (postState T t x) = ((T - t : ℝ) : ℂ) := by
  simp [weakDenominator, cinner, ket0, postState]

theorem post_momentum (T t : ℝ) (x : Space) :
    weakNumerator pauli1 ket0 (postState T t x) = ((x 0 : ℝ) : ℂ) := by
  simp [weakNumerator, matVec, cinner, ket0, postState, pauli1]

theorem pauli_readout (T t : ℝ) (x : Space) (ht : t < T) :
    weakValue? pauli1 ket0 (postState T t x) =
      some (((x 0 / (T - t) : ℝ) : ℂ)) := by
  have hd : ((T - t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sub_pos.mpr ht))
  rw [weak_value_some_of_nonorthogonal _ _ _ (by rwa [post_overlap]),
    post_momentum, post_overlap]
  congr 1
  exact (Complex.ofReal_div _ _).symm

theorem velocity_is_real_weak_readout (T t : ℝ) (x : Space) (ht : t < T) :
    (weakValue? pauli1 ket0 (postState T t x)).map Complex.re =
      some (velocity T t x 1) := by
  rw [pauli_readout T t x ht]
  simp [velocity]

theorem seam_readout_undefined (T : ℝ) (x : Space) :
    weakValue? pauli1 ket0 (postState T T x) = none := by
  apply weak_value_none_of_orthogonal
  simp [post_overlap]

theorem velocity_partial (T t : ℝ) (x : Space) (i k : Fin 3) :
    partial (fun y => velocity T t y i) x k =
      if i = 1 ∧ k = 0 then 1 / (T - t) else 0 := by
  fin_cases i <;> fin_cases k <;> simp [velocity, partial, coordinate]

theorem velocity_divergence (T t : ℝ) (x : Space) :
    divergence (velocity T t) x = 0 := by
  simp [divergence, velocity_partial, Fin.sum_univ_succ]

theorem velocity_laplacian (T t : ℝ) (x : Space) (i : Fin 3) :
    laplacian (fun y => velocity T t y i) x = 0 := by
  simp only [laplacian]
  simp_rw [velocity_partial]
  simp [partial]

theorem velocity_advection (T t : ℝ) (x : Space) (i : Fin 3) :
    (∑ k, velocity T t x k * partial (fun y => velocity T t y i) x k) = 0 := by
  fin_cases i <;> simp [velocity_partial, velocity, Fin.sum_univ_succ]

theorem hasDerivAt_velocity (T t : ℝ) (x : Space) (i : Fin 3) (ht : t < T) :
    HasDerivAt (fun s => velocity T s x i) (forcing T t x i) t := by
  have hd : T - t ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  have h := (hasDerivAt_const t (x 0)).div
    ((hasDerivAt_const t T).sub (hasDerivAt_id t)) hd
  fin_cases i
  · simpa [velocity, forcing] using hasDerivAt_const t (0 : ℝ)
  · simpa [velocity, forcing] using h
  · simpa [velocity, forcing] using hasDerivAt_const t (0 : ℝ)

theorem velocity_time_derivative (T t : ℝ) (x : Space) (i : Fin 3) (ht : t < T) :
    deriv (fun s => velocity T s x i) t = forcing T t x i :=
  (hasDerivAt_velocity T t x i ht).deriv

theorem velocity_regularity (T : ℝ) :
    ClassicalRegularityOn (Set.Iio T) (velocity T) (fun _ _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht x i
    exact (hasDerivAt_velocity T t x i ht).differentiableAt
  · intro t ht
    have hd : T - t ≠ 0 := ne_of_gt (sub_pos.mpr ht)
    unfold velocity
    fun_prop (disch := assumption)
  · intro t _
    fun_prop

/-- A genuine coordinate PDE calculation, with its singular forcing exposed. -/
theorem solves_forced_navier_stokes (nu T : ℝ) :
    SolvesNavierStokesOn (Set.Iio T) nu (velocity T) (fun _ _ => 0) (forcing T) := by
  refine ⟨velocity_regularity T, ?_, ?_⟩
  · intro t _ x
    exact velocity_divergence T t x
  · intro t ht x i
    simp [nsResidual, velocity_time_derivative T t x i ht,
      velocity_advection, velocity_laplacian, partial]

end InfoGeometry.Canonical.WeakValueForcedShear
