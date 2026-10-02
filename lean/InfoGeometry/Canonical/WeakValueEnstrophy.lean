import InfoGeometry.Canonical.WeakValueSpatialReconstruction

/-!
# Curl enstrophy under weak reconstruction

The functional is the integral of the sum of squared curl components.
Integrability is explicit in the divergence theorem; a nonintegrable Bochner
integral is not used as evidence for a finite enstrophy. This is a conditional
spatial theorem, not a claim that the algebraic UHF colimit is physical space.
-/

noncomputable section
namespace InfoGeometry.Canonical.WeakValueEnstrophy

open Filter MeasureTheory Set
open scoped Topology BigOperators
open WeakValueSpatialReconstruction

def curlEnergy (u : Field) (x : Space) : ℝ := ∑ i, curl u x i ^ 2

/-- Enstrophy without the optional conventional factor 1/2. -/
def enstrophy (mu : Measure Space) (u : Field) : ℝ :=
  ∫ x, curlEnergy u x ∂mu

theorem curlEnergy_nonneg (u : Field) (x : Space) : 0 ≤ curlEnergy u x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (curl u x i))

theorem curlEnergy_reconstruct_uniform (u : Field) (d : ℝ) (x : Space) :
    curlEnergy (reconstruct u (fun _ => d)) x = curlEnergy u x / d ^ 2 := by
  simp only [curlEnergy, curl_reconstruct_uniform, div_pow, Finset.sum_div]

theorem enstrophy_reconstruct_uniform (mu : Measure Space) (u : Field) (d : ℝ) :
    enstrophy mu (reconstruct u (fun _ => d)) = enstrophy mu u / d ^ 2 := by
  simp only [enstrophy, curlEnergy_reconstruct_uniform, integral_div]

theorem integrable_reconstruct_uniform (mu : Measure Space) (u : Field) (d : ℝ)
    (hi : Integrable (curlEnergy u) mu) :
    Integrable (curlEnergy (reconstruct u (fun _ => d))) mu := by
  have he : curlEnergy (reconstruct u (fun _ => d)) =
      fun x => curlEnergy u x / d ^ 2 := by
    funext x
    exact curlEnergy_reconstruct_uniform u d x
  rw [he]
  exact hi.div_const _

/-- Positive inverse-square profiles genuinely tend to infinity from the left. -/
theorem inverse_square_tendsto (a T : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => a / (T - t) ^ 2) (𝓝[<] T) atTop := by
  apply tendsto_atTop.2
  intro B
  let M : ℝ := max B 0 + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hBM : B < M := by dsimp [M]; linarith [le_max_left B 0]
  let delta : ℝ := min 1 (a / M)
  have hd : 0 < delta := lt_min zero_lt_one (div_pos ha hM)
  filter_upwards [Ioo_mem_nhdsLT (show T - delta < T by linarith)] with t ht
  have hg : 0 < T - t := by linarith [ht.2]
  have hg1 : T - t < 1 := lt_of_lt_of_le (by linarith [ht.1]) (min_le_left _ _)
  have hga : T - t < a / M :=
    lt_of_lt_of_le (by linarith [ht.1]) (min_le_right _ _)
  have hmul : (T - t) * M < a := (lt_div_iff₀ hM).mp hga
  have hsq : (T - t) ^ 2 ≤ T - t := by nlinarith
  have hmulsq : M * (T - t) ^ 2 < a := by nlinarith
  have hlarge : M < a / (T - t) ^ 2 :=
    (lt_div_iff₀ (sq_pos_of_pos hg)).2 hmulsq
  exact (hBM.trans hlarge).le

/-- A positive-enstrophy current and uniform shrinking overlap force actual
enstrophy divergence, with finite enstrophy at every pre-seam time. -/
theorem enstrophy_blowup (mu : Measure Space) (j : Field) (T : ℝ)
    (hi : Integrable (curlEnergy j) mu) (hE : 0 < enstrophy mu j) :
    (∀ t < T, Integrable (curlEnergy (reconstruct j (fun _ => T - t))) mu) ∧
    Tendsto (fun t => enstrophy mu (reconstruct j (fun _ => T - t)))
      (𝓝[<] T) atTop := by
  constructor
  · intro t _
    exact integrable_reconstruct_uniform mu j (T - t) hi
  · have he : (fun t => enstrophy mu (reconstruct j (fun _ => T - t))) =
        fun t => enstrophy mu j / (T - t) ^ 2 := by
      funext t
      exact enstrophy_reconstruct_uniform mu j (T - t)
    rw [he]
    exact inverse_square_tendsto _ T hE

/-- Coercive spatial lower bounds also suffice without an exact profile. -/
theorem enstrophy_blowup_of_lower_bound (mu : Measure Space)
    (u : ℝ → Field) (weight : Space → ℝ) (T : ℝ)
    (hw : Integrable weight mu) (hm : 0 < ∫ x, weight x ∂mu)
    (hu : ∀ t < T, Integrable (curlEnergy (u t)) mu)
    (hlower : ∀ t < T, ∀ᵐ x ∂mu,
      weight x / (T - t) ^ 2 ≤ curlEnergy (u t) x) :
    Tendsto (fun t => enstrophy mu (u t)) (𝓝[<] T) atTop := by
  apply tendsto_atTop.2
  intro B
  have hlarge := (tendsto_atTop.1 (inverse_square_tendsto _ T hm)) B
  filter_upwards [hlarge, Ioo_mem_nhdsLT (show T - 1 < T by linarith)] with t ht htT
  have hle := integral_mono_ae (hw.div_const ((T - t) ^ 2))
    (hu t htT.2) (hlower t htT.2)
  rw [integral_div] at hle
  exact ht.trans hle

end InfoGeometry.Canonical.WeakValueEnstrophy
