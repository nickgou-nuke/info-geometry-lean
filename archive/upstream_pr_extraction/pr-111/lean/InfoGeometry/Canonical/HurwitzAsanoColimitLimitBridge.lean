import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Hurwitz–Asano Colimit Limit Bridge

This module formalizes:
1. **A conditional Hurwitz zero-free interface:**
   once the analytic zero-set dichotomy for the limit is supplied as an
   explicit hypothesis, non-vanishing at a single basepoint transfers to
   strict zero-freeness on all of $U$:
   $$\left(\forall n, \forall z \in U, f_n(z) \neq 0\right) \wedge f(z_0) \neq 0 \implies \forall z \in U, f(z) \neq 0.$$

2. **Conditional Asano–Lee–Yang zero transfer:**
   For a finite packet that is zero-free in the open unit disk, the limit is
   zero-free there only after an explicit limit dichotomy is supplied; the
   normalization at the origin selects the zero-free branch.

3. **Thermodynamic boundary-limit localization:**
   Since all approximating zeros lie on the unit circle, its closedness sends
   every convergent zero sequence to the same boundary. This does not claim
   that every limit zero is represented by such a sequence.

4. **Möbius–Cayley projection to the critical axis:**
   Via the Cayley correspondence $w = \frac{1-z}{1+z}$, the circle boundary
   away from $z=-1$ is mapped to the imaginary axis. This coordinate fact
   does not identify Lee–Yang zeros with zeros of $\xi$.
-/

noncomputable section

namespace InfoGeometry.Canonical.HurwitzAsano

open Set Filter Topology Complex

/-! ## 0. Kernel-checked moving-zero transfer -/

/-- Uniform-limit data for a sequence of moving zeros converging to a boundary point. -/
structure MovingZeroUniformLimitData where
  approximant : ℕ → ℂ → ℂ
  limit : ℂ → ℂ
  zeroSeq : ℕ → ℂ
  boundary : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  limit_continuousAt : ContinuousAt limit boundary
  locally_uniform :
    TendstoUniformlyOn approximant limit atTop (Metric.closedBall boundary radius)
  zero_at_stage : ∀ n, approximant n (zeroSeq n) = 0
  zeroSeq_tendsto : Tendsto zeroSeq atTop (𝓝 boundary)

/--
If the limit is continuous at `boundary`, the approximants converge uniformly
on a closed neighbourhood, and their zeros converge to `boundary`, then the
limit vanishes at `boundary`.

This is an elementary moving-zero/uniform-limit lemma.  It is not the Hurwitz
theorem: no holomorphicity, zero-free dichotomy, or converse is proved here.
-/
theorem continuous_limit_eq_zero_of_moving_zero (D : MovingZeroUniformLimitData) :
    D.limit D.boundary = 0 := by
  have h_eventually_in_ball :
      ∀ᶠ n : ℕ in atTop,
        D.zeroSeq n ∈ Metric.closedBall D.boundary D.radius := by
    obtain ⟨N, hN⟩ :=
      (Metric.tendsto_atTop.mp D.zeroSeq_tendsto) D.radius D.radius_pos
    filter_upwards [eventually_ge_atTop N] with n hn
    exact Metric.mem_closedBall.mpr (le_of_lt (hN n hn))
  apply tendsto_nhds_unique
    (l := atTop)
    (f := fun n => D.limit (D.zeroSeq n))
  · exact D.limit_continuousAt.tendsto.comp D.zeroSeq_tendsto
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    rw [Metric.tendsto_atTop]
    intro ε hε
    have h_uniform : ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ Metric.closedBall D.boundary D.radius,
          dist (D.limit x) (D.approximant n x) < ε :=
      (Metric.tendstoUniformlyOn_iff.mp D.locally_uniform) ε hε
    have h_eventually_dist : ∀ᶠ n : ℕ in atTop,
        dist ‖D.limit (D.zeroSeq n)‖ 0 < ε := by
      filter_upwards [h_uniform, h_eventually_in_ball] with n hn hball
      have hdist :
          dist (D.limit (D.zeroSeq n))
            (D.approximant n (D.zeroSeq n)) < ε :=
        hn (D.zeroSeq n) hball
      rw [D.zero_at_stage n, dist_zero_right] at hdist
      simpa [dist_zero_right] using hdist
    exact Filter.eventually_atTop.mp h_eventually_dist

/-! ## 1. Supplied zero-free dichotomy -/

/-- A limit function together with an explicit zero/zero-free dichotomy.

The dichotomy is a field, not a consequence proved by this structure. -/
structure LimitDichotomyData (U : Set ℂ) where
  flim : ℂ → ℂ
  /-- Zero-free limit dichotomy, supplied explicitly at this interface.

  Proving this field from local uniform convergence and holomorphicity is a
  separate analytic owner target. -/
  h_dichotomy : (∀ z ∈ U, flim z = 0) ∨ (∀ z ∈ U, flim z ≠ 0)

/-- Read back the explicitly supplied dichotomy for the limit. -/
theorem zero_free_limit_dichotomy_of_data (U : Set ℂ)
    (data : LimitDichotomyData U) :
    (∀ z ∈ U, data.flim z = 0) ∨ (∀ z ∈ U, data.flim z ≠ 0) :=
  data.h_dichotomy

/-- Zero-free transfer from the supplied dichotomy and a nonzero basepoint. -/
theorem zero_free_limit_transfer_of_data (U : Set ℂ)
    (data : LimitDichotomyData U)
    (z0 : ℂ) (hz0 : z0 ∈ U) (h_nontriv : data.flim z0 ≠ 0) :
    ∀ z ∈ U, data.flim z ≠ 0 := by
  cases zero_free_limit_dichotomy_of_data U data with
  | inl h_ident_zero =>
    have : data.flim z0 = 0 := h_ident_zero z0 hz0
    exact False.elim (h_nontriv this)
  | inr h_zerofree =>
    exact h_zerofree

/-! ## 2. Open Unit Disk and Asano Colimit Limit -/

/-- The open unit disk domain 𝔻 = {z : ℂ | ‖z‖ < 1} -/
def openUnitDisk : Set ℂ := Metric.ball 0 1

/-- 🏆 THEOREM 3: The Open Unit Disk is Connected -/
theorem openUnitDisk_isConnected : IsConnected openUnitDisk :=
  (convex_ball (0 : ℂ) 1).isConnected ⟨0, Metric.mem_ball_self (by norm_num)⟩

/-- 🏆 THEOREM 4: The Open Unit Disk is Nonempty -/
theorem openUnitDisk_nonempty : openUnitDisk.Nonempty :=
  ⟨0, Metric.mem_ball_self (by norm_num)⟩

/-- Thermodynamic Asano limit readout on the Open Unit Disk.

The finite approximants are intentionally not fields of this structure:
the theorem below uses only the supplied dichotomy and normalization.
Local-uniform convergence and finite-stage zero-freeness belong to a separate
Hurwitz realization theorem, not to this conditional readout. -/
structure AsanoColimitDiskData where
  /-- Colimit limit partition function P_∞ -/
  P_inf : ℂ → ℂ
  /-- Normalization at origin P_∞(0) = 1 -/
  h_norm_origin : P_inf 0 = 1
  /-- Supplied zero/zero-free dichotomy for the limit on the disk. -/
  h_dichotomy : (∀ z ∈ openUnitDisk, P_inf z = 0) ∨ (∀ z ∈ openUnitDisk, P_inf z ≠ 0)

/-- Zero-free transfer for a disk packet with an explicitly supplied limit dichotomy. -/
theorem asano_colimit_zerofree_of_supplied_dichotomy (data : AsanoColimitDiskData) :
    ∀ z ∈ openUnitDisk, data.P_inf z ≠ 0 := by
  have h0_in : (0 : ℂ) ∈ openUnitDisk := Metric.mem_ball_self (by norm_num)
  have h0_ne : data.P_inf 0 ≠ 0 := by
    rw [data.h_norm_origin]
    exact one_ne_zero
  have h_trans := zero_free_limit_transfer_of_data openUnitDisk
    ⟨data.P_inf, data.h_dichotomy⟩
    0 h0_in h0_ne
  exact h_trans

/-! ## 3. Closedness of the Lee-Yang Phase Transition Unit Circle -/

/-- The unit circle boundary 𝕊¹ = {z : ℂ | ‖z‖ = 1} -/
def unitCircle : Set ℂ := Metric.sphere 0 1

/-- 🏆 THEOREM 6: Closedness of the Unit Circle Locus -/
theorem unitCircle_isClosed : IsClosed unitCircle :=
  Metric.isClosed_sphere

/-- 🏆 THEOREM 7: Unit Circle Limit Conservation.
    If a sequence of zeros z_N of the finite partition functions lies on 𝕊¹,
    any convergent subsequence limit z_* must also lie on 𝕊¹. -/
theorem leeyang_zeros_limit_on_unit_circle
    (z_seq : ℕ → ℂ) (z_star : ℂ)
    (h_on_circle : ∀ N, z_seq N ∈ unitCircle)
    (h_lim : Tendsto z_seq atTop (nhds z_star)) :
    z_star ∈ unitCircle :=
  unitCircle_isClosed.mem_of_tendsto h_lim (Filter.Eventually.of_forall h_on_circle)

/-! ## 4. Möbius–Cayley Transform to the Critical Axis -/

/-- Standard Cayley / Möbius transform mapping the unit disk to the right half-plane -/
def cayleyTransform (z : ℂ) : ℂ :=
  (1 - z) / (1 + z)

/-- 🏆 THEOREM 8: Cayley Map sends the Unit Circle to the Imaginary Axis.
    For z = e^{iθ} (‖z‖ = 1, z ≠ -1), Re(Cayley(z)) = 0. -/
theorem cayley_unit_circle_maps_to_imaginary_axis (z : ℂ) (hz_circle : ‖z‖ = 1) (hz_ne : z ≠ -1) :
    (cayleyTransform z).re = 0 := by
  dsimp [cayleyTransform]
  have h_den : 1 + z ≠ 0 := by
    intro hzero
    have h_re : z.re = -1 := by
      have := congrArg Complex.re hzero
      simp at this
      linarith
    have h_im : z.im = 0 := by
      have := congrArg Complex.im hzero
      simp at this
      exact this
    apply hz_ne
    apply Complex.ext
    · exact h_re
    · simpa using h_im
  have h_norm_ne : Complex.normSq (1 + z) ≠ 0 :=
    mt Complex.normSq_eq_zero.mp h_den
  have h_normSq : Complex.normSq z = 1 := by
    have h_norm_sq : ‖z‖ ^ 2 = 1 := by rw [hz_circle, one_pow]
    have h_norm_def : Complex.normSq z = ‖z‖ ^ 2 := by
      rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z)]
    rw [h_norm_def, h_norm_sq]
  rw [Complex.div_re]
  have h_num : (1 - z).re * (1 + z).re + (1 - z).im * (1 + z).im = 0 := by
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
               Complex.one_re, Complex.one_im]
    have h_norm_expand : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by
      simp [Complex.normSq, sq]
    have h_alg : (1 - z.re) * (1 + z.re) + (0 - z.im) * (0 + z.im) = 1 - (z.re ^ 2 + z.im ^ 2) := by ring
    rw [h_alg, ← h_norm_expand, h_normSq]
    ring
  have h_div : (1 - z).re * (1 + z).re / normSq (1 + z) + (1 - z).im * (1 + z).im / normSq (1 + z) =
      ((1 - z).re * (1 + z).re + (1 - z).im * (1 + z).im) / normSq (1 + z) := by ring
  rw [h_div, h_num]
  field_simp [h_norm_ne]
  ring

/-- Combine the two conditional consequences for a supplied packet. -/
theorem asano_colimit_zero_free_and_circle_limit
    (data : AsanoColimitDiskData)
    (z_seq : ℕ → ℂ) (z_star : ℂ)
    (h_on_circle : ∀ N, z_seq N ∈ unitCircle)
    (h_lim : Tendsto z_seq atTop (nhds z_star)) :
    (∀ z ∈ openUnitDisk, data.P_inf z ≠ 0) ∧
    (z_star ∈ unitCircle) :=
  ⟨asano_colimit_zerofree_of_supplied_dichotomy data,
   leeyang_zeros_limit_on_unit_circle z_seq z_star h_on_circle h_lim⟩

end InfoGeometry.Canonical.HurwitzAsano
