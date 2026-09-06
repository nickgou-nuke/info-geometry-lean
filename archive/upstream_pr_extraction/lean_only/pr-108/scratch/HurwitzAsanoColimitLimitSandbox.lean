import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Analysis.AsanoLeeYangCircleBridge

/-!
# Hurwitz–Asano Colimit Limit Sandbox

This sandbox formalizes:
1. **A theorem-safe conditional interface:**
   once a zero/zero-free dichotomy for the limit has been supplied as an
   explicit hypothesis, non-vanishing at a single basepoint transfers to
   strict zero-freeness on all of $U$:
   $$\left(\forall n, \forall z \in U, f_n(z) \neq 0\right) \wedge f(z_0) \neq 0 \implies \forall z \in U, f(z) \neq 0.$$

2. **A conditional Asano–Lee–Yang limit readout:**
   If a supplied limit function on the open unit disk has a zero/zero-free
   dichotomy and is normalized at the origin ($P_\infty(0) = 1 \neq 0$),
   then it is zero-free on the disk.  Finite-stage convergence is not encoded
   by this readout.

3. **Boundary-limit localization (independent of Hurwitz):**
   Since all approximating zeros lie on the unit circle, closedness of the
   unit circle sends every convergent zero sequence to the same boundary.
   This is a sequential closedness theorem, not a claim that every limit
   zero is obtained by such a sequence.

4. **Möbius–Cayley Projection to the Imaginary Axis:**
   Via the Cayley correspondence $w = \frac{1-z}{1+z}$, the circle boundary
   $\mathbb{S}^1$ (away from $z=-1$) is mapped to the imaginary axis
   $\operatorname{Re}(w) = 0$. This coordinate statement does not identify
   Lee–Yang zeros with zeros of $\xi$; an additional affine shift is needed
   before interpreting this axis as the critical line.
-/

noncomputable section

namespace InfoGeometry.Canonical.HurwitzAsano

open Set Filter Topology Complex
open InfoGeometry.Analysis.AsanoLeeYangCircle

/-! ## 0. Kernel-checked moving-zero transfer

The conditional dichotomy interface below is not a proof of Hurwitz' theorem.
The following datum contains only the hypotheses used by the elementary
moving-zero implication: local uniform convergence on a compact
neighbourhood, continuity of the limit, zeros of the approximants, and
convergence of the zero locations.
-/

/-- Uniform-limit data for a sequence of moving zeros converging to a boundary point.

This is an elementary continuity/uniform-convergence lemma.  It is not a
formalization of Hurwitz' theorem and therefore carries no unused
holomorphicity fields. -/
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

/-- If a sequence of approximants converges uniformly on a neighbourhood and
their zeros converge to `boundary`, then the continuous limit vanishes there.
This is only the moving-zero implication; it is not Hurwitz' theorem. -/
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

/--
Compositional boundary readout.

The first conjunct is the locally-uniform Hurwitz moving-zero transfer above.
The second conjunct uses only the independent unit-circle boundary hypothesis
and the canonical Cayley inverse.  This is a coordinate consequence; it does
not identify the limit function with `xi` or with a Lee--Yang partition
function.
-/
theorem hurwitz_boundary_zero_cayley_critical_line
    (D : MovingZeroUniformLimitData)
    (h_boundary_circle : ‖D.boundary‖ = 1)
    (h_boundary_ne_neg_one : D.boundary ≠ -1) :
    D.limit D.boundary = 0 ∧
      (riemannCayleyInverse D.boundary).re = 1 / 2 := by
  refine ⟨continuous_limit_eq_zero_of_moving_zero D, ?_⟩
  exact re_riemannCayleyInverse_eq_half_of_norm_eq_one
    h_boundary_circle h_boundary_ne_neg_one

/-! ## 1. Conditional zero-dichotomy interface on connected domains -/

/-- A supplied zero/zero-free dichotomy on a domain `U`.

This structure contains the conclusion normally obtained from an analytic
Hurwitz argument as an explicit input.  It is not the sequence-level
hypothesis of Hurwitz' theorem. -/
structure SuppliedZeroDichotomyData (U : Set ℂ) where
  /-- The limit function -/
  flim : ℂ → ℂ
  /-- Analytic Hurwitz dichotomy, supplied explicitly at this interface.

  This field is intentionally not proved here: proving it from local uniform
  convergence and holomorphicity is the genuine analytic Hurwitz theorem and
  remains a separate owner target. -/
  h_dichotomy : (∀ z ∈ U, flim z = 0) ∨ (∀ z ∈ U, flim z ≠ 0)

/-- Conditional readout of the supplied analytic Hurwitz dichotomy. -/
theorem supplied_zero_dichotomy
    (U : Set ℂ) (data : SuppliedZeroDichotomyData U) :
    (∀ z ∈ U, data.flim z = 0) ∨ (∀ z ∈ U, data.flim z ≠ 0) :=
  data.h_dichotomy

/-- Conditional Hurwitz zero-transfer.

The only analytic input is `data.h_dichotomy`; therefore this theorem is a
finite logical consequence of that explicit premise, not an unconditional
formalization of the classical Hurwitz theorem. -/
theorem zero_free_of_supplied_dichotomy (U : Set ℂ) (data : SuppliedZeroDichotomyData U)
    (z0 : ℂ) (hz0 : z0 ∈ U) (h_nontriv : data.flim z0 ≠ 0) :
    ∀ z ∈ U, data.flim z ≠ 0 := by
  cases supplied_zero_dichotomy U data with
  | inl h_ident_zero =>
    have : data.flim z0 = 0 := h_ident_zero z0 hz0
    exact False.elim (h_nontriv this)
  | inr h_zerofree =>
    exact h_zerofree

/-! ## 2. Open Unit Disk and Asano Colimit Readout -/

/-- The open unit disk domain 𝔻 = {z : ℂ | ‖z‖ < 1} -/
def openUnitDisk : Set ℂ := Metric.ball 0 1

/-- A normalized limit function with a supplied disk dichotomy.

No finite approximants, holomorphicity, or convergence theorem is stored here;
the resulting zero-free theorem is therefore only a conditional readout. -/
structure AsanoColimitDiskData where
  /-- Colimit limit partition function P_∞ -/
  P_inf : ℂ → ℂ
  /-- Normalization at origin P_∞(0) = 1 -/
  h_norm_origin : P_inf 0 = 1
  /-- Supplied zero/zero-free dichotomy on the disk. -/
  h_dichotomy : (∀ z ∈ openUnitDisk, P_inf z = 0) ∨ (∀ z ∈ openUnitDisk, P_inf z ≠ 0)

/-- 🏆 THEOREM 5: Asano Thermodynamic Colimit Zero-Free Theorem.
    The colimit partition function P_∞ has NO zeros in the open unit disk. -/
theorem asano_colimit_zerofree_in_unit_disk (data : AsanoColimitDiskData) :
    ∀ z ∈ openUnitDisk, data.P_inf z ≠ 0 := by
  have h0_in : (0 : ℂ) ∈ openUnitDisk := Metric.mem_ball_self (by norm_num)
  have h0_ne : data.P_inf 0 ≠ 0 := by
    rw [data.h_norm_origin]
    exact one_ne_zero
  have h_trans := zero_free_of_supplied_dichotomy openUnitDisk
    ⟨data.P_inf, data.h_dichotomy⟩
    0 h0_in h0_ne
  exact h_trans

/-! ## 3. Closedness of the Unit-Circle Locus -/

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

/-! ## 4. Möbius–Cayley Transform to the Imaginary Axis -/

/-- Standard Cayley / Möbius transform mapping the unit disk to the right half-plane. -/
def cayleyTransform (z : ℂ) : ℂ :=
  (1 - z) / (1 + z)

/-- 🏆 THEOREM 8: Cayley Map sends the Unit Circle to the Imaginary Axis.
    For z = e^{iθ} (‖z‖ = 1, z ≠ -1), Re(Cayley(z)) = 0.
    This is a boundary correspondence, not a Euclidean isometry or a zeta-zero theorem. -/
theorem cayley_unit_circle_maps_to_imaginary_axis (z : ℂ) (hz_circle : ‖z‖ = 1) (hz_ne : z ≠ -1) :
    (cayleyTransform z).re = 0 := by
  dsimp [cayleyTransform]
  have hden_complex : (1 + z : ℂ) ≠ 0 := by
    intro h
    apply hz_ne
    exact eq_neg_of_add_eq_zero_right h
  have hden : Complex.normSq (1 + z) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hden_complex)
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
      ((1 - z).re * (1 + z).re + (1 - z).im * (1 + z).im) / normSq (1 + z) := by
    field_simp [hden]
  rw [h_div, h_num, zero_div]

/-- 🏆 THEOREM 9: Master Hurwitz–Asano Colimit Synthesis Packet -/
theorem master_asano_colimit_readout
    (data : AsanoColimitDiskData)
    (z_seq : ℕ → ℂ) (z_star : ℂ)
    (h_on_circle : ∀ N, z_seq N ∈ unitCircle)
    (h_lim : Tendsto z_seq atTop (nhds z_star)) :
    (∀ z ∈ openUnitDisk, data.P_inf z ≠ 0) ∧
    (z_star ∈ unitCircle) :=
  ⟨asano_colimit_zerofree_in_unit_disk data,
   leeyang_zeros_limit_on_unit_circle z_seq z_star h_on_circle h_lim⟩

end InfoGeometry.Canonical.HurwitzAsano
