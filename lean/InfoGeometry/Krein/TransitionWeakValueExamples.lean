import InfoGeometry.Krein.TransitionWeakValue
import InfoGeometry.Canonical.WeakValuePoleBounds

/-!
# A normalized doubled-state curve with an unbounded weak readout

The two component states remain normalized, and the total doubled state is
Krein-null for every parameter, not just at the overlap zero. The overlap
crosses zero while the observable has a nonzero transition numerator.

This realizes a reconstruction pole in finite-dimensional state space. It is
not a Navier--Stokes trajectory, a proof of a spatial gradient singularity,
or an Andreev scattering theorem.
-/

noncomputable section
open scoped InnerProductSpace

namespace InfoGeometry.Krein.TransitionWeakValueExamples
open InfoGeometry.Krein.TransitionWeakValue

/-- Rational parametrization of the unit circle, first coordinate. -/
def circleX (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)

/-- Rational parametrization of the unit circle, second coordinate. -/
def circleY (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)

theorem circle_unit (t : ℝ) : circleX t ^ 2 + circleY t ^ 2 = 1 := by
  have h : (1 : ℝ) + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold circleX circleY
  field_simp [h] <;> ring

/-- The real two-dimensional owner carrier is used instead of a new matrix model. -/
def pre : DoubledSpace ℝ := to_doubled 1 0

def post (t : ℝ) : DoubledSpace ℝ := to_doubled (circleX t) (circleY t)

def state (t : ℝ) : DoubledSpace (DoubledSpace ℝ) := to_doubled pre (post t)

theorem pair_inner (a b c d : ℝ) :
    inner ℝ (to_doubled a b) (to_doubled c d) = a * c + b * d := by
  simp [to_doubled, WithLp.prod_inner_apply, mul_comm]

@[simp] theorem pre_inner : inner ℝ pre pre = 1 := by
  norm_num [pre, pair_inner]

theorem post_inner (t : ℝ) : inner ℝ (post t) (post t) = 1 := by
  rw [post, pair_inner]
  nlinarith [circle_unit t]

/-- Positive Hilbert normalization of the two components remains intact. -/
theorem component_norms (t : ℝ) : ‖pre‖ ^ 2 = 1 ∧ ‖post t‖ ^ 2 = 1 := by
  constructor
  · rw [← real_inner_self_eq_norm_sq]
    exact pre_inner
  · rw [← real_inner_self_eq_norm_sq]
    exact post_inner t

/-- The doubled state is null throughout the curve; nullity alone does not locate the pole. -/
theorem state_null (t : ℝ) :
    KreinSpace.kreinInner (state t) (state t) = 0 := by
  rw [state, krein_self_to_doubled, (component_norms t).1, (component_norms t).2]
  norm_num

theorem state_nonzero (t : ℝ) : state t ≠ 0 := by
  intro h
  have hpre : pre = 0 := by
    simpa [state] using congrArg WithLp.fst h
  have hnorm := (component_norms t).1
  rw [hpre] at hnorm
  norm_num at hnorm

@[simp] theorem state_overlap (t : ℝ) : overlap (state t) = circleX t := by
  change inner ℝ (post t) pre = circleX t
  simp [post, pre, pair_inner]

@[simp] theorem state_numerator (t : ℝ) :
    numerator (modular_j (E := ℝ)) (state t) = circleY t := by
  change inner ℝ (post t) (modular_j pre) = circleY t
  simp [post, pre, modular_j_to_doubled, pair_inner]

/-- The node has zero overlap and unit numerator, although the state is nonzero. -/
theorem node_data : overlap (state 0) = 0 ∧
    numerator (modular_j (E := ℝ)) (state 0) = 1 ∧ state 0 ≠ 0 := by
  refine ⟨?_, ?_, state_nonzero 0⟩ <;> norm_num [circleX, circleY]

theorem state_overlap_ne_zero {t : ℝ} (ht : t ≠ 0) : overlap (state t) ≠ 0 := by
  rw [state_overlap]
  unfold circleX
  exact div_ne_zero (mul_ne_zero (by norm_num) ht) (ne_of_gt (by positivity))

/-- Exact weak readout on the punctured parameter chart. -/
theorem state_readout (t : ℝ) (ht : t ≠ 0) :
    readout (modular_j (E := ℝ)) (state t) = (1 - t ^ 2) / (2 * t) := by
  rw [readout, state_numerator, state_overlap]
  have h : (1 : ℝ) + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold circleX circleY
  field_simp [ht, h] <;> ring

/-- Arbitrarily large readouts with both component norms fixed at one.
The statement is finite and quantitative; no continuum or PDE limit is assumed. -/
theorem arbitrarily_large_readout (R : ℝ) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ overlap (state t) ≠ 0 ∧
      R < readout (modular_j (E := ℝ)) (state t) := by
  let a : ℝ := 2 * (|R| + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : 1 ≤ a := by dsimp [a]; nlinarith [abs_nonneg R]
  have hinv : 1 / a ≤ 1 := (div_le_iff₀ ha).2 (by simpa using ha1)
  have ht : 0 < 1 / a := one_div_pos.mpr ha
  refine ⟨1 / a, ht, hinv, state_overlap_ne_zero (ne_of_gt ht), ?_⟩
  rw [state_readout (1 / a) (ne_of_gt ht)]
  have hformula : (1 - (1 / a) ^ 2) / (2 * (1 / a)) = (a - 1 / a) / 2 := by
    field_simp [ne_of_gt ha] <;> ring
  rw [hformula]
  dsimp [a] at hinv ⊢
  nlinarith [le_abs_self R]

/-- The same near-orthogonal states have the bounded identity readout. -/
theorem identity_readout (t : ℝ) (ht : t ≠ 0) :
    readout (ContinuousLinearMap.id ℝ (DoubledSpace ℝ)) (state t) = 1 :=
  readout_id _ (state_overlap_ne_zero ht)

end InfoGeometry.Krein.TransitionWeakValueExamples
