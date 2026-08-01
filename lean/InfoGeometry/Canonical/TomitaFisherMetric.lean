import Mathlib.Tactic
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Canonical.TomitaBregmanDuality
import InfoGeometry.Canonical.ModularSL2R

/-!
# InfoGeometry.Canonical.TomitaFisherMetric

Finite Fisher-metric lane from the Tomita-Bregman seed on `M₂(ℝ)`.

We use the scalar potential `ψ(x)=exp x`, whose Hessian is `exp x`,
evaluated at the two diagonal channels `x=-1` and `x=1`.
This yields an explicit diagonal Fisher matrix, plus:
* nonnegative quadratic form,
* nilpotent-boundary trace orthogonality.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.TomitaFisherMetric

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.ModularSL2R

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev V2R := Matrix (Fin 2) (Fin 1) ℝ

/-- Channel Hessian values for `ψ(x)=exp x` at `x=-1,1`. -/
noncomputable def fisher11 : ℝ := Real.exp (-1)
noncomputable def fisher22 : ℝ := Real.exp 1

/-- Explicit diagonal Fisher metric on the two-channel finite seed. -/
noncomputable def fisherMetric : M2R :=
  !![fisher11, 0;
     0,        fisher22]

/-- Quadratic Fisher form on column vectors in `ℝ²`. -/
noncomputable def fisherQuad (v : V2R) : ℝ :=
  fisher11 * (v 0 0) ^ 2 + fisher22 * (v 1 0) ^ 2

/-- Concrete Hessian diagonal evaluation. -/
theorem fisherMetric_eval :
    fisherMetric = !![Real.exp (-1), 0; 0, Real.exp 1] := by
  unfold fisherMetric fisher11 fisher22
  rfl

/-- The Fisher quadratic form is nonnegative. -/
theorem fisherQuad_nonneg (v : V2R) :
    0 ≤ fisherQuad v := by
  unfold fisherQuad fisher11 fisher22
  have h0 : 0 ≤ Real.exp (-1) * (v 0 0) ^ 2 := by
    nlinarith [Real.exp_pos (-1), sq_nonneg (v 0 0)]
  have h1 : 0 ≤ Real.exp 1 * (v 1 0) ^ 2 := by
    nlinarith [Real.exp_pos 1, sq_nonneg (v 1 0)]
  nlinarith

/-- Fisher metric remains orthogonal to the nilpotent boundary under `traceForm`. -/
theorem trace_fisherMetric_boundary :
    traceForm fisherMetric N = 0 := by
  rw [fisherMetric_eval]
  unfold traceForm tr
  norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- If one coordinate is nonzero, the Fisher quadratic form is strictly positive. -/
theorem fisherQuad_pos_of_coord_ne_zero (v : V2R)
    (h : v 0 0 ≠ 0 ∨ v 1 0 ≠ 0) :
    0 < fisherQuad v := by
  unfold fisherQuad fisher11 fisher22
  rcases h with h0 | h1
  · have hs0 : 0 < (v 0 0) ^ 2 := by
      nlinarith [sq_pos_of_ne_zero h0]
    have hterm0 : 0 < Real.exp (-1) * (v 0 0) ^ 2 := by
      nlinarith [Real.exp_pos (-1), hs0]
    have hterm1 : 0 ≤ Real.exp 1 * (v 1 0) ^ 2 := by
      nlinarith [Real.exp_pos 1, sq_nonneg (v 1 0)]
    nlinarith
  · have hs1 : 0 < (v 1 0) ^ 2 := by
      nlinarith [sq_pos_of_ne_zero h1]
    have hterm0 : 0 ≤ Real.exp (-1) * (v 0 0) ^ 2 := by
      nlinarith [Real.exp_pos (-1), sq_nonneg (v 0 0)]
    have hterm1 : 0 < Real.exp 1 * (v 1 0) ^ 2 := by
      nlinarith [Real.exp_pos 1, hs1]
    nlinarith

/-- Characterization of zero Fisher energy in the finite two-channel seed. -/
theorem fisherQuad_eq_zero_iff (v : V2R) :
    fisherQuad v = 0 ↔ v 0 0 = 0 ∧ v 1 0 = 0 := by
  constructor
  · intro hq
    by_contra hne
    have hpos : 0 < fisherQuad v := by
      apply fisherQuad_pos_of_coord_ne_zero
      exact not_and_or.mp hne
    linarith
  · rintro ⟨h0, h1⟩
    unfold fisherQuad
    simp [h0, h1]

/-- Coercive lower bound against the Euclidean square norm in two channels. -/
theorem fisherQuad_lower_bound (v : V2R) :
    Real.exp (-1) * ((v 0 0) ^ 2 + (v 1 0) ^ 2) ≤ fisherQuad v := by
  unfold fisherQuad fisher11 fisher22
  have h0 : 0 ≤ (v 1 0) ^ 2 := sq_nonneg (v 1 0)
  have hmono : Real.exp (-1) ≤ Real.exp 1 := by
    exact Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 1)
  have hterm :
      Real.exp (-1) * (v 1 0) ^ 2 ≤ Real.exp 1 * (v 1 0) ^ 2 := by
    nlinarith
  nlinarith

/-- Matching upper bound against Euclidean square norm in two channels. -/
theorem fisherQuad_upper_bound (v : V2R) :
    fisherQuad v ≤ Real.exp 1 * ((v 0 0) ^ 2 + (v 1 0) ^ 2) := by
  unfold fisherQuad fisher11 fisher22
  have h0 : 0 ≤ (v 0 0) ^ 2 := sq_nonneg (v 0 0)
  have hmono : Real.exp (-1) ≤ Real.exp 1 := by
    exact Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 1)
  have hterm :
      Real.exp (-1) * (v 0 0) ^ 2 ≤ Real.exp 1 * (v 0 0) ^ 2 := by
    nlinarith
  nlinarith

/-- Two-sided Euclidean comparison for the Fisher quadratic form. -/
theorem fisherQuad_norm_equiv (v : V2R) :
    Real.exp (-1) * ((v 0 0) ^ 2 + (v 1 0) ^ 2) ≤ fisherQuad v ∧
    fisherQuad v ≤ Real.exp 1 * ((v 0 0) ^ 2 + (v 1 0) ^ 2) := by
  refine ⟨?_, ?_⟩
  · exact fisherQuad_lower_bound v
  · exact fisherQuad_upper_bound v

/-- Vanishing of Fisher energy is equivalent to vanishing Euclidean square norm. -/
theorem fisherQuad_eq_zero_iff_euclidean_sq_zero (v : V2R) :
    fisherQuad v = 0 ↔ (v 0 0) ^ 2 + (v 1 0) ^ 2 = 0 := by
  constructor
  · intro hq
    rcases (fisherQuad_eq_zero_iff v).mp hq with ⟨h0, h1⟩
    simp [h0, h1]
  · intro hsq
    have hsum_nonneg : 0 ≤ (v 0 0) ^ 2 + (v 1 0) ^ 2 := by
      nlinarith [sq_nonneg (v 0 0), sq_nonneg (v 1 0)]
    have hsum_eq : (v 0 0) ^ 2 + (v 1 0) ^ 2 = 0 := le_antisymm (by simpa [hsq] using hsum_nonneg) (by simpa [hsq])
    have h0sq : (v 0 0) ^ 2 = 0 := by nlinarith [sq_nonneg (v 0 0), sq_nonneg (v 1 0), hsum_eq]
    have h1sq : (v 1 0) ^ 2 = 0 := by nlinarith [sq_nonneg (v 0 0), sq_nonneg (v 1 0), hsum_eq]
    have h0 : v 0 0 = 0 := pow_eq_zero h0sq
    have h1 : v 1 0 = 0 := pow_eq_zero h1sq
    exact (fisherQuad_eq_zero_iff v).2 ⟨h0, h1⟩

end InfoGeometry.Canonical.TomitaFisherMetric
