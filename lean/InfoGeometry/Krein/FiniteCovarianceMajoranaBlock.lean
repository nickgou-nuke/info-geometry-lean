import Mathlib
import Mathlib.Tactic

/-!
# Finite covariance-to-Majorana block

For a scalar covariance `c` with `0 ≤ c ≤ 1`, this file records the finite
two-dimensional dilation pattern:

`c ↦ P c ↦ S c = 2 P c - 1`.

The construction is deliberately scalar and matrix-level.  It does not claim
an operator square-root theorem, an Araki--Wyss representation, or a general
von Neumann commutant result.
-/

open Matrix

namespace InfoGeometry.Krein.FiniteCovarianceMajoranaBlock

noncomputable def covarianceProjection (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c, Real.sqrt c * Real.sqrt (1 - c);
      Real.sqrt c * Real.sqrt (1 - c), 1 - c]

noncomputable def fundamentalSymmetry (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  2 • covarianceProjection c - 1

def complexAxis : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

private lemma sqrt_covariance_identities {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    Real.sqrt c * Real.sqrt c = c ∧
      Real.sqrt (1 - c) * Real.sqrt (1 - c) = 1 - c := by
  constructor
  · exact Real.mul_self_sqrt hc
  · exact Real.mul_self_sqrt (sub_nonneg.mpr hc1)

private lemma covariance_cross_square {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    (Real.sqrt c * Real.sqrt (1 - c)) *
        (Real.sqrt c * Real.sqrt (1 - c)) = c * (1 - c) := by
  calc
    (Real.sqrt c * Real.sqrt (1 - c)) *
        (Real.sqrt c * Real.sqrt (1 - c)) =
        (Real.sqrt c * Real.sqrt c) *
          (Real.sqrt (1 - c) * Real.sqrt (1 - c)) := by ring
    _ = c * (1 - c) := by
      rw [Real.mul_self_sqrt hc, Real.mul_self_sqrt (sub_nonneg.mpr hc1)]

theorem covarianceProjection_sq {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    covarianceProjection c * covarianceProjection c = covarianceProjection c := by
  have hs := sqrt_covariance_identities hc hc1
  have hcross := covariance_cross_square hc hc1
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [covarianceProjection, Matrix.mul_apply, Fin.sum_univ_succ, hs.1, hs.2,
      hcross]
    <;> ring

theorem covarianceProjection_self_adjoint {c : ℝ} :
    (covarianceProjection c).transpose = covarianceProjection c := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The finite covariance projection is positive semidefinite as a Gram matrix. -/
theorem covarianceProjection_posSemidef {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    Matrix.PosSemidef (covarianceProjection c) := by
  let v : Fin 2 → ℝ := fun i =>
    match i with
    | 0 => Real.sqrt c
    | 1 => Real.sqrt (1 - c)
  have hgram : covarianceProjection c = Matrix.gram ℝ v := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [covarianceProjection, v, Matrix.gram, hc, sub_nonneg.mpr hc1]
      <;> ring
  rw [hgram]
  exact Matrix.posSemidef_gram ℝ v

/-- The finite covariance projection has unit trace. -/
theorem covarianceProjection_trace {c : ℝ} :
    Matrix.trace (covarianceProjection c) = 1 := by
  simp [covarianceProjection, Matrix.trace_fin_two]

/-- The induced finite fundamental symmetry is trace-free. -/
theorem fundamentalSymmetry_trace {c : ℝ} :
    Matrix.trace (fundamentalSymmetry c) = 0 := by
  simp [fundamentalSymmetry, covarianceProjection, Matrix.trace_fin_two]
  ring

theorem fundamentalSymmetry_self_adjoint {c : ℝ} :
    (fundamentalSymmetry c).transpose = fundamentalSymmetry c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fundamentalSymmetry, covarianceProjection]

theorem fundamentalSymmetry_sq {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    fundamentalSymmetry c * fundamentalSymmetry c = 1 := by
  have hP := covarianceProjection_sq hc hc1
  simp only [fundamentalSymmetry]
  calc
    (2 • covarianceProjection c - 1) *
        (2 • covarianceProjection c - 1) =
        4 • (covarianceProjection c * covarianceProjection c) -
          4 • covarianceProjection c + 1 := by
      simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        one_mul, mul_one, smul_add, add_smul, smul_sub, sub_smul]
      noncomm_ring
    _ = 1 := by rw [hP]; module

theorem complexAxis_sq :
    complexAxis * complexAxis = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexAxis, Matrix.mul_apply, Fin.sum_univ_succ]

theorem complexAxis_anticommutes_fundamentalSymmetry
    {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    complexAxis * fundamentalSymmetry c =
      -(fundamentalSymmetry c * complexAxis) := by
  have hs := sqrt_covariance_identities hc hc1
  have hcross := covariance_cross_square hc hc1
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [complexAxis, fundamentalSymmetry, covarianceProjection,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two, hs.1, hs.2, hcross]
    <;> ring

theorem covarianceMajorana_split_quaternionic_relations
    {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    fundamentalSymmetry c * fundamentalSymmetry c = 1 ∧
      complexAxis * complexAxis = -(1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      complexAxis * fundamentalSymmetry c =
        -(fundamentalSymmetry c * complexAxis) :=
  ⟨fundamentalSymmetry_sq hc hc1,
   complexAxis_sq,
   complexAxis_anticommutes_fundamentalSymmetry hc hc1⟩

end InfoGeometry.Krein.FiniteCovarianceMajoranaBlock
