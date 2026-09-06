import Mathlib
import InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66

noncomputable section

namespace InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66

/-- Raw four-component TKK parameter action.  The middle operator is left
unrestricted here: injectivity of the decomposition is independent of the
metric-skewness condition later imposed on the zero-grade rotation sector. -/
def tkkParamAction
    (u : V10) (lambda : ℝ) (A : Module.End ℝ V10) (v : V10) (x : V12) : V12 :=
  pGen u x + dGen lambda x + rotGen A x + kGen v x

/-- The four graded TKK parameters are separated by the three canonical test
vectors `(1,0,0)`, `(0,0,1)`, and `(0,z,0)`.

This is the concrete injectivity core needed before restricting the middle
operator to the `(5,5)`-skew subspace. -/
theorem tkk_param_injective
    (u : V10) (lambda : ℝ) (A : Module.End ℝ V10) (v : V10)
    (h_zero : ∀ x : V12, tkkParamAction u lambda A v x = 0) :
    u = 0 ∧ lambda = 0 ∧ A = 0 ∧ v = 0 := by
  have h1 := h_zero ((1 : ℝ), ((0 : V10), (0 : ℝ)))
  simp [tkkParamAction, pGen, dGen, rotGen, kGen] at h1
  have hlambda : lambda = 0 := congrArg (fun p : V12 => p.1) h1
  have hv : v = 0 := congrArg (fun p : V12 => p.2.1) h1

  have h2 := h_zero ((0 : ℝ), ((0 : V10), (1 : ℝ)))
  simp [tkkParamAction, pGen, dGen, rotGen, kGen] at h2
  have hu : u = 0 := congrArg (fun p : V12 => p.2.1) h2

  have hA : A = 0 := by
    ext z
    have hz := h_zero ((0 : ℝ), (z, (0 : ℝ)))
    rw [hu, hlambda, hv] at hz
    simp [tkkParamAction, pGen, dGen, rotGen, kGen] at hz
    exact congrArg (fun p : V12 => p.2.1) hz

  exact ⟨hu, hlambda, hA, hv⟩

/-- A function-level parameterization of the 3-graded conformal generators.
The next owner can bundle this as a linear map into `Module.End ℝ V12` after
installing the four generator linearity lemmas. -/
def tkkParamFunction :
    V10 × ((ℝ × Module.End ℝ V10) × V10) → (V12 → V12) :=
  fun p => tkkParamAction p.1 p.2.1.1 p.2.1.2 p.2.2

/-- Injectivity of the raw parameterization follows immediately from the
three-test-vector theorem. -/
theorem tkkParamFunction_injective : Function.Injective tkkParamFunction := by
  intro p q hpq
  rcases p with ⟨u, ⟨⟨lambda, A⟩, v⟩⟩
  rcases q with ⟨u', ⟨⟨lambda', A'⟩, v'⟩⟩
  have hz : ∀ x : V12,
      tkkParamAction (u - u') (lambda - lambda') (A - A') (v - v') x = 0 := by
    intro x
    have h := congrFun hpq x
    simp [tkkParamFunction, tkkParamAction, pGen, dGen, rotGen, kGen,
      B10, zornPolar, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
      ZornVectorMatrix.conj, ZornVectorMatrix.sub, ZornVectorMatrix.add,
      ZornVectorMatrix.neg, ZornVectorMatrix.smul, ZornVec3.dot,
      Fin.sum_univ_three] at h ⊢
    module at h ⊢
    exact h
  rcases tkk_param_injective (u - u') (lambda - lambda') (A - A') (v - v') hz with
    ⟨hu, hlambda, hA, hv⟩
  apply Prod.ext
  · exact sub_eq_zero.mp hu
  · apply Prod.ext
    · apply Prod.ext
      · exact sub_eq_zero.mp hlambda
      · exact sub_eq_zero.mp hA
    · exact sub_eq_zero.mp hv

end InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66
