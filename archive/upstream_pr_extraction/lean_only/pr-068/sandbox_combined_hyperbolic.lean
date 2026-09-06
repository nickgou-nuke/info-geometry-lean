import InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow
import InfoGeometry.Lie.SplitOctonionCircularNormCone

open InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow
open InfoGeometry.Lie.SplitOctonionCircularNormCone
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionCircularAxialGrading
open InfoGeometry.Algebra.Zorn.ZornMatrix
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open Finset

noncomputable section

def circularNormQuad (x : Fin 8 → ℝ) : ℝ :=
  x 0 * x 4 - ∑ i : Fin 3, x ⟨i.val + 1, by omega⟩ * x ⟨i.val + 5, by omega⟩

theorem circularNormQuad_hyperbolicFlow (t : ℝ) (x : Fin 8 → ℝ) :
    circularNormQuad (hyperbolicFlowCoordinate t x) = circularNormQuad x := by
  dsimp [circularNormQuad, hyperbolicFlowCoordinate, hyperbolicScale]
  have hw0 : axialWeight 0 = 0 := rfl
  have hw4 : axialWeight 4 = 0 := rfl
  rw [hw0, hw4]
  simp only [mul_zero, Real.exp_zero, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hw1 : axialWeight ⟨i.val + 1, by omega⟩ = 1 := by
    fin_cases i <;> rfl
  have hw5 : axialWeight ⟨i.val + 5, by omega⟩ = -1 := by
    fin_cases i <;> rfl
  rw [hw1, hw5]
  change (Real.exp (t * 1) * _) * (Real.exp (t * -1) * _) = _
  rw [mul_one, show t * -1 = -t by ring]
  calc
    (Real.exp t * x ⟨i.val + 1, _⟩) * (Real.exp (-t) * x ⟨i.val + 5, _⟩)
      = (Real.exp t * Real.exp (-t)) * (x ⟨i.val + 1, _⟩ * x ⟨i.val + 5, _⟩) := by ring
    _ = Real.exp (t + -t) * (x ⟨i.val + 1, _⟩ * x ⟨i.val + 5, _⟩) := by
      rw [← Real.exp_add]
    _ = Real.exp 0 * (x ⟨i.val + 1, _⟩ * x ⟨i.val + 5, _⟩) := by
      rw [add_neg_cancel]
    _ = x ⟨i.val + 1, _⟩ * x ⟨i.val + 5, _⟩ := by
      rw [Real.exp_zero, one_mul]

abbrev CZ := CanonicalZorn

/-- The hyperbolic exponential flow on CanonicalZorn, pulled back from circular coordinates. -/
def hyperbolicFlowZorn (t : ℝ) : CanonicalZorn →ₗ[ℝ] CanonicalZorn :=
  circularPeirceBasis.equivFun.symm.toLinearMap.comp
    ((hyperbolicFlowCoordinate t).comp circularPeirceBasis.equivFun.toLinearMap)

theorem hyperbolicFlowZorn_apply (t : ℝ) (X : CanonicalZorn) :
    hyperbolicFlowZorn t X =
      circularPeirceBasis.equivFun.symm (hyperbolicFlowCoordinate t (circularPeirceBasis.equivFun X)) := rfl

/-- The hyperbolic flow on CanonicalZorn preserves the zero-norm cone (and the full norm). -/
theorem hyperbolicFlowZorn_preserves_norm (t : ℝ) (X : CanonicalZorn) :
    detZ (hyperbolicFlowZorn t X) = detZ X := by
  have h1 (Y : CanonicalZorn) : detZ Y = circularNormQuad (circularPeirceBasis.equivFun Y) := by
    rw [circularNorm_eq Y, circularPeirceBasis_coordinate_eq_equivFun Y]
    rfl
  rw [h1, h1]
  have h2 : circularPeirceBasis.equivFun (hyperbolicFlowZorn t X) =
      hyperbolicFlowCoordinate t (circularPeirceBasis.equivFun X) := by
    rw [hyperbolicFlowZorn_apply]
    rw [LinearEquiv.apply_symm_apply]
  rw [h2]
  exact circularNormQuad_hyperbolicFlow t (circularPeirceBasis.equivFun X)
