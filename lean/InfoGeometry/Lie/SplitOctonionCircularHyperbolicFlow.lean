import InfoGeometry.Lie.SplitOctonionCircularAxialGrading
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Hyperbolic flow in circular coordinates

The normalized axial grading has weights `0,+1,+1,+1,0,-1,-1,-1`.
This owner defines the corresponding diagonal flow on the coordinate module.
It uses the ordinary associative endomorphism algebra of the coordinate
module; no reassociation of split-octonion products is involved.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow

open InfoGeometry.Lie.SplitOctonionCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

abbrev Coord := InfoGeometry.Algebra.FiniteSpin.Vec8R

def hyperbolicScale (t : ℝ) (i : Fin 8) : ℝ :=
  Real.exp (t * axialWeight i)

/-- The Witt quadratic polynomial in the ordered circular coordinates
`(u₊,σ₊¹,σ₊²,σ₊³,u₋,σ₋¹,σ₋²,σ₋³)`. -/
def circularWittNorm (x : Coord) : ℝ :=
  x 0 * x 4 - (x 1 * x 5 + x 2 * x 6 + x 3 * x 7)

noncomputable def hyperbolicFlowCoordinate (t : ℝ) : Coord →ₗ[ℝ] Coord where
  toFun x i := hyperbolicScale t i * x i
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply]
    change hyperbolicScale t i * (c * x i) =
      c * (hyperbolicScale t i * x i)
    ring

@[simp] theorem hyperbolicFlowCoordinate_apply (t : ℝ) (x : Coord) (i : Fin 8) :
    hyperbolicFlowCoordinate t x i =
      Real.exp (t * axialWeight i) * x i := rfl

theorem hyperbolicFlowCoordinate_zero :
    hyperbolicFlowCoordinate 0 = LinearMap.id := by
  ext x i
  simp [hyperbolicFlowCoordinate, hyperbolicScale]

theorem hyperbolicFlowCoordinate_add (s t : ℝ) :
    hyperbolicFlowCoordinate (s + t) =
      (hyperbolicFlowCoordinate s).comp (hyperbolicFlowCoordinate t) := by
  ext x i
  simp only [hyperbolicFlowCoordinate_apply, LinearMap.comp_apply]
  rw [add_mul, Real.exp_add]
  ring

theorem hyperbolicFlowCoordinate_neg (t : ℝ) :
    (hyperbolicFlowCoordinate (-t)).comp (hyperbolicFlowCoordinate t) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [hyperbolicFlowCoordinate_apply, LinearMap.comp_apply]
  rw [LinearMap.id_apply]
  rw [show -t * axialWeight i = -(t * axialWeight i) by ring]
  rw [← mul_assoc, ← Real.exp_add]
  simp

noncomputable def hyperbolicFlowCoordinateEquiv (t : ℝ) : Coord ≃ₗ[ℝ] Coord where
  toFun := hyperbolicFlowCoordinate t
  invFun := hyperbolicFlowCoordinate (-t)
  left_inv := by
    intro x
    exact LinearMap.congr_fun (hyperbolicFlowCoordinate_neg t) x
  right_inv := by
    intro x
    simpa only [neg_neg, LinearMap.id_apply] using
      LinearMap.congr_fun (hyperbolicFlowCoordinate_neg (-t)) x
  map_add' := (hyperbolicFlowCoordinate t).map_add
  map_smul' := (hyperbolicFlowCoordinate t).map_smul

@[simp] theorem hyperbolicFlowCoordinateEquiv_apply (t : ℝ) (x : Coord) :
    hyperbolicFlowCoordinateEquiv t x = hyperbolicFlowCoordinate t x := rfl

theorem hyperbolicFlowCoordinateEquiv_symm (t : ℝ) :
    (hyperbolicFlowCoordinateEquiv t).symm =
      hyperbolicFlowCoordinateEquiv (-t) := by
  apply LinearEquiv.ext
  intro x
  rfl

theorem hyperbolicFlowCoordinate_weight_action (t : ℝ) (x : Coord) (i : Fin 8) :
    hyperbolicFlowCoordinate t x i =
      Real.exp (t * axialWeight i) * x i := rfl

theorem hyperbolicFlowCoordinate_basis_action (t : ℝ) (i : Fin 8) :
    hyperbolicFlowCoordinate t (Pi.single i 1 : Coord) =
      Real.exp (t * axialWeight i) • (Pi.single i 1 : Coord) := by
  ext j
  by_cases h : i = j
  · subst j
    simp [hyperbolicFlowCoordinate, hyperbolicScale, Pi.smul_apply,
      smul_eq_mul]
  · simp [hyperbolicFlowCoordinate, hyperbolicScale, Pi.smul_apply,
      smul_eq_mul, h]

theorem hyperbolicFlowCoordinate_preserves_circularWittNorm
    (t : ℝ) (x : Coord) :
    circularWittNorm (hyperbolicFlowCoordinate t x) = circularWittNorm x := by
  simp only [circularWittNorm, hyperbolicFlowCoordinate_apply]
  have h₀ : Real.exp (t * axialWeight (0 : Fin 8)) = 1 := by
    simp [axialWeight]
  have h₄ : Real.exp (t * axialWeight (4 : Fin 8)) = 1 := by
    simp [axialWeight]
  have h₁ : Real.exp (t * axialWeight (1 : Fin 8)) = Real.exp t := by
    simp [axialWeight]
  have h₂ : Real.exp (t * axialWeight (2 : Fin 8)) = Real.exp t := by
    simp [axialWeight]
  have h₃ : Real.exp (t * axialWeight (3 : Fin 8)) = Real.exp t := by
    simp [axialWeight]
  have h₅ : Real.exp (t * axialWeight (5 : Fin 8)) = Real.exp (-t) := by
    simp [axialWeight]
  have h₆ : Real.exp (t * axialWeight (6 : Fin 8)) = Real.exp (-t) := by
    simp [axialWeight]
  have h₇ : Real.exp (t * axialWeight (7 : Fin 8)) = Real.exp (-t) := by
    simp [axialWeight]
  rw [h₀, h₄, h₁, h₂, h₃, h₅, h₆, h₇]
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]

theorem hyperbolicFlowCoordinate_commutes_grading (t : ℝ) :
    (hyperbolicFlowCoordinate t).comp circularAxialGrading =
      circularAxialGrading.comp (hyperbolicFlowCoordinate t) := by
  apply LinearMap.ext
  intro x
  funext i
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  have h₁ := circularAxialGrading_coordinate
    ((circularPeirceBasis.equivFun).symm x) i
  have h₂ := circularAxialGrading_coordinate
    ((circularPeirceBasis.equivFun).symm (hyperbolicFlowCoordinate t x)) i
  simp only [LinearEquiv.apply_symm_apply] at h₁ h₂
  rw [hyperbolicFlowCoordinate_apply, h₁, h₂]
  rw [hyperbolicFlowCoordinate_apply]
  ring

end InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow
