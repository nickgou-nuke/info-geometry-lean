import InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow
import InfoGeometry.Lie.SplitOctonionCircularNormCone
import InfoGeometry.Lie.SplitOctonionErlangenInvariant

/-!
# Hyperbolic Flow on the Canonical Split-Octonion Algebra

This file pulls back the `hyperbolicFlowCoordinate` onto the native `CanonicalZorn`
algebra using the circular Peirce basis equivalence. It then proves that this
active transformation preserves the full algebraic norm (the Zorn determinant),
and thus keeps the algebraic null-cone invariant.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularHyperbolicZornFlow

open InfoGeometry.Lie.SplitOctonionCircularHyperbolicFlow
open InfoGeometry.Lie.SplitOctonionCircularNormCone
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionCircularAxialGrading
open InfoGeometry.Algebra.Zorn.ZornMatrix
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionErlangenInvariant
open Finset

abbrev CZ := CanonicalZorn

/-- The exact quadratic form of the circular norm in coordinates. -/
def circularNormQuad (x : Fin 8 → ℝ) : ℝ :=
  x 0 * x 4 - ∑ i : Fin 3, x ⟨i.val + 1, by omega⟩ * x ⟨i.val + 5, by omega⟩

/-- The coordinate hyperbolic flow is an isometry of the circular quadratic form. -/
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

/-- The hyperbolic exponential flow on CanonicalZorn, pulled back from circular coordinates. -/
def hyperbolicFlowZorn (t : ℝ) : CanonicalZorn →ₗ[ℝ] CanonicalZorn :=
  circularPeirceBasis.equivFun.symm.toLinearMap.comp
    ((hyperbolicFlowCoordinate t).comp circularPeirceBasis.equivFun.toLinearMap)

theorem hyperbolicFlowZorn_apply (t : ℝ) (X : CanonicalZorn) :
    hyperbolicFlowZorn t X =
      circularPeirceBasis.equivFun.symm (hyperbolicFlowCoordinate t (circularPeirceBasis.equivFun X)) := rfl

@[simp] theorem hyperbolicFlowZorn_coordinate_apply (t : ℝ)
    (X : CanonicalZorn) (i : Fin 8) :
    circularPeirceBasis.equivFun (hyperbolicFlowZorn t X) i =
      Real.exp (t * axialWeight i) * circularPeirceBasis.equivFun X i := by
  rw [hyperbolicFlowZorn_apply, LinearEquiv.apply_symm_apply,
    hyperbolicFlowCoordinate_apply]

theorem hyperbolicFlowZorn_basis_action (t : ℝ) (i : Fin 8) :
    hyperbolicFlowZorn t (circularPeirceBasis i) =
      Real.exp (t * axialWeight i) • circularPeirceBasis i := by
  have hcoord : circularPeirceBasis.equivFun (circularPeirceBasis i) =
      (Pi.single i 1 : Fin 8 → ℝ) := by
    funext j
    by_cases h : i = j
    · subst j
      simpa [Pi.single_apply] using
        Module.Basis.equivFun_self circularPeirceBasis i i
    · have h' : j ≠ i := by
        intro hji
        exact h hji.symm
      simpa [Pi.single_apply, h, h'] using
        Module.Basis.equivFun_self circularPeirceBasis i j
  have hcoord_symm : circularPeirceBasis.equivFun.symm
      (Pi.single i 1 : Fin 8 → ℝ) = circularPeirceBasis i := by
    rw [← hcoord]
    exact circularPeirceBasis.equivFun.symm_apply_apply _
  rw [hyperbolicFlowZorn_apply, hcoord,
    hyperbolicFlowCoordinate_basis_action]
  rw [map_smul, hcoord_symm]

theorem hyperbolicFlowZorn_zero :
    hyperbolicFlowZorn 0 = LinearMap.id := by
  apply LinearMap.ext
  intro X
  rw [hyperbolicFlowZorn_apply, hyperbolicFlowCoordinate_zero]
  simp only [LinearMap.id_apply]
  exact circularPeirceBasis.equivFun.symm_apply_apply X

theorem hyperbolicFlowZorn_add (s t : ℝ) :
    hyperbolicFlowZorn (s + t) =
      (hyperbolicFlowZorn s).comp (hyperbolicFlowZorn t) := by
  apply LinearMap.ext
  intro X
  apply circularPeirceBasis.equivFun.injective
  simp only [hyperbolicFlowZorn_apply, LinearMap.comp_apply,
    LinearEquiv.apply_symm_apply]
  rw [hyperbolicFlowCoordinate_add]
  rfl

theorem hyperbolicFlowZorn_neg (t : ℝ) :
    (hyperbolicFlowZorn (-t)).comp (hyperbolicFlowZorn t) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  apply circularPeirceBasis.equivFun.injective
  simp only [hyperbolicFlowZorn_apply, LinearMap.comp_apply,
    LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  exact LinearMap.congr_fun (hyperbolicFlowCoordinate_neg t)
    (circularPeirceBasis.equivFun X)

noncomputable def hyperbolicFlowZornEquiv (t : ℝ) :
    CanonicalZorn ≃ₗ[ℝ] CanonicalZorn where
  toFun := hyperbolicFlowZorn t
  invFun := hyperbolicFlowZorn (-t)
  left_inv := by
    intro X
    exact LinearMap.congr_fun (hyperbolicFlowZorn_neg t) X
  right_inv := by
    intro X
    simpa only [neg_neg] using
      LinearMap.congr_fun (hyperbolicFlowZorn_neg (-t)) X
  map_add' := (hyperbolicFlowZorn t).map_add
  map_smul' := (hyperbolicFlowZorn t).map_smul

@[simp] theorem hyperbolicFlowZornEquiv_apply (t : ℝ) (X : CanonicalZorn) :
    hyperbolicFlowZornEquiv t X = hyperbolicFlowZorn t X := rfl

theorem hyperbolicFlowZornEquiv_symm (t : ℝ) :
    (hyperbolicFlowZornEquiv t).symm = hyperbolicFlowZornEquiv (-t) := by
  apply LinearEquiv.ext
  intro X
  rfl

theorem hyperbolicFlowZornEquiv_zero_apply (X : CanonicalZorn) :
    hyperbolicFlowZornEquiv 0 X = X := by
  change hyperbolicFlowZorn 0 X = X
  exact LinearMap.congr_fun hyperbolicFlowZorn_zero X

theorem hyperbolicFlowZornEquiv_add_apply (s t : ℝ) (X : CanonicalZorn) :
    hyperbolicFlowZornEquiv (s + t) X =
      hyperbolicFlowZornEquiv s (hyperbolicFlowZornEquiv t X) := by
  change hyperbolicFlowZorn (s + t) X =
    hyperbolicFlowZorn s (hyperbolicFlowZorn t X)
  rw [hyperbolicFlowZorn_add]
  rfl

theorem hyperbolicFlowZornEquiv_neg_apply (t : ℝ) (X : CanonicalZorn) :
    hyperbolicFlowZornEquiv (-t) (hyperbolicFlowZornEquiv t X) = X := by
  change hyperbolicFlowZorn (-t) (hyperbolicFlowZorn t X) = X
  exact LinearMap.congr_fun (hyperbolicFlowZorn_neg t) X

/-- The hyperbolic flow on CanonicalZorn preserves the zero-norm cone (and the full algebraic norm). -/
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

noncomputable def hyperbolicFlowZornQuadraticIsometry (t : ℝ) :
    canonicalDetQuadratic.IsometryEquiv canonicalDetQuadratic :=
  { hyperbolicFlowZornEquiv t with
    map_app' := fun X => by
      simpa [canonicalDetQuadratic] using hyperbolicFlowZorn_preserves_norm t X }

@[simp] theorem hyperbolicFlowZornQuadraticIsometry_apply
    (t : ℝ) (X : CanonicalZorn) :
    hyperbolicFlowZornQuadraticIsometry t X = hyperbolicFlowZorn t X := rfl

@[simp] theorem hyperbolicFlowZornQuadraticIsometry_preserves_form
    (t : ℝ) (X : CanonicalZorn) :
    canonicalDetQuadratic (hyperbolicFlowZornQuadraticIsometry t X) =
      canonicalDetQuadratic X := by
  exact QuadraticMap.IsometryEquiv.map_app
    (hyperbolicFlowZornQuadraticIsometry t) X

/-! The hyperbolic flow preserves the native split-octonion null cone. -/
theorem hyperbolicFlowZorn_mem_nullCone_iff (t : ℝ) (X : CanonicalZorn) :
    detZ (hyperbolicFlowZorn t X) = 0 ↔ detZ X = 0 := by
  rw [hyperbolicFlowZorn_preserves_norm]

end InfoGeometry.Lie.SplitOctonionCircularHyperbolicZornFlow
