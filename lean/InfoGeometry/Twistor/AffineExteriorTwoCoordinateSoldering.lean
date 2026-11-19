/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap
import InfoGeometry.Twistor.RealSupertwistorOperators

/-!
# Solder the affine-line coefficient carrier into two coordinates

This file defines the natural algebra map from the existing affine-line
polynomial/exterior carrier into the two-coordinate polynomial/exterior
carrier. It records generator behavior and proves compatibility with the
coefficient differential, matrix multiplication, and the resulting curvature.
Injectivity is a separate theorem and is not asserted here.
-/

noncomputable section

namespace InfoGeometry.Twistor.AffineExteriorTwoCoordinateSoldering

open scoped TensorProduct

abbrev C₁ := InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.AffineExteriorCoeff
abbrev C₂ := InfoGeometry.Twistor.RealSupertwistor.SuperWave (Fin 2) (Fin 2 → ℝ)

/-- Include the one-dimensional exterior generator as the first coordinate. -/
def coordinateLine : ℝ →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun r := Pi.single 0 r
  map_add' r s := by
    funext i
    fin_cases i <;> simp [Pi.single_apply]
  map_smul' c r := by
    funext i
    fin_cases i <;> simp [Pi.single_apply, smul_eq_mul]

/-- Send the affine polynomial variable to the first polynomial coordinate. -/
def polynomialCoordinate : Polynomial ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ :=
  Polynomial.aeval (MvPolynomial.X 0)

/-- Induced algebra map on exterior algebras. -/
def exteriorCoordinate : ExteriorAlgebra ℝ ℝ →ₐ[ℝ]
    ExteriorAlgebra ℝ (Fin 2 → ℝ) :=
  ExteriorAlgebra.map coordinateLine

/-- The affine-line coefficient algebra embeds by the chosen coordinate maps
into the two-coordinate polynomial/exterior coefficient algebra. -/
def affineToPlane : C₁ →ₐ[ℝ] C₂ :=
  Algebra.TensorProduct.map polynomialCoordinate exteriorCoordinate

/-- Project a two-coordinate vector to its first coordinate. -/
def coordinateProjection : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun v := v 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Retract the polynomial inclusion by evaluating the first coordinate at
the original polynomial variable and the unused coordinate at zero. -/
def polynomialProjection : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then Polynomial.X else 0)

/-- Retract the exterior-coordinate inclusion by projecting to the first
coordinate. -/
def exteriorProjection : ExteriorAlgebra ℝ (Fin 2 → ℝ) →ₐ[ℝ]
    ExteriorAlgebra ℝ ℝ := ExteriorAlgebra.map coordinateProjection

/-- The vector-space projection is a left inverse of the chosen coordinate
inclusion. -/
theorem coordinateProjection_coordinateLine :
    coordinateProjection.comp coordinateLine = LinearMap.id := by
  apply LinearMap.ext
  intro r
  rfl

/-- The exterior-algebra projection retracts the exterior inclusion. -/
theorem exteriorProjection_exteriorCoordinate :
    exteriorProjection.comp exteriorCoordinate =
      AlgHom.id ℝ (ExteriorAlgebra ℝ ℝ) := by
  rw [exteriorProjection, exteriorCoordinate,
    ExteriorAlgebra.map_comp_map coordinateLine coordinateProjection,
    coordinateProjection_coordinateLine, ExteriorAlgebra.map_id]

/-- The polynomial projection retracts the first-coordinate polynomial map. -/
theorem polynomialProjection_polynomialCoordinate (p : Polynomial ℝ) :
    polynomialProjection (polynomialCoordinate p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add polynomialCoordinate p q, map_add polynomialProjection,
        hp, hq]
  | monomial n a =>
      simp [polynomialProjection, polynomialCoordinate, Polynomial.aeval_monomial]
      rw [← Polynomial.C_mul_X_pow_eq_monomial]

/-- Algebraic retraction from the two-coordinate coefficient carrier to the
affine-line coefficient carrier. -/
def planeToAffine : C₂ →ₐ[ℝ] C₁ :=
  Algebra.TensorProduct.map polynomialProjection exteriorProjection

/-- The coefficient soldering map is a split injection: `planeToAffine` is an
explicit left inverse, so no coefficient information is lost. -/
theorem planeToAffine_affineToPlane :
    ∀ x : C₁, planeToAffine (affineToPlane x) = x := by
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p a =>
      simp only [planeToAffine, Algebra.TensorProduct.map_tmul,
        affineToPlane, Algebra.TensorProduct.map_tmul,
        polynomialProjection_polynomialCoordinate]
      have ha : exteriorProjection (exteriorCoordinate a) = a := by
        change (exteriorProjection.comp exteriorCoordinate) a = a
        rw [exteriorProjection_exteriorCoordinate]
        rfl
      rw [ha]

/-- The affine-line coefficient map therefore identifies its source with an
actual subalgebra of the two-coordinate carrier. -/
theorem affineToPlane_injective : Function.Injective affineToPlane := by
  intro x y h
  have h' := congrArg planeToAffine h
  rw [planeToAffine_affineToPlane x, planeToAffine_affineToPlane y] at h'
  exact h'

@[simp] theorem polynomialCoordinate_X :
    polynomialCoordinate Polynomial.X = MvPolynomial.X (0 : Fin 2) := by
  simp [polynomialCoordinate]

@[simp] theorem coordinateLine_one :
    coordinateLine (1 : ℝ) = Pi.single (0 : Fin 2) (1 : ℝ) := rfl

@[simp] theorem exteriorCoordinate_dX :
    exteriorCoordinate
      (InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineExteriorDX) =
      ExteriorAlgebra.ι ℝ (Pi.single (0 : Fin 2) (1 : ℝ)) := by
  simp [exteriorCoordinate,
    InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineExteriorDX]

@[simp] theorem affineToPlane_tmul (p : Polynomial ℝ)
    (a : ExteriorAlgebra ℝ ℝ) :
    affineToPlane (p ⊗ₜ[ℝ] a) = polynomialCoordinate p ⊗ₜ[ℝ] exteriorCoordinate a := by
  simp [affineToPlane]

@[simp] theorem affineToPlane_coordinate_polynomial :
    affineToPlane ((Polynomial.X : Polynomial ℝ) ⊗ₜ[ℝ]
        (1 : ExteriorAlgebra ℝ ℝ)) =
      (MvPolynomial.X (0 : Fin 2)) ⊗ₜ[ℝ]
        (1 : ExteriorAlgebra ℝ (Fin 2 → ℝ)) := by
  simp

@[simp] theorem affineToPlane_coordinate_one_form :
    affineToPlane ((1 : Polynomial ℝ) ⊗ₜ[ℝ]
        InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineExteriorDX) =
      (1 : MvPolynomial (Fin 2) ℝ) ⊗ₜ[ℝ]
        ExteriorAlgebra.ι ℝ (Pi.single (0 : Fin 2) (1 : ℝ)) := by
  simp

/-- The chosen polynomial inclusion intertwines the affine derivative with
the first coordinate partial derivative. -/
theorem polynomialCoordinate_derivative (p : Polynomial ℝ) :
    MvPolynomial.pderiv (0 : Fin 2) (polynomialCoordinate p) =
      polynomialCoordinate (Polynomial.derivative p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      rw [Polynomial.derivative_monomial]
      simp [polynomialCoordinate, Polynomial.aeval_monomial]
      rw [← mul_assoc]

/-- Differentiation in the unused second polynomial coordinate vanishes on
the image of the affine polynomial algebra. -/
theorem polynomialCoordinate_pderiv_one (p : Polynomial ℝ) :
    MvPolynomial.pderiv (1 : Fin 2) (polynomialCoordinate p) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      simp [polynomialCoordinate, Polynomial.aeval_monomial]

/-- The affine-line differential is carried to the two-coordinate
polynomial/exterior differential. This is the chain-map law on the complete
coefficient carrier, not only on its generators. -/
theorem affineToPlane_intertwines_differentials (x : C₁) :
    affineToPlane
        (InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineExteriorCoeffD x) =
      InfoGeometry.Twistor.RealSupertwistor.polynomialExteriorDifferential
        (Fin 2) (affineToPlane x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul p a =>
      rw [affineToPlane_tmul]
      simp only [InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineExteriorCoeffD,
        TensorProduct.map_tmul, Algebra.coe_lmul_eq_mul]
      rw [InfoGeometry.Twistor.RealSupertwistor.polynomialExteriorDifferential_tmul]
      simp only [Fin.sum_univ_two]
      rw [polynomialCoordinate_derivative, polynomialCoordinate_pderiv_one]
      simp [exteriorCoordinate,
        InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineExteriorDX,
        coordinateLine, map_mul]

/-- Entrywise lift of the coefficient soldering map to two-by-two matrices. -/
def affineMatrixToPlane
    (M : Matrix (Fin 2) (Fin 2) C₁) : Matrix (Fin 2) (Fin 2) C₂ :=
  fun i j => affineToPlane (M i j)

/-- Componentwise differential on matrices over the two-coordinate carrier. -/
def planeMatrixDifferential
    (M : Matrix (Fin 2) (Fin 2) C₂) : Matrix (Fin 2) (Fin 2) C₂ :=
  fun i j => InfoGeometry.Twistor.RealSupertwistor.polynomialExteriorDifferential
    (Fin 2) (M i j)

/-- The two-coordinate matrix differential is a genuine differential: its
square vanishes entrywise by the operator square-zero law. -/
theorem planeMatrixDifferential_sq_zero
    (M : Matrix (Fin 2) (Fin 2) C₂) :
    planeMatrixDifferential (planeMatrixDifferential M) = 0 := by
  ext i j
  change (InfoGeometry.Twistor.RealSupertwistor.polynomialExteriorDifferential
      (Fin 2) * InfoGeometry.Twistor.RealSupertwistor.polynomialExteriorDifferential
        (Fin 2)) (M i j) = 0
  rw [InfoGeometry.Twistor.RealSupertwistor.polynomialExteriorDifferential_fin2_sq_zero]
  rfl

/-- The entrywise lift preserves matrix addition. -/
theorem affineMatrixToPlane_add
    (M N : Matrix (Fin 2) (Fin 2) C₁) :
    affineMatrixToPlane (M + N) = affineMatrixToPlane M + affineMatrixToPlane N := by
  ext i j
  exact map_add affineToPlane (M i j) (N i j)

/-- The entrywise lift preserves matrix multiplication, including the finite
sum over the intermediate matrix index. -/
theorem affineMatrixToPlane_mul
    (M N : Matrix (Fin 2) (Fin 2) C₁) :
    affineMatrixToPlane (M * N) = affineMatrixToPlane M * affineMatrixToPlane N := by
  ext i j
  simp only [affineMatrixToPlane, Matrix.mul_apply, map_sum, map_mul]

/-- The matrix-level soldering map is injective because it is entrywise the
split-injective coefficient map. -/
theorem affineMatrixToPlane_injective :
    Function.Injective affineMatrixToPlane := by
  intro M N h
  ext i j
  exact affineToPlane_injective (congrFun (congrFun h i) j)

/-- The matrix lift is a chain map for the source and target componentwise
differentials. -/
theorem affineMatrixToPlane_intertwines_differentials
    (M : Matrix (Fin 2) (Fin 2) C₁) :
    affineMatrixToPlane
        (InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineExteriorMatrixD M) =
      planeMatrixDifferential (affineMatrixToPlane M) := by
  ext i j
  exact affineToPlane_intertwines_differentials (M i j)

/-- Curvature transport for arbitrary two-by-two matrix-valued coefficients:
the coefficient soldering map carries `dA + A * A` to the corresponding
two-coordinate expression. -/
theorem affineMatrixToPlane_curvature
    (A : Matrix (Fin 2) (Fin 2) C₁) :
    affineMatrixToPlane
        (InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineExteriorMatrixCurvature A) =
      planeMatrixDifferential (affineMatrixToPlane A) +
        affineMatrixToPlane A * affineMatrixToPlane A := by
  rw [InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineExteriorMatrixCurvature,
    affineMatrixToPlane_add, affineMatrixToPlane_intertwines_differentials,
    affineMatrixToPlane_mul]

/-- The soldered image of the existing affine-line one-form connection still
has zero curvature. Adding a second polynomial coordinate to the coefficient
carrier does not manufacture a second exterior direction: the source
connection has only `dx`, and its curvature remains zero after transport. -/
theorem soldered_affineLine_oneForm_curvature_vanishes
    (A : InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.MovingSheetMat) :
    planeMatrixDifferential
        (affineMatrixToPlane
          (InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineLineMatrixToExteriorCoeff
            (InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineOneForm A))) +
      affineMatrixToPlane
          (InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineLineMatrixToExteriorCoeff
            (InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineOneForm A)) *
      affineMatrixToPlane
          (InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineLineMatrixToExteriorCoeff
            (InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineOneForm A)) = 0 := by
  rw [← affineMatrixToPlane_curvature,
    ← InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineLineMatrixToExteriorCoeff_curvature,
    InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineLineConnection_one_form_curvature_vanishes]
  have hzero :
      InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineLineMatrixToExteriorCoeff
          InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affineLineFormZero = 0 := by
    ext i j
    exact InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.affinePairToExteriorCoeff_zero
  rw [hzero]
  ext i j
  exact map_zero affineToPlane

/-- The two coordinate one-forms, viewed in the actual polynomial/exterior
coefficient carrier. -/
def dx : C₂ := InfoGeometry.Twistor.RealSupertwistor.coordinateOneForm 0

def dy : C₂ := InfoGeometry.Twistor.RealSupertwistor.coordinateOneForm 1

/-- A matrix connection using both independent exterior directions. -/
def twoCoordinateConnection : Matrix (Fin 2) (Fin 2) C₂ :=
  ![![0, dx], ![dy, 0]]

/-- The connection has zero componentwise exterior derivative: its only
nonzero entries are constant coordinate one-forms. -/
theorem twoCoordinateConnection_differential_zero :
    planeMatrixDifferential twoCoordinateConnection = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeMatrixDifferential, twoCoordinateConnection, dx, dy,
      InfoGeometry.Twistor.RealSupertwistor.coordinateOneForm,
      InfoGeometry.Twistor.RealSupertwistor.polynomialExteriorDifferential_tmul]

/-- The curvature of the two-coordinate connection has the coordinate area
form in its `(0,0)` entry, hence is nonzero in the actual tensor carrier. -/
theorem twoCoordinateConnection_curvature_nonzero :
    planeMatrixDifferential twoCoordinateConnection +
      twoCoordinateConnection * twoCoordinateConnection ≠ 0 := by
  intro hzero
  have h00 := congrFun (congrFun hzero 0) 0
  rw [twoCoordinateConnection_differential_zero] at h00
  have hdxdy : dx * dy ≠ 0 := by
    simpa [dx, dy] using
      InfoGeometry.Twistor.RealSupertwistor.coordinateOneForm_mul_ne_zero
  apply hdxdy
  change (0 + twoCoordinateConnection * twoCoordinateConnection) 0 0 = 0 at h00
  simp only [Matrix.add_apply, Matrix.zero_apply, zero_add] at h00
  rw [Matrix.mul_apply, Fin.sum_univ_two] at h00
  simpa [twoCoordinateConnection, dx, dy] using h00

end InfoGeometry.Twistor.AffineExteriorTwoCoordinateSoldering

namespace InfoGeometry.Twistor.AffineExteriorTwoCoordinateSolderingWitnesses

open scoped TensorProduct

theorem affineExteriorCoeff_mat2_noncomm :
    ∃ A B : Matrix (Fin 2) (Fin 2)
      InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.AffineExteriorCoeff,
      A * B ≠ B * A := by
  let A : Matrix (Fin 2) (Fin 2)
      InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.AffineExteriorCoeff :=
    Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let B : Matrix (Fin 2) (Fin 2)
      InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.AffineExteriorCoeff :=
    Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0
  refine ⟨A, B, ?_⟩
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  have hAB : (A * B) 0 0 = 1 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (1 : Fin 2)]
    · simp [A, B]
    · intro k _ hk
      simp [A, hk]
    · intro h1
      exact (h1 (Finset.mem_univ _)).elim
  have hBA : (B * A) 0 0 = 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero (fun k _ => by simp [B])
  rw [hAB, hBA] at h00
  let aug :
      InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap.AffineExteriorCoeff →ₐ[ℝ] ℝ :=
    Algebra.TensorProduct.lift (Polynomial.aeval (0 : ℝ))
      (ExteriorAlgebra.lift ℝ ⟨0, fun _ => by simp⟩) (fun _ _ => mul_comm _ _)
  have haug := congrArg aug h00
  simp at haug

theorem superWave_mat2_noncomm :
    ∃ A B : Matrix (Fin 2) (Fin 2)
      (InfoGeometry.Twistor.RealSupertwistor.SuperWave (Fin 2) (Fin 2 → ℝ)),
      A * B ≠ B * A := by
  let A : Matrix (Fin 2) (Fin 2)
      (InfoGeometry.Twistor.RealSupertwistor.SuperWave (Fin 2) (Fin 2 → ℝ)) :=
    Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let B : Matrix (Fin 2) (Fin 2)
      (InfoGeometry.Twistor.RealSupertwistor.SuperWave (Fin 2) (Fin 2 → ℝ)) :=
    Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0
  refine ⟨A, B, ?_⟩
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  have hAB : (A * B) 0 0 = 1 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (1 : Fin 2)]
    · simp [A, B]
    · intro k _ hk
      simp [A, hk]
    · intro h1
      exact (h1 (Finset.mem_univ _)).elim
  have hBA : (B * A) 0 0 = 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero (fun k _ => by simp [B])
  rw [hAB, hBA] at h00
  let aug :
      (InfoGeometry.Twistor.RealSupertwistor.SuperWave (Fin 2) (Fin 2 → ℝ)) →ₐ[ℝ] ℝ :=
    Algebra.TensorProduct.lift (MvPolynomial.aeval (fun _ => (0 : ℝ)))
      (ExteriorAlgebra.lift ℝ ⟨0, fun _ => by simp⟩) (fun _ _ => mul_comm _ _)
  have haug := congrArg aug h00
  simp at haug

end InfoGeometry.Twistor.AffineExteriorTwoCoordinateSolderingWitnesses
