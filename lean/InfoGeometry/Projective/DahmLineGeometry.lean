/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.PluckerMatrixAction

/-!
# Corrected specializations of Dahm's line-coordinate formulas

The boost multiplier is `γ² * (1 - β²)`. The real coordinates in equation (8)
give a split polynomial. Two explicit volume-preserving shears demonstrate
that Klein invariance does not require commuting point or bivector operators.

This file states finite algebraic results, without a gauge-group or dynamical
interpretation. Source: J. Phys.: Conf. Ser. 2912 (2024), 012036, pp. 2–3.
-/

namespace InfoGeometry.Projective.DahmLineGeometry

open Matrix
open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Projective.PluckerMatrixAction

section ComplementaryColumns

variable {R : Type*} [CommRing R]

/-- A standard bivector coordinate, in the existing Plücker carrier. -/
def coordinateBasis (i : Fin 6) : Plucker6 R :=
  coordinates.symm (Pi.single i 1)

/-- Transforming a coordinate basis vector reads the corresponding minor column. -/
theorem coordinates_transform_basis (A : Matrix (Fin 4) (Fin 4) R) (j : Fin 6) :
    coordinates (transform A (coordinateBasis j)) = fun i => secondCompound A i j := by
  rw [coordinates_transform]
  simp only [coordinateBasis, Equiv.apply_symm_apply]
  exact Matrix.mulVec_single_one (secondCompound A) j

theorem complementary_pairing_01_23 (A : Matrix (Fin 4) (Fin 4) R) :
    Plucker6.polar (transform A (coordinateBasis 0))
      (transform A (coordinateBasis 5)) = A.det := by
  rw [polar_transform]
  simp [coordinateBasis, coordinates, Plucker6.polar, Plucker6.kleinQ, Plucker6.add]

/-- The middle pair uses `31`, so it is the negative of the `13` column. -/
theorem complementary_pairing_02_31 (A : Matrix (Fin 4) (Fin 4) R) :
    Plucker6.polar (transform A (coordinateBasis 1))
      (transform A (Plucker6.scale (-1) (coordinateBasis 4))) = A.det := by
  rw [polar_transform]
  simp [coordinateBasis, coordinates, Plucker6.polar, Plucker6.kleinQ,
    Plucker6.add, Plucker6.scale]

theorem complementary_pairing_03_12 (A : Matrix (Fin 4) (Fin 4) R) :
    Plucker6.polar (transform A (coordinateBasis 2))
      (transform A (coordinateBasis 3)) = A.det := by
  rw [polar_transform]
  simp [coordinateBasis, coordinates, Plucker6.polar, Plucker6.kleinQ, Plucker6.add]

/-- A six-dimensional matrix with unequal first and third complementary
column pairings cannot come from a single four-dimensional point matrix. -/
theorem not_secondCompound_of_complementary_pairings_ne
    (M : Matrix (Fin 6) (Fin 6) R)
    (h : Plucker6.polar (coordinates.symm (fun i => M i 0))
          (coordinates.symm (fun i => M i 5)) ≠
        Plucker6.polar (coordinates.symm (fun i => M i 2))
          (coordinates.symm (fun i => M i 3))) :
    ¬ ∃ A : Matrix (Fin 4) (Fin 4) R, secondCompound A = M := by
  rintro ⟨A, rfl⟩
  have hcol (j : Fin 6) :
      coordinates.symm (fun i => secondCompound A i j) =
        transform A (coordinateBasis j) := by
    apply coordinates.injective
    rw [Equiv.apply_symm_apply, coordinates_transform_basis]
  apply h
  rw [hcol, hcol, hcol, hcol,
    complementary_pairing_01_23, complementary_pairing_03_12]

end ComplementaryColumns

/-- The point-coordinate boost displayed in equation (1). Its normalization
is an explicit hypothesis of the invariance theorem. -/
def boost (γ β : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![γ, -(γ * β), 0, 0;
     -(γ * β), γ, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

theorem det_boost (γ β : ℝ) : (boost γ β).det = γ ^ 2 * (1 - β ^ 2) := by
  rw [Matrix.det_succ_row_zero]
  norm_num [boost, Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- The correct determinant multiplier before imposing the boost equation. -/
theorem kleinQ_boost (γ β : ℝ) (P : Plucker6 ℝ) :
    Plucker6.kleinQ (transform (boost γ β) P) =
      γ ^ 2 * (1 - β ^ 2) * Plucker6.kleinQ P := by
  rw [kleinQ_transform, det_boost]

theorem kleinQ_boost_of_normalized (γ β : ℝ)
    (h : γ ^ 2 * (1 - β ^ 2) = 1) (P : Plucker6 ℝ) :
    Plucker6.kleinQ (transform (boost γ β) P) = Plucker6.kleinQ P := by
  rw [kleinQ_boost, h, one_mul]

/-- At zero velocity the point transformation is the identity. -/
theorem boost_one_zero : boost 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [boost]

/-- The sign printed after equation (4) already fails at the identity boost. -/
theorem printed_boost_multiplier_ne_det_at_identity :
    (1 : ℝ) ^ 2 * ((0 : ℝ) ^ 2 - 1) ≠ (boost 1 0).det := by
  rw [det_boost]
  norm_num

/-- Equation (8) over the reals, respecting the orientation `p31 = -p13`.
It is a three-plus/three-minus polynomial, without changing the real form. -/
theorem real_klein_split_coordinates (P : Plucker6 ℝ) :
    4 * Plucker6.kleinQ P =
      (P.p01 + P.p23) ^ 2 - (P.p01 - P.p23) ^ 2 +
      (P.p02 - P.p13) ^ 2 - (P.p02 + P.p13) ^ 2 +
      (P.p03 + P.p12) ^ 2 - (P.p03 - P.p12) ^ 2 := by
  unfold Plucker6.kleinQ
  ring

/-- An elementary shear in the `01` plane. -/
def shear01 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- An elementary shear in the `12` plane. -/
def shear12 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     0, 1, 1, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

theorem det_shear01 : shear01.det = 1 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [shear01, Fin.sum_univ_succ, Matrix.det_fin_three]

theorem det_shear12 : shear12.det = 1 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [shear12, Fin.sum_univ_succ, Matrix.det_fin_three]

theorem shears_do_not_commute : shear01 * shear12 ≠ shear12 * shear01 := by
  intro h
  have h02 := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A 0 2) h
  norm_num [shear01, shear12, Matrix.mul_apply, Fin.sum_univ_succ] at h02

/-- The six-dimensional operator induced by the first point shear. -/
def exteriorShear01 : Matrix (Fin 6) (Fin 6) ℝ := secondCompound shear01

/-- The six-dimensional operator induced by the second point shear. -/
def exteriorShear12 : Matrix (Fin 6) (Fin 6) ℝ := secondCompound shear12

/-- The same failure of commutation is retained by the six-dimensional action. -/
theorem secondCompound_shears_do_not_commute :
    exteriorShear01 * exteriorShear12 ≠ exteriorShear12 * exteriorShear01 := by
  intro h
  have h25 := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) h
  norm_num [exteriorShear01, exteriorShear12, secondCompound, coordinatePair, shear01, shear12,
    Matrix.mul_apply, Fin.sum_univ_succ] at h25

theorem kleinQ_shear01 (P : Plucker6 ℝ) :
    Plucker6.kleinQ (transform shear01 P) = Plucker6.kleinQ P := by
  rw [kleinQ_transform, det_shear01, one_mul]

theorem kleinQ_shear12 (P : Plucker6 ℝ) :
    Plucker6.kleinQ (transform shear12 P) = Plucker6.kleinQ P := by
  rw [kleinQ_transform, det_shear12, one_mul]

/-- Noncommuting operators preserve the Klein form on every bivector.
The witnesses are the induced actions of the two explicit point shears. -/
theorem exists_noncommuting_klein_isometries :
    ∃ C D : Matrix (Fin 6) (Fin 6) ℝ, C * D ≠ D * C ∧
      ∀ P : Plucker6 ℝ,
        Plucker6.kleinQ (coordinates.symm (C *ᵥ coordinates P)) = Plucker6.kleinQ P ∧
        Plucker6.kleinQ (coordinates.symm (D *ᵥ coordinates P)) = Plucker6.kleinQ P := by
  refine ⟨secondCompound shear01, secondCompound shear12,
    secondCompound_shears_do_not_commute, ?_⟩
  intro P
  exact ⟨kleinQ_shear01 P, kleinQ_shear12 P⟩

/-- A witness outside the null cone, so covariance is not only `0 = 0`. -/
def twoPlaneSum : Plucker6 ℝ := ⟨1, 0, 0, 0, 0, 1⟩

theorem kleinQ_twoPlaneSum : Plucker6.kleinQ twoPlaneSum = 1 := by
  norm_num [Plucker6.kleinQ, twoPlaneSum]

theorem twoPlaneSum_not_wedge (u v : Vec4 ℝ) : Vec4.wedge u v ≠ twoPlaneSum := by
  intro h
  have hw := Vec4.wedge_isKlein u v
  change Plucker6.kleinQ (Vec4.wedge u v) = 0 at hw
  rw [h, kleinQ_twoPlaneSum] at hw
  norm_num at hw

end InfoGeometry.Projective.DahmLineGeometry
