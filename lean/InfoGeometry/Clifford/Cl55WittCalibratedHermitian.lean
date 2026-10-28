/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl55WittCalibratedRepresentation
import InfoGeometry.Clifford.Cl55ChiralGrandCanonical
import InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Hermitian finite-stage seeds from the calibrated native CAR representation

The named creation and annihilation matrices are adjoints. Their occupation
operators, the raw native number image, and the chiral charge image are
therefore Hermitian. The existing coherent complexification preserves these
equalities and the tower indexing, supplying concrete Hermitian Hamiltonians
for finite-seed KMS consumers without imposing a star operation on `Cl55`.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55WittCalibratedHermitian

open scoped BigOperators
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl55WittCalibratedRepresentation
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.Cl55WittLieRouting
open InfoGeometry.Canonical.Cl55ChiralOccupationFiveGradeBridge
open InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge

theorem wittOccupation_isHermitian (i : Fin 5) :
    (creation i * annihilation i).IsHermitian := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, creation_transpose]
    using Matrix.isHermitian_mul_conjTranspose_self (creation i)

theorem wittDiagonalMixed_isHermitian (i : Fin 5) : (E i i).IsHermitian := by
  simpa [E] using (wittOccupation_isHermitian i).sub
    ((Matrix.isHermitian_one : (1 : MatStage 5).IsHermitian).smul
      (IsSelfAdjoint.all (1 / 2 : ℝ)))

theorem rawFockNumber_isHermitian : rawFockNumber.IsHermitian := by
  unfold rawFockNumber
  exact (isSelfAdjoint_sum Finset.univ
    (fun i _ => (wittOccupation_isHermitian i).isSelfAdjoint)).isHermitian

theorem cl55WittRepresentation_numberOperator55_isHermitian :
    (cl55WittRepresentation numberOperator55).IsHermitian := by
  rw [cl55WittRepresentation_numberOperator55_raw]
  exact rawFockNumber_isHermitian

@[simp] theorem cl55WittRepresentation_chiralCharge55 :
    cl55WittRepresentation chiralCharge55 = E 0 0 - E 1 1 := by
  simp [chiralCharge55, chiralPlusNumber55, chiralMinusNumber55]

theorem cl55WittRepresentation_chiralCharge55_isHermitian :
    (cl55WittRepresentation chiralCharge55).IsHermitian := by
  rw [cl55WittRepresentation_chiralCharge55]
  exact (wittDiagonalMixed_isHermitian 0).sub (wittDiagonalMixed_isHermitian 1)

/-- The same matrix representation in the coherent complex tower coordinates. -/
def cl55WittComplexRepresentation : Cl55 →ₐ[ℝ] CoherentComplexStage 5 :=
  (coherentComplexifyClStage 5).comp cl55WittRepresentation

@[simp] theorem cl55WittComplexRepresentation_apply (X : Cl55) :
    cl55WittComplexRepresentation X =
      coherentComplexifyClStage 5 (cl55WittRepresentation X) := rfl

theorem coherentComplexify_isHermitian {n : ℕ} {A : MatStage n}
    (hA : A.IsHermitian) : (coherentComplexifyClStage n A).IsHermitian := by
  change star (coherentComplexifyClStage n A) = coherentComplexifyClStage n A
  rw [← coherentComplexifyClStage_star, hA.star_eq]

@[simp] theorem cl55WittComplexRepresentation_creation55_star (i : Fin 5) :
    star (cl55WittComplexRepresentation (creation55 i)) =
      cl55WittComplexRepresentation (annihilation55 i) := by
  simp only [cl55WittComplexRepresentation_apply,
    cl55WittRepresentation_creation55, cl55WittRepresentation_annihilation55]
  rw [← coherentComplexifyClStage_star]
  simp only [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, creation_transpose]

theorem cl55WittComplexRepresentation_numberOperator55_isHermitian :
    (cl55WittComplexRepresentation numberOperator55).IsHermitian :=
  coherentComplexify_isHermitian cl55WittRepresentation_numberOperator55_isHermitian

theorem cl55WittComplexRepresentation_chiralCharge55_isHermitian :
    (cl55WittComplexRepresentation chiralCharge55).IsHermitian :=
  coherentComplexify_isHermitian cl55WittRepresentation_chiralCharge55_isHermitian

theorem cl55WittComplexRepresentation_numberMinusCharge_isHermitian (μ : ℝ) :
    (cl55WittComplexRepresentation (numberOperator55 - μ • chiralCharge55)).IsHermitian := by
  rw [map_sub, map_smul]
  exact cl55WittComplexRepresentation_numberOperator55_isHermitian.sub
    (cl55WittComplexRepresentation_chiralCharge55_isHermitian.smul (IsSelfAdjoint.all μ))

end InfoGeometry.Clifford.Cl55WittCalibratedHermitian
