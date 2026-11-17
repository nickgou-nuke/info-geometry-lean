/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.RealSpacetimeSpinor
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The sixteen ordered blades of the real spacetime algebra

These are products of the existing native generators, in the order
`1, γ₀, γ₁, γ₂, γ₃, γ₀₁, γ₀₂, γ₀₃, γ₁₂, γ₁₃, γ₂₃,
γ₀₁₂, γ₀₁₃, γ₀₂₃, γ₁₂₃, γ₀₁₂₃`.

The quaternion representation supplies a computed dual table for the positive
timelike reversion pairing. The resulting dual linear maps prove independence;
the existing dimension theorem then gives a basis of the whole native algebra.
The normalized real quaternion trace is exactly its scalar coordinate.
-/

noncomputable section

namespace InfoGeometry.Clifford.RealSpacetimeBlades

open HestenesCl14
open RealSpacetimeQuaternion RealSpacetimeSpinor
open scoped Matrix

/-- The native ordered Clifford products, including all grades zero through four. -/
def blade : Fin 16 → Cl14
  | 0 => 1
  | 1 => gamma 0
  | 2 => gamma 1
  | 3 => gamma 2
  | 4 => gamma 3
  | 5 => gamma 0 * gamma 1
  | 6 => gamma 0 * gamma 2
  | 7 => gamma 0 * gamma 3
  | 8 => gamma 1 * gamma 2
  | 9 => gamma 1 * gamma 3
  | 10 => gamma 2 * gamma 3
  | 11 => gamma 0 * gamma 1 * gamma 2
  | 12 => gamma 0 * gamma 1 * gamma 3
  | 13 => gamma 0 * gamma 2 * gamma 3
  | 14 => gamma 1 * gamma 2 * gamma 3
  | 15 => gamma 0 * gamma 1 * gamma 2 * gamma 3

/-- Explicit images used only to compute the sixteen native products. -/
def bladeMatrix : Fin 16 → QuaternionMatrix
  | 0 => 1
  | 1 => timeMatrix
  | 2 => !![0, quaternionI; quaternionI, 0]
  | 3 => !![0, quaternionJ; quaternionJ, 0]
  | 4 => !![0, quaternionK; quaternionK, 0]
  | 5 => !![0, quaternionI; -quaternionI, 0]
  | 6 => !![0, quaternionJ; -quaternionJ, 0]
  | 7 => !![0, quaternionK; -quaternionK, 0]
  | 8 => !![quaternionK, 0; 0, quaternionK]
  | 9 => !![-quaternionJ, 0; 0, -quaternionJ]
  | 10 => !![quaternionI, 0; 0, quaternionI]
  | 11 => !![quaternionK, 0; 0, -quaternionK]
  | 12 => !![-quaternionJ, 0; 0, quaternionJ]
  | 13 => !![quaternionI, 0; 0, -quaternionI]
  | 14 => !![0, -1; -1, 0]
  | 15 => !![0, -1; 1, 0]

@[simp] theorem quaternionRep_blade (i : Fin 16) :
    quaternionRep (blade i) = bladeMatrix i := by
  fin_cases i <;>
    simp only [blade, bladeMatrix, map_one, map_mul, quaternionRep_gamma] <;>
    ext r c <;> fin_cases r <;> fin_cases c <;> ext <;>
    norm_num [vectorMatrix, basisVec, timeMatrix, quaternionI, quaternionJ,
      quaternionK, Matrix.mul_apply, Fin.sum_univ_two]

private theorem quaternionRep_time_reverse (a : Cl14) :
    quaternionRep (gamma 0 * CliffordAlgebra.reverse a * gamma 0) =
      star (quaternionRep a) := by
  rw [map_mul, map_mul, quaternionRep_gamma_zero, quaternionRep_reverse,
    matrixReverse]
  calc
    timeMatrix * (timeMatrix * star (quaternionRep a) * timeMatrix) * timeMatrix =
        (timeMatrix * timeMatrix) * star (quaternionRep a) *
          (timeMatrix * timeMatrix) := by simp only [mul_assoc]
    _ = _ := by rw [timeMatrix_sq]; simp

/-- Every ordered blade has unit positive norm, and distinct blades are
orthogonal, for the scalar pairing with timelike-twisted reversion. -/
theorem scalar_blade_time_reverse_blade (i j : Fin 16) :
    scalar (blade i * gamma 0 * CliffordAlgebra.reverse (blade j) * gamma 0) =
      if i = j then 1 else 0 := by
  have hassoc : blade i * gamma 0 * CliffordAlgebra.reverse (blade j) * gamma 0 =
      blade i * (gamma 0 * CliffordAlgebra.reverse (blade j) * gamma 0) := by
    simp only [mul_assoc]
  rw [hassoc]
  have hrep : quaternionRep
      (blade i * (gamma 0 * CliffordAlgebra.reverse (blade j) * gamma 0)) =
        bladeMatrix i * star (bladeMatrix j) := by
    rw [map_mul, quaternionRep_time_reverse, quaternionRep_blade,
      quaternionRep_blade]
  simp only [scalar, LinearMap.coe_mk, AddHom.coe_mk, hrep]
  fin_cases i <;> fin_cases j <;>
    norm_num [bladeMatrix, timeMatrix, quaternionI, quaternionJ, quaternionK,
      Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two]

/-- The scalar pairing against a fixed blade is a native real linear functional. -/
def bladeCoordinate (j : Fin 16) : Cl14 →ₗ[ℝ] ℝ where
  toFun a := scalar (a * gamma 0 * CliffordAlgebra.reverse (blade j) * gamma 0)
  map_add' a b := by simp only [add_mul, map_add]
  map_smul' r a := by simp only [smul_mul_assoc, map_smul]

@[simp] theorem bladeCoordinate_blade (i j : Fin 16) :
    bladeCoordinate j (blade i) = if i = j then 1 else 0 :=
  scalar_blade_time_reverse_blade i j

/-- The actual Clifford products are linearly independent over the reals. -/
theorem blade_linearIndependent : LinearIndependent ℝ blade := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (bladeCoordinate j) hc
  simpa [map_sum, map_smul, smul_eq_mul, mul_ite] using h

/-- The sixteen ordered products form a basis of the entire native `Cl(1,3)`. -/
def bladeBasis : Module.Basis (Fin 16) ℝ Cl14 :=
  basisOfLinearIndependentOfCardEqFinrank blade_linearIndependent (by
    simp only [Fintype.card_fin, HestenesEvenPauliEquiv.cliffordAlgebra14_finrank])

@[simp] theorem bladeBasis_apply (i : Fin 16) : bladeBasis i = blade i := by
  simp [bladeBasis]

/-- The computed scalar duals are exactly the coordinates of the proved basis. -/
theorem bladeBasis_repr_apply (a : Cl14) (i : Fin 16) :
    bladeBasis.repr a i = bladeCoordinate i a := by
  have h := congrArg (bladeCoordinate i) (bladeBasis.sum_repr a)
  simpa [map_sum, map_smul, smul_eq_mul, mul_ite] using h

/-- Every Clifford element is reconstructed from the scalar dual readouts. -/
theorem blade_expansion (a : Cl14) :
    ∑ i : Fin 16, bladeCoordinate i a • blade i = a := by
  simpa only [bladeBasis_apply, bladeBasis_repr_apply] using bladeBasis.sum_repr a

@[simp] theorem scalar_blade (i : Fin 16) :
    scalar (blade i) = if i = 0 then 1 else 0 := by
  simp only [scalar, LinearMap.coe_mk, AddHom.coe_mk, quaternionRep_blade]
  fin_cases i <;>
    norm_num [bladeMatrix, timeMatrix, quaternionI, quaternionJ, quaternionK]

/-- The normalized quaternion real trace is the grade-zero coefficient in the
actual ordered Clifford basis, rather than an arbitrary matrix readout. -/
theorem scalar_eq_bladeBasis_repr_zero (a : Cl14) :
    scalar a = bladeBasis.repr a 0 := by
  have h := congrArg scalar (bladeBasis.sum_repr a)
  simpa [map_sum, map_smul, smul_eq_mul, mul_ite] using h.symm

/-- Exact indices of the native ordered blades with negative square. -/
def negativeBladeIndices : Finset (Fin 16) := {2, 3, 4, 8, 9, 10, 11, 12, 13, 15}

/-- Full square table: all sixteen products square to a real scalar sign. -/
theorem blade_mul_self (i : Fin 16) :
    blade i * blade i = if i ∈ negativeBladeIndices then -(1 : Cl14) else 1 := by
  fin_cases i <;> apply quaternionRep_injective <;>
    ext r c <;> fin_cases r <;> fin_cases c <;> ext <;>
    norm_num [map_mul, negativeBladeIndices, quaternionRep_blade, bladeMatrix,
      timeMatrix, quaternionI, quaternionJ, quaternionK,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The negative list is an equivalence about the actual Clifford square. -/
theorem blade_mul_self_eq_neg_one_iff (i : Fin 16) :
    blade i * blade i = -(1 : Cl14) ↔ i ∈ negativeBladeIndices := by
  constructor
  · intro h
    by_contra hi
    have hs : (1 : Cl14) = -1 := by
      simpa only [blade_mul_self, if_neg hi] using h
    have hscalar := congrArg scalar hs
    norm_num at hscalar
  · intro hi
    simp only [blade_mul_self, if_pos hi]

/-- Exactly ten of the sixteen ordered blades have square `-1`. -/
theorem negativeBladeIndices_card : negativeBladeIndices.card = 10 := by
  decide

end InfoGeometry.Clifford.RealSpacetimeBlades
