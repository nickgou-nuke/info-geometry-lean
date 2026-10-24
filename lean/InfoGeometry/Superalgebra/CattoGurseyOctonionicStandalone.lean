/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CattoGurseySplitBasis
import InfoGeometry.Algebra.ZornDerivationBridge

/-!
# Integer readout of the existing signed Zorn basis

The historical module name is retained, but no independent vector carrier or
multiplication is defined here. The convention is `u0 = E11`, `u0Star = E22`,
`u = -U`, `uStar = V`: the two named families and singlets are exchanged relative
to `Canonical.GunaydinGursey`. The multiplication table is unchanged.
This is a nonassociative element table, not an operator CAR or gl(3|1) theorem.
-/
namespace CattoGurseyOctonionicStandalone
open InfoGeometry.Algebra

abbrev SplitOctonion := ZornVectorMatrix ℤ

namespace SplitOctonion
noncomputable section

local instance : One SplitOctonion := ⟨ZornVectorMatrix.one⟩

abbrev splitOctonion_mul := ZornVectorMatrix.mul (R := ℤ)
abbrev anticomm (X Y : SplitOctonion) := X * Y + Y * X
abbrev comm := ZornVectorMatrix.commutator (R := ℤ)
abbrev associator := ZornVectorMatrix.associator (R := ℤ)
abbrev jacobiator := ZornVectorMatrix.commutatorJacobiator (R := ℤ)

abbrev u0 : SplitOctonion := InfoGeometry.Canonical.GunaydinGursey.uStarZero
abbrev u0Star : SplitOctonion := InfoGeometry.Canonical.GunaydinGursey.uZero
abbrev ie7 : SplitOctonion := ZornVectorMatrix.diagonal 1 (-1)
abbrev u (i : Fin 3) : SplitOctonion := InfoGeometry.Canonical.GunaydinGursey.uStar i
abbrev uStar (i : Fin 3) : SplitOctonion := InfoGeometry.Canonical.GunaydinGursey.u i

theorem page4_split_octonion_multiplication_table :
    (u0 * u0 = (u0 : SplitOctonion) ∧
     u0Star * u0Star = (u0Star : SplitOctonion) ∧
     u0 * u0Star = (0 : SplitOctonion) ∧
     u0Star * u0 = (0 : SplitOctonion) ∧
     u0 + u0Star = (1 : SplitOctonion)) ∧
    (∀ j : Fin 3,
      u0 * u j = u j ∧ u j * u0Star = u j ∧
      u0Star * u j = (0 : SplitOctonion) ∧ u j * u0 = (0 : SplitOctonion) ∧
      u0Star * uStar j = uStar j ∧ uStar j * u0 = uStar j ∧
      u0 * uStar j = (0 : SplitOctonion) ∧ uStar j * u0Star = (0 : SplitOctonion)) ∧
    (u 0 * u 1 = (uStar 2 : SplitOctonion) ∧ u 1 * u 0 = -uStar 2 ∧
     u 1 * u 2 = (uStar 0 : SplitOctonion) ∧ u 2 * u 1 = -uStar 0 ∧
     u 2 * u 0 = (uStar 1 : SplitOctonion) ∧ u 0 * u 2 = -uStar 1 ∧
     uStar 0 * uStar 1 = (u 2 : SplitOctonion) ∧
     uStar 1 * uStar 2 = (u 0 : SplitOctonion) ∧
     uStar 2 * uStar 0 = (u 1 : SplitOctonion)) ∧
    (∀ i : Fin 3, u i * uStar i = -u0 ∧ uStar i * u i = -u0Star) ∧
    (∀ i j : Fin 3, i ≠ j → u i * uStar j = (0 : SplitOctonion) ∧ uStar i * u j = (0 : SplitOctonion)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨InfoGeometry.Canonical.GunaydinGursey.uStarZero_sq,
      InfoGeometry.Canonical.GunaydinGursey.uZero_sq,
      InfoGeometry.Canonical.GunaydinGursey.uStarZero_mul_uZero,
      InfoGeometry.Canonical.GunaydinGursey.uZero_mul_uStarZero, ?_⟩
    change InfoGeometry.Canonical.GunaydinGursey.uStarZero +
        InfoGeometry.Canonical.GunaydinGursey.uZero =
      (ZornVectorMatrix.one : ZornVectorMatrix ℤ)
    rw [add_comm]
    exact InfoGeometry.Canonical.GunaydinGursey.singlet_sum (R := ℤ)
  · intro i
    obtain ⟨h₁, h₂, h₃, h₄⟩ :=
      InfoGeometry.Canonical.GunaydinGursey.antitriplet_absorption (R := ℤ) i
    exact ⟨h₁, h₂, h₃, h₄,
      InfoGeometry.Canonical.GunaydinGursey.uZero_mul_u i,
      InfoGeometry.Canonical.GunaydinGursey.u_mul_uStarZero i,
      InfoGeometry.Canonical.GunaydinGursey.uStarZero_mul_u i,
      InfoGeometry.Canonical.GunaydinGursey.u_mul_uZero i⟩
  · change
      ((-ZornVectorMatrix.U 0 : SplitOctonion) * (-ZornVectorMatrix.U 1) = ZornVectorMatrix.V 2 ∧
       (-ZornVectorMatrix.U 1) * (-ZornVectorMatrix.U 0) = -ZornVectorMatrix.V 2 ∧
       (-ZornVectorMatrix.U 1) * (-ZornVectorMatrix.U 2) = ZornVectorMatrix.V 0 ∧
       (-ZornVectorMatrix.U 2) * (-ZornVectorMatrix.U 1) = -ZornVectorMatrix.V 0 ∧
       (-ZornVectorMatrix.U 2) * (-ZornVectorMatrix.U 0) = ZornVectorMatrix.V 1 ∧
       (-ZornVectorMatrix.U 0) * (-ZornVectorMatrix.U 2) = -ZornVectorMatrix.V 1 ∧
       ZornVectorMatrix.V 0 * ZornVectorMatrix.V 1 = -ZornVectorMatrix.U 2 ∧
       ZornVectorMatrix.V 1 * ZornVectorMatrix.V 2 = -ZornVectorMatrix.U 0 ∧
       ZornVectorMatrix.V 2 * ZornVectorMatrix.V 0 = -ZornVectorMatrix.U 1)
    simp only [zvm_mul_def, zvm_neg_def, ZornVectorMatrix.neg_mul, ZornVectorMatrix.mul_neg,
      ZornVectorMatrix.U_zero_mul_U_one, ZornVectorMatrix.U_one_mul_U_zero,
      ZornVectorMatrix.U_one_mul_U_two, ZornVectorMatrix.U_two_mul_U_one,
      ZornVectorMatrix.U_two_mul_U_zero, ZornVectorMatrix.U_zero_mul_U_two,
      ZornVectorMatrix.V_zero_mul_V_one, ZornVectorMatrix.V_one_mul_V_two,
      ZornVectorMatrix.V_two_mul_V_zero]
    simp only [← zvm_neg_def, _root_.neg_neg, and_self]
  · intro i
    have h := InfoGeometry.Canonical.GunaydinGursey.mixed_table (R := ℤ) i i
    refine ⟨?_, ?_⟩
    · change ZornVectorMatrix.mul (InfoGeometry.Canonical.GunaydinGursey.uStar i)
          (InfoGeometry.Canonical.GunaydinGursey.u i) =
        -InfoGeometry.Canonical.GunaydinGursey.uStarZero
      simpa only [ite_true] using h.2
    · change ZornVectorMatrix.mul (InfoGeometry.Canonical.GunaydinGursey.u i)
          (InfoGeometry.Canonical.GunaydinGursey.uStar i) =
        -InfoGeometry.Canonical.GunaydinGursey.uZero
      simpa only [ite_true] using h.1
  · intro i j hij
    refine ⟨?_, ?_⟩
    · change ZornVectorMatrix.mul (InfoGeometry.Canonical.GunaydinGursey.uStar i)
          (InfoGeometry.Canonical.GunaydinGursey.u j) =
        (0 : ZornVectorMatrix ℤ)
      have hji : j ≠ i := Ne.symm hij
      simpa only [hji, ite_false] using
        (InfoGeometry.Canonical.GunaydinGursey.mixed_table (R := ℤ) j i).2
    · change ZornVectorMatrix.mul (InfoGeometry.Canonical.GunaydinGursey.u i)
          (InfoGeometry.Canonical.GunaydinGursey.uStar j) =
        (0 : ZornVectorMatrix ℤ)
      simpa only [hij, ite_false] using
        (InfoGeometry.Canonical.GunaydinGursey.mixed_table (R := ℤ) i j).1

end
end SplitOctonion
end CattoGurseyOctonionicStandalone
