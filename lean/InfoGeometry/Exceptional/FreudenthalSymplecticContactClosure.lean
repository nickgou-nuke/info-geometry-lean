/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Exceptional.FreudenthalSymplecticContactCommonCARCCR
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.FreudenthalSymplecticContactGrading
import InfoGeometry.Exceptional.FreudenthalSymplecticContactLieAlgebra
import InfoGeometry.Exceptional.FreudenthalSymplecticTKKJacobiObstruction

noncomputable section
namespace InfoGeometry.Exceptional.Freudenthal
variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

abbrev contactRho : FiveGradedCarrier D →ₗ⁅ℝ⁆ SymplecticContactEnd (J := J) :=
  symplecticContactRepresentationLieHom D

theorem contactRho_injective (D : CubicJordanDatum J) :
    Function.Injective (contactRho D) :=
  symplecticContactRepresentationLieHom_injective D

theorem contactRho_map_lie (u v : FiveGradedCarrier D) :
    contactRho D ⁅u, v⁆ = ⁅contactRho D u, contactRho D v⁆ :=
  (contactRho D).map_lie u v

theorem common_carrier_CAR_CCR :
    contactFermionAnnihilation (J := J) *
        contactFermionCreation (J := J) +
      contactFermionCreation (J := J) *
        contactFermionAnnihilation (J := J) = 1 ∧
      contactBosonAnnihilation (J := J) *
          contactBosonCreation (J := J) -
        contactBosonCreation (J := J) *
          contactBosonAnnihilation (J := J) = 1 :=
  ⟨contactFermion_CAR (J := J), contactBoson_CCR (J := J)⟩

theorem symplectic_contact_verified_closure_packet (u v : FiveGradedCarrier D) :
    contactRho D ⁅u, v⁆ = ⁅contactRho D u, contactRho D v⁆ ∧
      Function.Injective (contactRho D) :=
  ⟨contactRho_map_lie D u v, contactRho_injective D⟩

/-- **Emergent 5-Grade Cancellation of the 3-Graded Symplectic Jacobi Obstruction**:
in the 3-graded TKK truncation, the `(-1, +1, -1)` Jacobiator leaves the explicit
non-zero residual `(ω(y,x)•z + ω(z,x)•y) - (ω(y,z)•x + ω(x,z)•y)` (`tkk_mixed_jacobi_minus1_obstruction_explicit`).
Extending the algebra with the emergent grade-`0` seniority scale channel
(`ω(y,z)•x - ω(y,x)•z`) and the emergent grade-`-2` Heisenberg pairing channel
(`(-2 * ω(z,x))•y`) cancels the 3-graded defect identically and closes the global
5-graded Lie Jacobi identity `⁅x⁻¹, ⁅y⁺¹, z⁻¹⁆⁆ + ⁅y⁺¹, ⁅z⁻¹, x⁻¹⁆⁆ + ⁅z⁻¹, ⁅x⁻¹, y⁺¹⁆⁆ = 0`. -/
theorem three_grade_jacobi_obstruction_cancelled_by_emergent_five_grades
    (x y z : FreudenthalCharge J) :
    ((tkkTotalBracket D (injMinus1 D x)
        (tkkTotalBracket D (injPlus1 D y) (injMinus1 D z))).minus1 +
      (tkkTotalBracket D (injPlus1 D y)
        (tkkTotalBracket D (injMinus1 D z) (injMinus1 D x))).minus1 +
      (tkkTotalBracket D (injMinus1 D z)
        (tkkTotalBracket D (injMinus1 D x) (injPlus1 D y))).minus1) +
      (FreudenthalCharge.symplecticForm D y z • x -
        FreudenthalCharge.symplecticForm D y x • z) +
      ((-2 * FreudenthalCharge.symplecticForm D z x) • y) = 0 ∧
    (⁅injChargeMinus D x, ⁅injChargePlus D y, injChargeMinus D z⁆⁆ +
      ⁅injChargePlus D y, ⁅injChargeMinus D z, injChargeMinus D x⁆⁆ +
      ⁅injChargeMinus D z, ⁅injChargeMinus D x, injChargePlus D y⁆⁆ :
        FiveGradedCarrier D) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [tkk_mixed_jacobi_minus1_obstruction_explicit D x z y]
    have hzx := FreudenthalCharge.symplectic_form_skew D z x
    calc
      (FreudenthalCharge.symplecticForm D y x • z +
          FreudenthalCharge.symplecticForm D z x • y -
          (FreudenthalCharge.symplecticForm D y z • x +
            FreudenthalCharge.symplecticForm D x z • y)) +
        (FreudenthalCharge.symplecticForm D y z • x -
          FreudenthalCharge.symplecticForm D y x • z) +
        ((-2 * FreudenthalCharge.symplecticForm D z x) • y)
        = (FreudenthalCharge.symplecticForm D z x -
            FreudenthalCharge.symplecticForm D x z +
            (-2 * FreudenthalCharge.symplecticForm D z x)) • y := by module
      _ = (FreudenthalCharge.symplecticForm D z x +
            FreudenthalCharge.symplecticForm D z x -
            2 * FreudenthalCharge.symplecticForm D z x) • y := by
          rw [hzx]; module
      _ = 0 := by
          have h0 :
              FreudenthalCharge.symplecticForm D z x +
                FreudenthalCharge.symplecticForm D z x -
                2 * FreudenthalCharge.symplecticForm D z x = 0 := by ring
          rw [h0, zero_smul]
  · simpa [add_assoc] using
      lie_jacobi (injChargeMinus D x) (injChargePlus D y) (injChargeMinus D z)

end InfoGeometry.Exceptional.Freudenthal
