/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bridge
import InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral.FourierCharacterDefect

/-!
# Exact defects between the homogenized and Fourier Peirce channels

The double-commutator channels `hProjV`, `hProjPhi`, `hProjJ`, and `hProjSig`
and the four sandwich-character sums are different maps on a general input.
Their differences are explicit commutators with `V`. They agree on the
centralizer of `V`, without imposing commutativity on the ambient ring. The
generic defects already belong to `SquareZeroPairSpectral.FourierCharacterDefect`;
this module identifies the Peirce channels with that native endomorphism
owner and transports its theorems. The `Phi` and `J` channels agree exactly
when the input commutes with `V²`, a weaker condition than commuting with `V`.

The final evaluations distinguish a sandwich sum that weights only the
identity term by two from the existing Fourier sum, which doubles all four
terms. The former need not have scale eight or annihilate the `Phi` channel.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.OperatorAlgebra.LieJordan
open InfoGeometry.OperatorAlgebra.SquareZeroPairSpectral

variable {B : Type*} [Ring B]

/-! ### Identification with the square-zero-pair owner -/

/-- The spin Laplacian completes the existing dictionary for `Phi` and `J`. -/
theorem derivSqSig_eq_spinLaplacian (P A C X : B) :
    derivSqSig P A C X = spinLaplacian ℤ (conePlus P A) (coneMinus P C) X := by
  simp only [derivSqSig, spinLaplacian, LinearMap.neg_apply,
    Module.End.mul_apply, lieOp_apply, genSig, comm]

theorem hProjV_eq_projMass (P A C X : B) :
    hProjV P A C X = projMass ℤ (conePlus P A) (coneMinus P C) X := by
  rw [projMass_apply]
  simp only [hProjV, derivSqPhi_eq_phiLaplacian, derivSqJ_eq_jLaplacian,
    derivSqSig_eq_spinLaplacian, genV, anticomm, ofNat_zsmul, mul_assoc]
  abel

theorem hProjPhi_eq_projSum (P A C X : B) :
    hProjPhi P A C X = projSum ℤ (conePlus P A) (coneMinus P C) X := by
  rw [projSum_apply]
  simp only [hProjPhi, derivSqPhi_eq_phiLaplacian, derivSqJ_eq_jLaplacian,
    derivSqSig_eq_spinLaplacian, genV, anticomm]

theorem hProjJ_eq_projDifference (P A C X : B) :
    hProjJ P A C X = projDifference ℤ (conePlus P A) (coneMinus P C) X := by
  rw [projDifference_apply]
  simp only [hProjJ, derivSqPhi_eq_phiLaplacian, derivSqJ_eq_jLaplacian,
    derivSqSig_eq_spinLaplacian, genV, anticomm]

theorem hProjSig_eq_projSpin (P A C X : B) :
    hProjSig P A C X = projSpin ℤ (conePlus P A) (coneMinus P C) X := by
  rw [projSpin_apply]
  simp only [hProjSig, derivSqPhi_eq_phiLaplacian, derivSqJ_eq_jLaplacian,
    derivSqSig_eq_spinLaplacian, genV, anticomm]

theorem fourierV_eq_fourierProjMass (P A C X : B) :
    fourierV P A C X =
      fourierProjMass (u := conePlus P A) (v := coneMinus P C) X := by
  simp only [fourierV, grpId, grpPhi, grpJ, grpSig, fourierProjMass,
    fourierSandwichId, fourierSandwichSum, fourierSandwichDifference,
    fourierSandwichSpin, genV, anticomm, genPhi, genJ, genSig, comm,
    two_zsmul, two_nsmul]

theorem fourierPhi_eq_fourierProjSum (P A C X : B) :
    fourierPhi P A C X =
      fourierProjSum (u := conePlus P A) (v := coneMinus P C) X := by
  simp only [fourierPhi, grpId, grpPhi, grpJ, grpSig, fourierProjSum,
    fourierSandwichId, fourierSandwichSum, fourierSandwichDifference,
    fourierSandwichSpin, genV, anticomm, genPhi, genJ, genSig, comm,
    two_zsmul, two_nsmul]

theorem fourierJ_eq_fourierProjDifference (P A C X : B) :
    fourierJ P A C X =
      fourierProjDifference (u := conePlus P A) (v := coneMinus P C) X := by
  simp only [fourierJ, grpId, grpPhi, grpJ, grpSig, fourierProjDifference,
    fourierSandwichId, fourierSandwichSum, fourierSandwichDifference,
    fourierSandwichSpin, genV, anticomm, genPhi, genJ, genSig, comm,
    two_zsmul, two_nsmul]

theorem fourierSig_eq_fourierProjSpin (P A C X : B) :
    fourierSig P A C X =
      fourierProjSpin (u := conePlus P A) (v := coneMinus P C) X := by
  simp only [fourierSig, grpId, grpPhi, grpJ, grpSig, fourierProjSpin,
    fourierSandwichId, fourierSandwichSum, fourierSandwichDifference,
    fourierSandwichSpin, genV, anticomm, genPhi, genJ, genSig, comm,
    two_zsmul, two_nsmul]

variable {P : B} (hP : P * P = P)
include hP

/-- The mass-channel discrepancy retains the ordered commutator with the
test operator. No centralizer assumption is made. -/
theorem hProjV_sub_fourierV (A C X : B) :
    hProjV P A C X - fourierV P A C X =
      (3 : ℤ) • (genV P A C * comm (genV P A C) X) +
        comm (genV P A C) X * genV P A C := by
  calc
    hProjV P A C X - fourierV P A C X =
        (3 : ℕ) • ((genV P A C * genV P A C) * X) -
          (2 : ℕ) • (genV P A C * X * genV P A C) -
            X * (genV P A C * genV P A C) := by
      simpa only [hProjV_eq_projMass, fourierV_eq_fourierProjMass, genV, anticomm]
        using projMass_fourierProjMass_defect (R := ℤ)
          (conePlus_mul_conePlus hP A A) (coneMinus_mul_coneMinus hP C C) X
    _ = _ := by simp only [comm]; noncomm_ring

/-- The `Phi`-channel discrepancy is the negative commutator with `V²`. -/
theorem hProjPhi_sub_fourierPhi (A C X : B) :
    hProjPhi P A C X - fourierPhi P A C X =
      -comm (genV P A C * genV P A C) X := by
  calc
    hProjPhi P A C X - fourierPhi P A C X =
        X * (genV P A C * genV P A C) -
          (genV P A C * genV P A C) * X := by
      simpa only [hProjPhi_eq_projSum, fourierPhi_eq_fourierProjSum, genV, anticomm]
        using projSum_fourierProjSum_defect (R := ℤ)
          (conePlus_mul_conePlus hP A A) (coneMinus_mul_coneMinus hP C C) X
    _ = _ := by simp only [comm]; noncomm_ring

/-- The `J`-channel has the same `V²` commutator defect. -/
theorem hProjJ_sub_fourierJ (A C X : B) :
    hProjJ P A C X - fourierJ P A C X =
      -comm (genV P A C * genV P A C) X := by
  calc
    hProjJ P A C X - fourierJ P A C X =
        X * (genV P A C * genV P A C) -
          (genV P A C * genV P A C) * X := by
      simpa only [hProjJ_eq_projDifference, fourierJ_eq_fourierProjDifference, genV, anticomm]
        using projDifference_fourierProjDifference_defect (R := ℤ)
          (conePlus_mul_conePlus hP A A) (coneMinus_mul_coneMinus hP C C) X
    _ = _ := by simp only [comm]; noncomm_ring

/-- The spin-channel discrepancy is a double commutator with `V`. -/
theorem hProjSig_sub_fourierSig (A C X : B) :
    hProjSig P A C X - fourierSig P A C X =
      -comm (genV P A C) (comm (genV P A C) X) := by
  calc
    hProjSig P A C X - fourierSig P A C X =
        (2 : ℕ) • (genV P A C * X * genV P A C) -
          (genV P A C * genV P A C) * X -
            X * (genV P A C * genV P A C) := by
      simpa only [hProjSig_eq_projSpin, fourierSig_eq_fourierProjSpin, genV, anticomm]
        using projSpin_fourierProjSpin_defect (R := ℤ)
          (conePlus_mul_conePlus hP A A) (coneMinus_mul_coneMinus hP C C) X
    _ = _ := by simp only [comm]; noncomm_ring

/-- The `Phi` comparison needs exactly commutation with `V²`. -/
theorem hProjPhi_eq_fourierPhi_iff_commute_mass_sq (A C X : B) :
    hProjPhi P A C X = fourierPhi P A C X ↔
      Commute X (genV P A C * genV P A C) := by
  simpa only [hProjPhi_eq_projSum, fourierPhi_eq_fourierProjSum, genV, anticomm]
    using projSum_fourierProjSum_eq_iff_commute_mass_sq (R := ℤ)
      (conePlus_mul_conePlus hP A A) (coneMinus_mul_coneMinus hP C C) X

/-- The `J` comparison has the same exact condition. -/
theorem hProjJ_eq_fourierJ_iff_commute_mass_sq (A C X : B) :
    hProjJ P A C X = fourierJ P A C X ↔
      Commute X (genV P A C * genV P A C) := by
  simpa only [hProjJ_eq_projDifference, fourierJ_eq_fourierProjDifference, genV, anticomm]
    using projDifference_fourierProjDifference_eq_iff_commute_mass_sq (R := ℤ)
      (conePlus_mul_conePlus hP A A) (coneMinus_mul_coneMinus hP C C) X

/-- The mass channels agree on every input commuting with `V`. -/
theorem hProjV_eq_fourierV_of_commute (A C X : B)
    (hVX : Commute (genV P A C) X) :
    hProjV P A C X = fourierV P A C X := by
  have hcomm : comm (genV P A C) X = 0 := sub_eq_zero.mpr hVX.eq
  apply sub_eq_zero.mp
  rw [hProjV_sub_fourierV hP]
  simp only [hcomm, mul_zero, zero_mul, smul_zero, add_zero]

/-- Commutation with `V` suffices for equality of the `Phi` channels. -/
theorem hProjPhi_eq_fourierPhi_of_commute (A C X : B)
    (hVX : Commute (genV P A C) X) :
    hProjPhi P A C X = fourierPhi P A C X := by
  have hcommSq : comm (genV P A C * genV P A C) X = 0 := by
    unfold comm
    rw [mul_assoc, hVX.eq, ← mul_assoc, hVX.eq, mul_assoc, sub_self]
  apply sub_eq_zero.mp
  rw [hProjPhi_sub_fourierPhi hP, hcommSq, neg_zero]

/-- Commutation with `V` suffices for equality of the `J` channels. -/
theorem hProjJ_eq_fourierJ_of_commute (A C X : B)
    (hVX : Commute (genV P A C) X) :
    hProjJ P A C X = fourierJ P A C X := by
  have hcommSq : comm (genV P A C * genV P A C) X = 0 := by
    unfold comm
    rw [mul_assoc, hVX.eq, ← mul_assoc, hVX.eq, mul_assoc, sub_self]
  apply sub_eq_zero.mp
  rw [hProjJ_sub_fourierJ hP, hcommSq, neg_zero]

/-- Commutation with `V` suffices for equality of the spin channels. -/
theorem hProjSig_eq_fourierSig_of_commute (A C X : B)
    (hVX : Commute (genV P A C) X) :
    hProjSig P A C X = fourierSig P A C X := by
  have hcomm : comm (genV P A C) X = 0 := sub_eq_zero.mpr hVX.eq
  apply sub_eq_zero.mp
  rw [hProjSig_sub_fourierSig hP, hcomm]
  simp only [comm, mul_zero, zero_mul, sub_self, neg_zero]

/-- Doubling only the identity sandwich gives coefficient five on `V`,
whereas `fourierV` doubles every term and gives coefficient eight. -/
theorem identity_weight_two_sandwich_sum_at_genV (A C : B) :
    (2 : ℤ) • grpId P A C (genV P A C) +
        grpPhi P A C (genV P A C) + grpJ P A C (genV P A C) +
        grpSig P A C (genV P A C) =
      (5 : ℤ) • ((genV P A C * genV P A C) * genV P A C) := by
  simp only [grpId, grpPhi, grpJ, grpSig]
  peirce_nf hP

/-- The same unequal weighting leaves the operator `V² * Phi`; it need
not annihilate the odd channel. -/
theorem identity_weight_two_sandwich_sum_at_genPhi (A C : B) :
    (2 : ℤ) • grpId P A C (genPhi P A C) +
        grpPhi P A C (genPhi P A C) + grpJ P A C (genPhi P A C) +
        grpSig P A C (genPhi P A C) =
      (genV P A C * genV P A C) * genPhi P A C := by
  simp only [grpId, grpPhi, grpJ, grpSig]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
