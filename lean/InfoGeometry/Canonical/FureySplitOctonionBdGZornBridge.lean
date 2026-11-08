/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FureySplitOctonionCommonCarrierBridge
import InfoGeometry.Canonical.FixedColourCoreZornEmbedding

/-!
# CAR mass anomaly in the fixed-colour operator-Zorn realization

The finite-mode split-octonion carrier supplies genuine CAR creation and
annihilation endomorphisms.  The fixed-colour map then places their BdG
commutator defect in the existing operator-valued Zorn carrier.  The CAR
relation identifies that defect with the centered occupation operator while
retaining the order of every operator product.
-/

noncomputable section

namespace InfoGeometry.Canonical.FureySplitOctonionBdGZornBridge

open InfoGeometry.Canonical.FureySplitOctonionCommonCarrierBridge
open InfoGeometry.Twistor.RealPolynomialCCR

/-! ### CAR defect as a Zorn-embedded particle-hole interaction -/

/-- The split-octonion CAR interaction defect, represented in the native
fixed-colour Zorn carrier, is the centered occupation operator
`c * a + c * a - 1`.  This is an operator identity; no scalar occupation
number or commutation reduction is used. -/
theorem splitOctonion_CAR_anomaly_is_centered_occupation_in_Zorn
    (k i : Fin 3) :
    InfoGeometry.Canonical.fixedColourEmbedding k
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly
          (zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i))
          (zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i))) =
      InfoGeometry.Canonical.fixedColourEmbedding k
        (!![0,
            zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i) *
                zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) +
              zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i) *
                zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) - 1;
            1 - (zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i) *
                  zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) +
              zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i) *
                zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i)),
            0]) := by
  let c := zornFermionLift
    (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i)
  let a := zornFermionLift
    (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i)
  have hCAR : a * c + c * a = 1 := by
    simpa [a, c] using splitOctonionCommonCarrier_CAR i i
  have hAC : a * c = 1 - c * a := by
    calc
      a * c = (a * c + c * a) - c * a := by
        exact (add_sub_cancel_right (a * c) (c * a)).symm
      _ = 1 - c * a := by rw [hCAR]
  have hMatrix :
      InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a =
        !![0, c * a + c * a - 1; 1 - (c * a + c * a), 0] := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [InfoGeometry.Physics.massiveBdGCommutatorAnomaly, hAC] <;>
      noncomm_ring
  exact congrArg (InfoGeometry.Canonical.fixedColourEmbedding k) hMatrix

/-- Andreev particle-hole reflection cancels the centered CAR occupation
defect after it has been transported into the operator-Zorn carrier. -/
theorem splitOctonion_CAR_centered_defect_cancels_under_Andreev_in_Zorn
    (k i : Fin 3) :
    let centered :=
      InfoGeometry.Canonical.fixedColourEmbedding k
        (!![0,
            zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i) *
                zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) +
              zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i) *
                zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) - 1;
            1 - (zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i) *
                  zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i) +
              zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i) *
                zornFermionLift (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i)),
            0])
    centered +
      InfoGeometry.Canonical.operatorZornMul
        (InfoGeometry.Canonical.operatorZornMul
          (InfoGeometry.Canonical.fixedColourEmbedding k
            InfoGeometry.Physics.andreevSwap)
          centered)
        (InfoGeometry.Canonical.fixedColourEmbedding k
          InfoGeometry.Physics.andreevSwap) = 0 := by
  dsimp
  let c := zornFermionLift
    (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i)
  let a := zornFermionLift
    (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i)
  rw [← splitOctonion_CAR_anomaly_is_centered_occupation_in_Zorn k i]
  have hReflected :
      InfoGeometry.Canonical.operatorZornMul
          (InfoGeometry.Canonical.operatorZornMul
            (InfoGeometry.Canonical.fixedColourEmbedding k
              InfoGeometry.Physics.andreevSwap)
            (InfoGeometry.Canonical.fixedColourEmbedding k
              (InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a)))
          (InfoGeometry.Canonical.fixedColourEmbedding k
            InfoGeometry.Physics.andreevSwap) =
        InfoGeometry.Canonical.fixedColourEmbedding k
          (InfoGeometry.Physics.andreevSwap *
            InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a *
            InfoGeometry.Physics.andreevSwap) := by
    rw [← InfoGeometry.Canonical.fixedColourEmbedding_mul k
      InfoGeometry.Physics.andreevSwap
      (InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a)]
    rw [← InfoGeometry.Canonical.fixedColourEmbedding_mul k
      (InfoGeometry.Physics.andreevSwap *
        InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a)
      InfoGeometry.Physics.andreevSwap]
  calc
    _ = InfoGeometry.Canonical.fixedColourEmbedding k
          (InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a) +
        InfoGeometry.Canonical.fixedColourEmbedding k
          (InfoGeometry.Physics.andreevSwap *
            InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a *
            InfoGeometry.Physics.andreevSwap) := by rw [hReflected]
    _ = InfoGeometry.Canonical.fixedColourEmbedding k
          (InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a +
            InfoGeometry.Physics.andreevSwap *
              InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a *
              InfoGeometry.Physics.andreevSwap) :=
      (InfoGeometry.Canonical.fixedColourEmbedding_add k _ _).symm
    _ = 0 := by
      rw [InfoGeometry.Physics.andreev_reflect_mass_commutator_anomaly]
      rw [InfoGeometry.Canonical.fixedColourEmbedding_add k _ _]
      have hneg :
          InfoGeometry.Canonical.fixedColourEmbedding k
              (-InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a) =
            -InfoGeometry.Canonical.fixedColourEmbedding k
              (InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a) := by
        apply eq_neg_iff_add_eq_zero.mpr
        calc
          InfoGeometry.Canonical.fixedColourEmbedding k
              (-InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a) +
            InfoGeometry.Canonical.fixedColourEmbedding k
              (InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a) =
              InfoGeometry.Canonical.fixedColourEmbedding k
                (-InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a +
                  InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a) :=
            (InfoGeometry.Canonical.fixedColourEmbedding_add k _ _).symm
          _ = 0 := by
            have hcancel :
                -InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a +
                  InfoGeometry.Physics.massiveBdGCommutatorAnomaly c a = 0 :=
              by ext r s <;> simp
            rw [hcancel]
            exact InfoGeometry.Canonical.fixedColourEmbedding_zero k
      rw [hneg, add_neg_cancel]

end InfoGeometry.Canonical.FureySplitOctonionBdGZornBridge

end
