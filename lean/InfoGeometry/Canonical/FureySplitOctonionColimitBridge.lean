/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FureySplitOctonionCommonCarrierBridge
import InfoGeometry.Canonical.FiniteCARCCRPeirceBridge
import InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
import InfoGeometry.Canonical.FixedColourCoreZornEmbedding
import InfoGeometry.Canonical.SplitOctonionCl55ZornActionBridge
import InfoGeometry.Canonical.FureySplitOctonionSuperchargeBridge
import InfoGeometry.Canonical.Cl55AllModeMassCoercivity
import InfoGeometry.Clifford.Cl11StarAlgebraColimit
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentationAdditivityWave17

/-!
# Finite CAR interaction in the Cl(5,5) matrix stage and UHF colimit

The same first-three-mode CAR pair has three already-owned realizations:
the polynomial–split-octonion carrier, the faithful Cl(5,5) spinor matrix
stage, and its UHF colimit image. These theorems show that the CAR
noncommutation remains nonzero in the colimit and that the corresponding
fixed-colour BdG anomaly is canceled by its Andreev-reflected hole term there.
-/

noncomputable section

namespace InfoGeometry.Canonical.FureySplitOctonionColimitBridge

open InfoGeometry.Canonical.FureySplitOctonionCommonCarrierBridge
open InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
open InfoGeometry.Canonical.FiniteCARCCRCommonCarrier
open InfoGeometry.Canonical.FiniteCARCCRPeirceBridge
open InfoGeometry.Canonical.SplitOctonionCl55ZornActionBridge
open InfoGeometry.Canonical.SplitOctonionCl55CARRestrictionBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.FureySplitOctonionSuperchargeBridge
open InfoGeometry.Canonical.Cl55AllModeMassCoercivity
open InfoGeometry.Canonical.Cl55CARRepresentationCalibration
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11StarAlgebraColimit
open InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
open InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
open InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Clifford.ExteriorZornCARIntertwiner
open InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation
open InfoGeometry.Canonical

private theorem cl55ToStage5_injective : Function.Injective cl55ToStage5 :=
  (InfoGeometry.Clifford.TowerMatrix.matEquivFinPowTwo 5).symm.injective.comp
    (InfoGeometry.Clifford.Cl55FockMatrixIntertwiner.neutralCliffordCoordinateMatrixRep_injective.comp
      InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry.neutralCliffordAlgEquiv.symm.injective)

private theorem vacuumIdeal_leftAction_add (a b : Cl55)
    (x : cl55VacuumIdeal) :
    cl55VacuumIdealLeftAction (a + b) x =
      cl55VacuumIdealLeftAction a x + cl55VacuumIdealLeftAction b x := by
  apply Subtype.ext
  exact add_mul a b x.1

private theorem vacuumIdeal_leftAction_finset_sum_apply {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → Cl55)
    (x : cl55VacuumIdeal) :
    cl55VacuumIdealLeftAction (∑ i ∈ s, f i) x =
      ∑ i ∈ s, cl55VacuumIdealLeftAction (f i) x := by
  induction s using Finset.induction with
  | empty => simp [cl55VacuumIdealLeftAction]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [vacuumIdeal_leftAction_add, ih]

private theorem cl55_creation_annihilation_do_not_commute (i : Fin 3) :
    creation55 (Fin.castAdd 2 i) * annihilation55 (Fin.castAdd 2 i) ≠
      annihilation55 (Fin.castAdd 2 i) * creation55 (Fin.castAdd 2 i) := by
  intro h
  have hRep := congrArg cl55CommonCarrierRep h
  have hcomm : InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (cl55CommonCarrierRep (creation55 (Fin.castAdd 2 i)))
      (cl55CommonCarrierRep (annihilation55 (Fin.castAdd 2 i))) = 0 := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    change cl55CommonCarrierRep (creation55 (Fin.castAdd 2 i)) *
      cl55CommonCarrierRep (annihilation55 (Fin.castAdd 2 i)) -
      cl55CommonCarrierRep (annihilation55 (Fin.castAdd 2 i)) *
      cl55CommonCarrierRep (creation55 (Fin.castAdd 2 i)) = 0
    have hRep' :
        cl55CommonCarrierRep (creation55 (Fin.castAdd 2 i)) *
          cl55CommonCarrierRep (annihilation55 (Fin.castAdd 2 i)) =
        cl55CommonCarrierRep (annihilation55 (Fin.castAdd 2 i)) *
          cl55CommonCarrierRep (creation55 (Fin.castAdd 2 i)) := by
      simpa only [map_mul] using hRep
    calc
      cl55CommonCarrierRep (creation55 (Fin.castAdd 2 i)) *
          cl55CommonCarrierRep (annihilation55 (Fin.castAdd 2 i)) -
        cl55CommonCarrierRep (annihilation55 (Fin.castAdd 2 i)) *
          cl55CommonCarrierRep (creation55 (Fin.castAdd 2 i))
          = cl55CommonCarrierRep (annihilation55 (Fin.castAdd 2 i)) *
              cl55CommonCarrierRep (creation55 (Fin.castAdd 2 i)) -
            cl55CommonCarrierRep (annihilation55 (Fin.castAdd 2 i)) *
              cl55CommonCarrierRep (creation55 (Fin.castAdd 2 i)) := by rw [hRep']
      _ = 0 := sub_self
        (cl55CommonCarrierRep (annihilation55 (Fin.castAdd 2 i)) *
          cl55CommonCarrierRep (creation55 (Fin.castAdd 2 i)))
  exact commonCarrier_car_commutator_ne_zero (Fin.castAdd 2 i) hcomm

/-- The Cl(5,5) positive-null generator has the same nonzero action on the
split-octonion vacuum state as the existing Zorn creation operator. -/
theorem cl55_color_mode_has_nonzero_Zorn_vacuum_action (i : Fin 3) :
    fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv
        (cl55VacuumIdealLeftAction
          (annihilation55 (Fin.castAdd 2 i))
          (colorStateInCl55Ideal (1 : Exterior3))))) ≠ 0 := by
  rw [cl55_color_creation_as_zorn, fockToZorn_one, creationMap_basis]
  intro h
  have hv := (regular_vacuum i).2.1
  rw [hv] at h
  have hcoord := congrArg
    (fun z : InfoGeometry.Canonical.ZornMatrix ℝ => z.x i) h
  norm_num [InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis] at hcoord

/-- The actual Cl(5,5) Majorana generator on the color ideal transports to
the native Zorn Majorana operator on every color state. This composes the
already-owned vacuum-ideal restriction with the exterior-to-Zorn intertwiner. -/
theorem cl55_color_majorana_as_zorn (i : Fin 3) (ψ : Exterior3) :
    fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv
        (cl55VacuumIdealLeftAction
          (annihilation55 (Fin.castAdd 2 i) + creation55 (Fin.castAdd 2 i))
          (colorStateInCl55Ideal ψ)))) =
      (create i + annihilate i) (fockToZorn ψ) := by
  rw [vacuumIdeal_leftAction_add, map_add, map_add, map_add]
  rw [cl55_color_creation_as_zorn, cl55_color_annihilation_as_zorn]
  simp [creationMap_basis]

/-- Sum the three first-color Cl(5,5) Majorana actions on the vacuum ideal.
This is the genuine finite operator mass on the 32-dimensional carrier. -/
def cl55ColorMajoranaEnd : Module.End ℝ cl55VacuumIdeal :=
  ∑ i : Fin 3,
    cl55VacuumIdealLeftAction
      (annihilation55 (Fin.castAdd 2 i) + creation55 (Fin.castAdd 2 i))

/-- The vacuum-ideal action is multiplicative in the Clifford operator. -/
theorem cl55VacuumIdealLeftAction_mul (a b : Cl55) :
    cl55VacuumIdealLeftAction (a * b) =
      cl55VacuumIdealLeftAction a * cl55VacuumIdealLeftAction b := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (a * b) * x.1 = a * (b * x.1)
  exact mul_assoc a b x.1

/-- The summed finite color Majorana operator is the action of the native
Cl(5,5) color mass element. -/
theorem cl55ColorMajoranaEnd_apply (x : cl55VacuumIdeal) :
    cl55ColorMajoranaEnd x =
      cl55VacuumIdealLeftAction nativeThreeColorModeMajorana x := by
  apply Subtype.ext
  change (∑ i : Fin 3,
      (annihilation55 (Fin.castAdd 2 i) + creation55 (Fin.castAdd 2 i)) * x.1) =
    (∑ i : Fin 3,
      (creation55 (Fin.castAdd 2 i) + annihilation55 (Fin.castAdd 2 i))) * x.1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [add_comm (annihilation55 (Fin.castAdd 2 i))]

/-- The finite native color mass preserves the embedded three-mode exterior
subspace, and its action there is exactly the Zorn Majorana sum. This is the
uncompressed first-three-mode intertwiner; the spectator-mode contribution
to the full five-mode mass is intentionally excluded. -/
theorem cl55_color_mass_preserves_and_intertwines_includeColorExterior
    (ψ : Exterior3) :
    cl55VacuumIdealSpinorEquiv
      (cl55ColorMajoranaEnd (colorStateInCl55Ideal ψ)) =
      includeColorExterior
        (∑ i : Fin 3,
          (InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorWedge3
              (InfoGeometry.Canonical.SplitOctonionCl55ExteriorRestrictionBridge.basisVector3 i) ψ +
            InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorContract3
              (LinearMap.proj i) ψ)) := by
  classical
  simp only [cl55ColorMajoranaEnd, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [vacuumIdeal_leftAction_add, map_add,
    cl55_annihilation55_restricts_to_color_creation,
    cl55_creation55_restricts_to_color_annihilation]
  exact (map_add includeColorExterior _ _).symm

/-- On the actual Cl(5,5) vacuum ideal, the three-mode color mass squares to
three times the identity operator. This is the finite carrier theorem used
before transporting the action to the split-Zorn state module. -/
theorem cl55ColorMajoranaEnd_square :
    ∀ x : cl55VacuumIdeal,
      cl55ColorMajoranaEnd (cl55ColorMajoranaEnd x) = (3 : ℝ) • x := by
  have hmass := nativeColor_and_complement_mass_squares.1
  intro x
  rw [cl55ColorMajoranaEnd_apply, cl55ColorMajoranaEnd_apply]
  apply Subtype.ext
  change nativeThreeColorModeMajorana *
      (nativeThreeColorModeMajorana * x.1) = (3 : ℝ) • x.1
  rw [← mul_assoc, hmass]
  simp [Algebra.smul_def]

/-- The full finite color mass intertwines with the native three-mode Zorn
mass on every state in the color sector. Thus the CAR realization and the
Zorn operator realization are connected by the actual state-space map. -/
theorem cl55_color_three_mode_mass_as_zorn (ψ : Exterior3) :
    fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv
        (cl55ColorMajoranaEnd (colorStateInCl55Ideal ψ)))) =
      InfoGeometry.Canonical.FureySplitOctonionSuperchargeBridge.zornThreeModeMajoranaState
        (fockToZorn ψ) := by
  change fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv
        ((∑ i : Fin 3,
          cl55VacuumIdealLeftAction
            (annihilation55 (Fin.castAdd 2 i) + creation55 (Fin.castAdd 2 i)))
          (colorStateInCl55Ideal ψ)))) =
    ∑ i : Fin 3, (create i + annihilate i) (fockToZorn ψ)
  simp only [LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact cl55_color_majorana_as_zorn i ψ

/-- The two native complementary Cl(5,5) Majorana modes have zero action on
the three-color sector after the existing exterior-to-Zorn projection. -/
theorem cl55_complement_mass_projects_to_zero (ψ : Exterior3) :
    fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv
        (cl55VacuumIdealLeftAction nativeTwoComplementModeMajorana
          (colorStateInCl55Ideal ψ)))) = 0 := by
  unfold nativeTwoComplementModeMajorana
  rw [vacuumIdeal_leftAction_finset_sum_apply]
  unfold projectColorExterior
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [vacuumIdeal_leftAction_add, map_add, map_add, map_add,
    cl55_complement_creation_projects_to_zero,
    cl55_complement_annihilation_projects_to_zero]
  simp

/-- The full five-mode native Cl(5,5) Majorana mass restricts to the
three-mode Zorn mass: the complementary two modes contribute zero on the
embedded color exterior sector. -/
theorem cl55_five_mode_mass_restricts_to_zorn (ψ : Exterior3) :
    fockToZorn (projectColorExterior
      (cl55VacuumIdealSpinorEquiv
        (cl55VacuumIdealLeftAction nativeFiveModeMajorana
          (colorStateInCl55Ideal ψ)))) =
      InfoGeometry.Canonical.FureySplitOctonionSuperchargeBridge.zornThreeModeMajoranaState
        (fockToZorn ψ) := by
  rw [nativeFiveModeMajorana_color_two_mode_decomposition,
    vacuumIdeal_leftAction_add, map_add, map_add, map_add,
    cl55_complement_mass_projects_to_zero, add_zero]
  unfold nativeThreeColorModeMajorana
  rw [vacuumIdeal_leftAction_finset_sum_apply]
  simp only [map_sum]
  unfold zornThreeModeMajoranaState
  simp only [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [add_comm (creation55 (Fin.castAdd 2 i))
      (annihilation55 (Fin.castAdd 2 i)), cl55_color_majorana_as_zorn]

/-- Embed the existing split-octonion CAR state carrier into the algebraic
Fock direct limit by its finite three-mode exterior realization. This map is
the stage inclusion composed with the already-proved exterior/Zorn CAR
equivalence. -/
def zornStateToFockColimit :
    InfoGeometry.Canonical.ZornMatrix ℝ →ₗ[ℝ] FockInfinity :=
  (DirectLimit.Module.of ℝ ℕ FockStage
    (fun m n h => fockStageMap m n h) 3).comp
      exteriorZornCARLinearEquiv.symm.toLinearMap

/-- The first three recursive split-Clifford generators representing creation
on the Zorn CAR carrier. -/
def zornCreationClifford (i : Fin 3) : SplitClNNAlg 3 :=
  CliffordAlgebra.ι (TowerForm 3)
    (neutralPrimalSheetMap 3 (Pi.single i (1 : ℝ)))

/-- The first three recursive split-Clifford generators representing
annihilation on the Zorn CAR carrier. -/
def zornAnnihilationClifford (i : Fin 3) : SplitClNNAlg 3 :=
  CliffordAlgebra.ι (TowerForm 3)
    (neutralVacuumSheetMap 3 (LinearMap.proj i))

/-- Zorn creation agrees on every state with the action of its finite-stage
Clifford generator after passage to the algebraic Fock colimit. -/
theorem zorn_creation_intertwines_fock_colimit (i : Fin 3)
    (z : InfoGeometry.Canonical.ZornMatrix ℝ) :
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) 3 (zornCreationClifford i))
        (zornStateToFockColimit z) =
      zornStateToFockColimit
        (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i z) := by
  unfold zornCreationClifford zornStateToFockColimit
  change splitCliffordFockAction
      (DirectLimit.Algebra.of SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) 3
        (CliffordAlgebra.ι (TowerForm 3)
          (neutralPrimalSheetMap 3 (Pi.single i (1 : ℝ)))))
      (fockToInfinity 3 (exteriorZornCARLinearEquiv.symm z)) =
    fockToInfinity 3 (exteriorZornCARLinearEquiv.symm
      (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i z))
  rw [splitCliffordFockAction_generator_of]
  have hvector : (neutralToSplit 3).symm
      (neutralPrimalSheetMap 3 (Pi.single i (1 : ℝ))) =
        (Pi.single i (1 : ℝ), 0) := by
    simp [neutralPrimalSheetMap]
  have hstate : exteriorZornCARLinearEquiv.symm
      (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i z) =
      InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorWedge3
        (Pi.single i (1 : ℝ)) (exteriorZornCARLinearEquiv.symm z) := by
    apply exteriorZornCARLinearEquiv.injective
    calc
      exteriorZornCARLinearEquiv
          (exteriorZornCARLinearEquiv.symm
            (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i z)) =
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i z :=
        exteriorZornCARLinearEquiv.apply_symm_apply _
      _ = InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i
          (fockToZorn (exteriorZornCARLinearEquiv.symm z)) := by
        exact (congrArg
          (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i)
          (exteriorZornCARLinearEquiv.apply_symm_apply z)).symm
      _ = fockToZorn
          (InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorWedge3
            (Pi.single i (1 : ℝ)) (exteriorZornCARLinearEquiv.symm z)) :=
        (fockToZorn_wedge (Pi.single i (1 : ℝ))
          (exteriorZornCARLinearEquiv.symm z)).symm
      _ = exteriorZornCARLinearEquiv
          (InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorWedge3
            (Pi.single i (1 : ℝ)) (exteriorZornCARLinearEquiv.symm z)) := rfl
  change fockToInfinity 3
      (InfoGeometry.Clifford.spinorAction
        ((neutralToSplit 3).symm
          (neutralPrimalSheetMap 3 (Pi.single i (1 : ℝ))))
        (exteriorZornCARLinearEquiv.symm z)) = _
  rw [hvector]
  simp [InfoGeometry.Clifford.spinorAction, InfoGeometry.Clifford.extAction,
    InfoGeometry.Clifford.intAction]
  rw [hstate]
  rfl

/-- Zorn annihilation agrees on every state with the action of its finite-stage
Clifford generator after passage to the algebraic Fock colimit. -/
theorem zorn_annihilation_intertwines_fock_colimit (i : Fin 3)
    (z : InfoGeometry.Canonical.ZornMatrix ℝ) :
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) 3 (zornAnnihilationClifford i))
        (zornStateToFockColimit z) =
      zornStateToFockColimit
        (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i z) := by
  unfold zornAnnihilationClifford zornStateToFockColimit
  change splitCliffordFockAction
      (DirectLimit.Algebra.of SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) 3
        (CliffordAlgebra.ι (TowerForm 3)
          (neutralVacuumSheetMap 3 (LinearMap.proj i))))
      (fockToInfinity 3 (exteriorZornCARLinearEquiv.symm z)) =
    fockToInfinity 3 (exteriorZornCARLinearEquiv.symm
      (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i z))
  rw [splitCliffordFockAction_generator_of]
  have hvector : (neutralToSplit 3).symm
      (neutralVacuumSheetMap 3 (LinearMap.proj i)) =
        (0, (LinearMap.proj i :
          Module.Dual ℝ (InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.V3))) := by
    simp [neutralVacuumSheetMap]
  change fockToInfinity 3
      (InfoGeometry.Clifford.spinorAction
        ((neutralToSplit 3).symm
          (neutralVacuumSheetMap 3 (LinearMap.proj i)))
        (exteriorZornCARLinearEquiv.symm z)) = _
  rw [hvector]
  simp [InfoGeometry.Clifford.spinorAction, InfoGeometry.Clifford.extAction,
    InfoGeometry.Clifford.intAction]
  have hstate : exteriorZornCARLinearEquiv.symm
      (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i z) =
      InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorContract3
        (LinearMap.proj i) (exteriorZornCARLinearEquiv.symm z) := by
    apply exteriorZornCARLinearEquiv.injective
    calc
      exteriorZornCARLinearEquiv
          (exteriorZornCARLinearEquiv.symm
            (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i z)) =
          InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i z :=
        exteriorZornCARLinearEquiv.apply_symm_apply _
      _ = InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i
          (fockToZorn (exteriorZornCARLinearEquiv.symm z)) := by
        exact (congrArg
          (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i)
          (exteriorZornCARLinearEquiv.apply_symm_apply z)).symm
      _ = fockToZorn
          (InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorContract3
            (LinearMap.proj i) (exteriorZornCARLinearEquiv.symm z)) :=
        (fockToZorn_contract i (exteriorZornCARLinearEquiv.symm z)).symm
      _ = exteriorZornCARLinearEquiv
          (InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorContract3
            (LinearMap.proj i) (exteriorZornCARLinearEquiv.symm z)) := rfl
  rw [hstate]
  rfl

/-- The three-mode Zorn mass generator expressed in the finite split-Clifford
stage before passage to the operator colimit. -/
def zornThreeModeMajoranaClifford : SplitClNNAlg 3 :=
  ∑ i : Fin 3, (zornCreationClifford i + zornAnnihilationClifford i)

/-- The finite three-mode Majorana sum acts on every embedded Zorn state as
the existing split-Zorn mass operator. This is the operator-level bridge
between the CAR mass and the algebraic Fock colimit. -/
theorem zorn_mass_intertwines_fock_colimit
    (z : InfoGeometry.Canonical.ZornMatrix ℝ) :
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) 3 zornThreeModeMajoranaClifford)
        (zornStateToFockColimit z) =
      zornStateToFockColimit
        (zornThreeModeMajoranaState z) := by
  classical
  have hsum : ∀ s : Finset (Fin 3),
      splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m n h => splitCliffordMap m n h) 3
            (∑ i ∈ s, (zornCreationClifford i + zornAnnihilationClifford i)))
          (zornStateToFockColimit z) =
        zornStateToFockColimit
          ((∑ i ∈ s,
            (InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.create i +
              InfoGeometry.Algebra.Zorn.RegularCARVacuumSeparation.annihilate i)) z) := by
    intro s
    induction s using Finset.induction with
    | empty =>
      have hzero : splitCliffordFockAction (0 : SplitCliffordInfinity)
          (zornStateToFockColimit z) = 0 := by
        let y := splitCliffordFockAction (0 : SplitCliffordInfinity)
          (zornStateToFockColimit z)
        have hadd := splitCliffordFockAction_add_left
          (0 : SplitCliffordInfinity) 0 (zornStateToFockColimit z)
        have hyy : y = y + y := by simpa [y] using hadd
        have hcancel : y + y = y + 0 := by rw [← hyy, add_zero]
        exact add_left_cancel hcancel
      have hOfZero : DirectLimit.Algebra.of SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) 3
          (0 : SplitClNNAlg 3) = 0 :=
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) 3).map_zero
      simp only [Finset.sum_empty]
      rw [hOfZero]
      change splitCliffordFockAction 0 (zornStateToFockColimit z) =
        zornStateToFockColimit 0
      exact hzero.trans (map_zero zornStateToFockColimit).symm
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, map_add, splitCliffordFockAction_add_left, ih,
        map_add, splitCliffordFockAction_add_left,
        zorn_creation_intertwines_fock_colimit,
        zorn_annihilation_intertwines_fock_colimit]
      simp only [LinearMap.add_apply, map_add, Finset.sum_insert hi]
  simpa [zornThreeModeMajoranaClifford, zornThreeModeMajoranaState]
    using hsum Finset.univ

/-- The transported three-mode mass has the same exact quadratic value on the
algebraic Fock colimit: its square acts as three times the identity on every
state coming from the Zorn CAR carrier. -/
theorem zorn_mass_square_on_fock_colimit
    (z : InfoGeometry.Canonical.ZornMatrix ℝ) :
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) 3 zornThreeModeMajoranaClifford)
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m n h => splitCliffordMap m n h) 3 zornThreeModeMajoranaClifford)
          (zornStateToFockColimit z)) =
      (3 : ℝ) • zornStateToFockColimit z := by
  have hstate : zornThreeModeMajoranaState (zornThreeModeMajoranaState z) =
      (3 : ℝ) • z := by
    have h := congrArg (fun T : Module.End ℝ (InfoGeometry.Canonical.ZornMatrix ℝ) => T z)
      zornThreeModeMajoranaState_square
    simpa [Module.End.mul_apply] using h
  calc
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) 3 zornThreeModeMajoranaClifford)
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m n h => splitCliffordMap m n h) 3 zornThreeModeMajoranaClifford)
          (zornStateToFockColimit z)) =
      zornStateToFockColimit
        (zornThreeModeMajoranaState (zornThreeModeMajoranaState z)) := by
          rw [zorn_mass_intertwines_fock_colimit,
            zorn_mass_intertwines_fock_colimit]
    _ = zornStateToFockColimit ((3 : ℝ) • z) := by rw [hstate]
    _ = (3 : ℝ) • zornStateToFockColimit z := map_smul _ _ _

/-- The native three-color Cl(5,5) mass retains its quadratic value in the
actual UHF colimit, agreeing with the finite CAR-sector mass theorem. -/
theorem nativeThreeColorMajorana_square_at_UHF_colimit :
    ofStage 5 (cl55ToStage5 nativeThreeColorModeMajorana) *
        ofStage 5 (cl55ToStage5 nativeThreeColorModeMajorana) =
      (3 : ℝ) • (1 : Limit) := by
  have hmass := nativeColor_and_complement_mass_squares.1
  have hmap := congrArg ((ofStage 5).comp cl55ToStage5) hmass
  have hscalar : ofStage 5 (cl55ToStage5 ((3 : ℝ) • (1 : Cl55))) =
      (3 : ℝ) • (1 : Limit) := by
    rw [Algebra.smul_def', Algebra.smul_def']
    change ofStage 5 (cl55ToStage5 (algebraMap ℝ Cl55 3 * 1)) =
      realAlgebraMap 3 * 1
    rw [map_mul, map_one]
    have hcomm : cl55ToStage5 (algebraMap ℝ Cl55 3) =
        algebraMap ℝ (Stage 5) 3 := by
      rw [cl55ToStage5_eq_exteriorCl55StageEquiv]
      change exteriorCl55StageEquiv (algebraMap ℝ Cl55 3) = _
      exact exteriorCl55StageEquiv.commutes 3
    rw [hcomm, realAlgebraMap_stage 5 3]
    simp
  have hmap' :
      ofStage 5 (cl55ToStage5 nativeThreeColorModeMajorana) *
          ofStage 5 (cl55ToStage5 nativeThreeColorModeMajorana) =
        ofStage 5 (cl55ToStage5 ((3 : ℝ) • (1 : Cl55))) := by
    simpa only [RingHom.comp_apply, map_mul] using hmap
  exact hmap'.trans hscalar

/-- Evaluation of the existing cyclotomic-six operator polynomial on the
transported three-color mass square in the UHF colimit. -/
theorem nativeThreeColorMajorana_cyclotomicSix_at_UHF_colimit :
    InfoGeometry.OperatorAlgebra.PeirceSpine.cyclotomicSix
        (ofStage 5 (cl55ToStage5 nativeThreeColorModeMajorana) *
          ofStage 5 (cl55ToStage5 nativeThreeColorModeMajorana)) =
      (7 : ℝ) • (1 : Limit) := by
  rw [nativeThreeColorMajorana_square_at_UHF_colimit]
  simp only [InfoGeometry.OperatorAlgebra.PeirceSpine.cyclotomicSix,
    Algebra.smul_def', mul_one]
  have hreal : (3 : ℝ) * 3 - 3 + 1 = 7 := by norm_num
  have hmap := congrArg (algebraMap ℝ Limit) hreal
  simpa only [map_mul, map_sub, map_add, map_one] using hmap

/-- The first-three-mode CAR commutator is still nonzero after the faithful
Cl(5,5) spinor representation, passage to the 32-by-32 matrix stage, and the
UHF colimit injection. Thus colimit transport does not erase the interaction
that the finite split-octonion carrier detects. -/
theorem first_three_mode_CAR_commutator_survives_UHF_colimit (i : Fin 3) :
    ofStage 5 (cl55ToStage5
      (creation55 (Fin.castAdd 2 i) * annihilation55 (Fin.castAdd 2 i) -
        annihilation55 (Fin.castAdd 2 i) * creation55 (Fin.castAdd 2 i))) ≠ 0 := by
  have hsource := cl55_creation_annihilation_do_not_commute i
  have hsource' :
      creation55 (Fin.castAdd 2 i) * annihilation55 (Fin.castAdd 2 i) -
        annihilation55 (Fin.castAdd 2 i) * creation55 (Fin.castAdd 2 i) ≠ 0 := by
    intro hz
    exact hsource (sub_eq_zero.mp hz)
  intro hzero
  have hzero' :
      ofStage 5 (cl55ToStage5
        (creation55 (Fin.castAdd 2 i) * annihilation55 (Fin.castAdd 2 i) -
          annihilation55 (Fin.castAdd 2 i) * creation55 (Fin.castAdd 2 i))) =
        ofStage 5 (cl55ToStage5 0) := by
    simpa using hzero
  have hpre := (ofStage_injective 5) hzero'
  have hsourceZero := cl55ToStage5_injective hpre
  exact hsource' hsourceZero

/-- The complete five-mode mixed CAR relation is preserved by the faithful
Cl(5,5)-to-matrix-stage map and the UHF colimit map, including the off-diagonal
zero relations. The following theorem restricts it to the three color modes. -/
theorem cl55_CAR_anticommutator_in_UHF_colimit (i j : Fin 5) :
    ofStage 5 (cl55ToStage5 (annihilation55 i)) *
        ofStage 5 (cl55ToStage5 (creation55 j)) +
      ofStage 5 (cl55ToStage5 (creation55 j)) *
        ofStage 5 (cl55ToStage5 (annihilation55 i)) =
      if i = j then 1 else 0 := by
  let f : Cl55 →+* Limit := (ofStage 5).comp cl55ToStage5
  have h := congrArg f (annihilation55_creation55_anticommutator_eq i j)
  have hmap : f (if i = j then 1 else 0) = if i = j then 1 else 0 := by
    by_cases hij : i = j <;> simp [hij]
  change f (annihilation55 i) * f (creation55 j) +
      f (creation55 j) * f (annihilation55 i) = _
  rw [← map_mul, ← map_mul, ← map_add, h, hmap]

/- The first-three-mode theorem below is the color-sector restriction of the
full five-mode Cl(5,5) CAR table just transported to the actual colimit. -/
theorem first_three_mode_CAR_anticommutator_in_UHF_colimit (i j : Fin 3) :
    ofStage 5 (cl55ToStage5 (annihilation55 (Fin.castAdd 2 i))) *
        ofStage 5 (cl55ToStage5 (creation55 (Fin.castAdd 2 j))) +
      ofStage 5 (cl55ToStage5 (creation55 (Fin.castAdd 2 j))) *
        ofStage 5 (cl55ToStage5 (annihilation55 (Fin.castAdd 2 i))) =
      if i = j then 1 else 0 := by
  let f : Cl55 →+* Limit := (ofStage 5).comp cl55ToStage5
  have h := congrArg f
    (annihilation55_creation55_anticommutator_eq
      (Fin.castAdd 2 i) (Fin.castAdd 2 j))
  have hindex : Fin.castAdd 2 i = Fin.castAdd 2 j ↔ i = j := by
    constructor
    · intro h
      exact Fin.castAdd_injective 3 2 h
    · rintro rfl
      rfl
  have hmap : f (if Fin.castAdd 2 i = Fin.castAdd 2 j then 1 else 0) =
      if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      simp
    · have hne : Fin.castAdd 2 i ≠ Fin.castAdd 2 j := fun heq =>
        hij (Fin.castAdd_injective 3 2 heq)
      simp [hij, hne]
  change f (annihilation55 (Fin.castAdd 2 i)) *
      f (creation55 (Fin.castAdd 2 j)) +
    f (creation55 (Fin.castAdd 2 j)) *
      f (annihilation55 (Fin.castAdd 2 i)) = _
  rw [← map_mul, ← map_mul, ← map_add, h, hmap]

/-- The CAR-created massive BdG commutator defect survives in the fixed-colour
operator-Zorn realization at the UHF limit. The nonzero result is obtained
from the off-diagonal matrix entry and injectivity of both existing carrier
maps. -/
theorem first_three_mode_BdG_anomaly_is_nonzero_in_Zorn_colimit (k : Fin 3) (i : Fin 3) :
    fixedColourEmbedding k
      (InfoGeometry.Physics.massiveBdGCommutatorAnomaly
        (ofStage 5 (cl55ToStage5 (creation55 (Fin.castAdd 2 i))))
        (ofStage 5 (cl55ToStage5 (annihilation55 (Fin.castAdd 2 i))))) ≠ 0 := by
  intro hz
  have hmatrix :
      InfoGeometry.Physics.massiveBdGCommutatorAnomaly
        (ofStage 5 (cl55ToStage5 (creation55 (Fin.castAdd 2 i))))
        (ofStage 5 (cl55ToStage5 (annihilation55 (Fin.castAdd 2 i)))) = 0 :=
    fixedColourEmbedding_injective k (by
      calc
        fixedColourEmbedding k
            (InfoGeometry.Physics.massiveBdGCommutatorAnomaly
              (ofStage 5 (cl55ToStage5 (creation55 (Fin.castAdd 2 i))))
              (ofStage 5 (cl55ToStage5 (annihilation55 (Fin.castAdd 2 i))))) =
            (0 : OperatorZornMatrix Limit) := hz
        _ = fixedColourEmbedding k (0 : FixedColourCore Limit) :=
          (fixedColourEmbedding_zero k).symm)
  have hentry := congrArg (fun M : FixedColourCore Limit => M 0 1) hmatrix
  have hcomm :
      ofStage 5 (cl55ToStage5 (creation55 (Fin.castAdd 2 i))) *
        ofStage 5 (cl55ToStage5 (annihilation55 (Fin.castAdd 2 i))) -
      ofStage 5 (cl55ToStage5 (annihilation55 (Fin.castAdd 2 i))) *
        ofStage 5 (cl55ToStage5 (creation55 (Fin.castAdd 2 i))) = 0 := by
    simpa [InfoGeometry.Physics.massiveBdGCommutatorAnomaly] using hentry
  have hsource := first_three_mode_CAR_commutator_survives_UHF_colimit i
  apply hsource
  simpa only [map_sub, map_mul] using hcomm

/-- At the UHF limit the nonzero first-three-mode CAR anomaly is odd under
Andreev reflection, so the particle contribution plus the reflected hole
contribution vanishes in the existing fixed-colour Zorn product. -/
theorem first_three_mode_BdG_anomaly_cancels_under_Andreev_in_Zorn_colimit
    (k : Fin 3) (i : Fin 3) :
    fixedColourEmbedding k
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly
          (ofStage 5 (cl55ToStage5 (creation55 (Fin.castAdd 2 i))))
          (ofStage 5 (cl55ToStage5 (annihilation55 (Fin.castAdd 2 i))))) +
      operatorZornMul
        (operatorZornMul
          (fixedColourEmbedding k InfoGeometry.Physics.andreevSwap)
          (fixedColourEmbedding k
            (InfoGeometry.Physics.massiveBdGCommutatorAnomaly
              (ofStage 5 (cl55ToStage5 (creation55 (Fin.castAdd 2 i))))
              (ofStage 5 (cl55ToStage5 (annihilation55 (Fin.castAdd 2 i)))))))
        (fixedColourEmbedding k InfoGeometry.Physics.andreevSwap) = 0 := by
  exact massiveBdG_andreev_anomaly_cancels_in_fixedColour_Zorn k
    (ofStage 5 (cl55ToStage5 (creation55 (Fin.castAdd 2 i))))
    (ofStage 5 (cl55ToStage5 (annihilation55 (Fin.castAdd 2 i))))

/-- The actual mass-coupled BdG operator built from a first-three-mode CAR
pair at the UHF limit has a nonzero off-diagonal interaction in its square.
Adding the Andreev-reflected square cancels that interaction and leaves the
ordered particle/hole mass terms on the diagonal. -/
theorem first_three_mode_colimit_mass_square_interaction_and_Andreev_cancellation
    (i : Fin 3) :
    let D : Limit :=
      ofStage 5 (cl55ToStage5 (creation55 (Fin.castAdd 2 i)))
    let M : Limit :=
      ofStage 5 (cl55ToStage5 (annihilation55 (Fin.castAdd 2 i)))
    let H := InfoGeometry.Physics.massiveBdGHamiltonian D M
    (H * H) 0 1 ≠ 0 ∧
    H * H + InfoGeometry.Physics.andreevSwap * (H * H) *
        InfoGeometry.Physics.andreevSwap =
      !![D * D + M * M + (M * M + D * D), 0;
         0, M * M + D * D + (D * D + M * M)] := by
  let D : Limit :=
    ofStage 5 (cl55ToStage5 (creation55 (Fin.castAdd 2 i)))
  let M : Limit :=
    ofStage 5 (cl55ToStage5 (annihilation55 (Fin.castAdd 2 i)))
  change
    ((InfoGeometry.Physics.massiveBdGHamiltonian D M) *
        (InfoGeometry.Physics.massiveBdGHamiltonian D M)) 0 1 ≠ 0 ∧
      InfoGeometry.Physics.massiveBdGHamiltonian D M *
          InfoGeometry.Physics.massiveBdGHamiltonian D M +
        InfoGeometry.Physics.andreevSwap *
          (InfoGeometry.Physics.massiveBdGHamiltonian D M *
            InfoGeometry.Physics.massiveBdGHamiltonian D M) *
          InfoGeometry.Physics.andreevSwap =
        !![D * D + M * M + (M * M + D * D), 0;
          0, M * M + D * D + (D * D + M * M)]
  constructor
  · have hentry := congrArg
      (fun X : InfoGeometry.Physics.BdGBlock Limit => X 0 1)
      (InfoGeometry.Physics.massiveBdGHamiltonian_sq_with_commutator D M)
    have hcomm : D * M - M * D =
        ofStage 5 (cl55ToStage5
          (creation55 (Fin.castAdd 2 i) * annihilation55 (Fin.castAdd 2 i) -
            annihilation55 (Fin.castAdd 2 i) * creation55 (Fin.castAdd 2 i))) := by
      calc
        D * M - M * D =
            ofStage 5 (cl55ToStage5 (creation55 (Fin.castAdd 2 i)) *
              cl55ToStage5 (annihilation55 (Fin.castAdd 2 i)) -
              cl55ToStage5 (annihilation55 (Fin.castAdd 2 i)) *
                cl55ToStage5 (creation55 (Fin.castAdd 2 i))) := by
          simp [D, M]
        _ = ofStage 5 (cl55ToStage5
            (creation55 (Fin.castAdd 2 i) * annihilation55 (Fin.castAdd 2 i) -
              annihilation55 (Fin.castAdd 2 i) * creation55 (Fin.castAdd 2 i))) := by
          congr 1
          simp only [map_sub, map_mul]
    rw [hentry]
    rw [hcomm]
    exact first_three_mode_CAR_commutator_survives_UHF_colimit i
  · exact InfoGeometry.Physics.massiveBdGHamiltonian_andreev_anomaly_cancellation _ _

end InfoGeometry.Canonical.FureySplitOctonionColimitBridge

end
