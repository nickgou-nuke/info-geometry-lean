/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.Cl55PeirceSuperderivationBridge
import InfoGeometry.OperatorAlgebra.PeirceBdGFiveGradeBridge
import InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
import InfoGeometry.OperatorAlgebra.Cl55ChiralSuperchargeBridge
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentationAdditivityWave17
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentationLinearityWave16
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentationMul
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentationUnit
import InfoGeometry.Clifford.Cl55Q55NativeSplitBridge

/-!
# Cl(5,5) CAR interaction as a BdG five-grade anomaly

This bridge specializes the existing operator-valued BdG interaction to a
native creation/annihilation CAR pair. CAR itself proves that the two
coefficients do not commute, so the existing chiral five-grade theorem yields
a nonzero nonzero-grade component without an additional noncommutation input.
The existing Andreev theorem then cancels the anomaly against its hole-reflected
copy.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.Cl55CARBdGInteractionBridge

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.OperatorAlgebra.Cl55PeirceSuperderivationBridge
open InfoGeometry.OperatorAlgebra.PeirceBdGFiveGradeBridge
open InfoGeometry.Core.TripotentAdjoint
open InfoGeometry.Physics
open InfoGeometry.Physics.Algebra
open InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
open InfoGeometry.Clifford.Cl55VacuumIdealSpinorBridge
open InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
open InfoGeometry.Clifford.Cl55NeutralFockFaithfulness
open InfoGeometry.OperatorAlgebra.Cl55ChiralSuperchargeBridge
open InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative
open InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

/-- A creation/annihilation CAR pair cannot commute: if it did, multiplying
the CAR equation on the left by the square-zero creator would force the creator
to vanish, contradicting the unit CAR relation. -/
theorem car_creation_annihilation_do_not_commute (i : Fin 5) :
    creation55 i * annihilation55 i ≠ annihilation55 i * creation55 i := by
  let c := creation55 i
  let a := annihilation55 i
  have hc : c * c = 0 := creation55_sq i
  have hcar : a * c + c * a = 1 := annihilation55_creation55_anticommutator i
  intro hcomm
  have htwice : c * a + c * a = 1 := by
    calc
      c * a + c * a = a * c + c * a := by rw [hcomm]
      _ = 1 := hcar
  have hcaZero : c * (c * a) = 0 := by
    calc
      c * (c * a) = (c * c) * a := by rw [← mul_assoc]
      _ = 0 := by rw [hc, zero_mul]
  have hcreatorZero : c = 0 := by
    have hmul := congrArg (fun z : Cl55 => c * z) htwice
    rw [mul_add, hcaZero, zero_add, mul_one] at hmul
    simpa using hmul.symm
  rw [hcreatorZero] at hcar
  simp at hcar

/-- For each native Cl(5,5) CAR mode, using creation as the kinetic slot and
annihilation as the operator-valued interaction slot produces a nonzero
component in a nonzero grade of the canonical BdG chiral five-grading. -/
theorem car_mode_generates_bdg_nonzero_five_grade (i : Fin 5) :
    ∃ k : InfoGeometry.Physics.Algebra.FiveGrade, k ≠ .zero ∧
      fiveGradeProjector
        (InfoGeometry.Physics.chiralGrading (A := Cl55)) k
        (InfoGeometry.Physics.massiveBdGHamiltonian (creation55 i) (annihilation55 i) *
            InfoGeometry.Physics.massiveBdGHamiltonian (creation55 i) (annihilation55 i) -
          (InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
              (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj
                (A := Cl55))
              (!![creation55 i, 0; 0, creation55 i]) *
            InfoGeometry.OperatorAlgebra.PeirceSpine.evenGrade
              (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj
                (A := Cl55))
              (!![creation55 i, 0; 0, creation55 i]) +
            InfoGeometry.OperatorAlgebra.PeirceSpine.genV
              (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj
                (A := Cl55))
              (!![0, annihilation55 i; 0, 0])
              (!![0, 0; annihilation55 i, 0]))) ≠ 0 := by
  exact massiveBdG_chiral_commutator_generates_fiveGrade_component
    (creation55 i) (annihilation55 i)
    (car_creation_annihilation_do_not_commute i)

/-- The CAR-specialized BdG interaction anomaly is odd under particle-hole
reflection and is canceled by adding its Andreev-reflected contribution. -/
theorem car_mode_bdg_andreev_anomaly_cancels (i : Fin 5) :
    massiveBdGCommutatorAnomaly (creation55 i) (annihilation55 i) +
      andreevSwap * massiveBdGCommutatorAnomaly (creation55 i) (annihilation55 i) *
        andreevSwap = 0 := by
  rw [← InfoGeometry.OperatorAlgebra.PeirceBdGOperatorBridge.massiveBdG_peirce_commutator_eq_andreev_anomaly]
  exact InfoGeometry.OperatorAlgebra.PeirceBdGOperatorBridge.andreev_reflected_peirce_anomaly_cancels
    (creation55 i) (annihilation55 i)

/-! ### Fock carrier transport

The preceding results live in the native Cl(5,5) algebra.  The existing
vacuum-ideal owner represents that algebra faithfully on the five-mode
exterior spinor.  These declarations transport the actual CAR pair and its
BdG anomaly to that endomorphism carrier; no second Fock model is introduced.
-/

/-- The exterior-Fock representation of the native Cl(5,5) carrier is
faithful: equality of represented operators reflects equality of Clifford
operators. -/
theorem cl55SpinorRep_injective : Function.Injective cl55SpinorRep := by
  intro x y h
  apply neutralCliffordAlgEquiv.symm.injective
  exact neutralCliffordRep_injective h

/-- In the repository's neutral-Fock convention, annihilation acts by exterior
wedge on the spinor carrier. -/
theorem car_mode_annihilation_on_fock (i : Fin 5) :
    cl55SpinorRep (annihilation55 i) =
      InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.wedge
        (InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.basisVector i) := by
  simpa [cl55SpinorRep] using annihilation55_spinor i

/-- In the repository's neutral-Fock convention, creation acts by contraction.
The convention is fixed by the calibrated null-pair basis in the Clifford owner. -/
theorem car_mode_creation_on_fock (i : Fin 5) :
    cl55SpinorRep (creation55 i) =
      InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.contract
        (InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.dualBasisVector i) := by
  simpa [cl55SpinorRep] using creation55_spinor i

/-- The CAR mixed relation is preserved by the faithful Fock endomorphism
representation, with the Kronecker pairing represented by the identity map. -/
theorem fock_car_mixed_anticommutator (i j : Fin 5) :
    cl55SpinorRep (annihilation55 i) * cl55SpinorRep (creation55 j) +
      cl55SpinorRep (creation55 j) * cl55SpinorRep (annihilation55 i) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    have h := congrArg cl55SpinorRep
      (annihilation55_creation55_anticommutator i)
    simpa using h
  · have h := congrArg cl55SpinorRep
      (annihilation55_creation55_anticommutator_eq i j)
    simpa [hij] using h

/-- The native CAR noncommutation remains noncommutation in the faithful
exterior-Fock operator carrier. -/
theorem fock_car_creation_annihilation_do_not_commute (i : Fin 5) :
    cl55SpinorRep (creation55 i) * cl55SpinorRep (annihilation55 i) ≠
      cl55SpinorRep (annihilation55 i) * cl55SpinorRep (creation55 i) := by
  intro h
  apply car_creation_annihilation_do_not_commute i
  apply cl55SpinorRep_injective
  simpa only [map_mul] using h

/-- The native Cl(5,5) chiral-supercharge anticommutator, represented by the
actual exterior-Fock algebra hom, is the diagonal partner-Hamiltonian pair on
the two chiral sectors. This transports the Clifford SUSY block relation to
the same operator carrier as the CAR modes. -/
theorem fock_chiral_supercharge_anticommutator (i j : Fin 5) :
    Matrix.map
        (cl55QPlus i * cl55QMinus j + cl55QMinus j * cl55QPlus i)
        cl55SpinorRep =
      !![cl55SpinorRep (creation55 i * annihilation55 j), 0;
         0, cl55SpinorRep (annihilation55 j * creation55 i)] := by
  have h := congrArg
      (fun M : Cl55ChiralMatrix => Matrix.map M cl55SpinorRep)
      (cl55Q_anticomm i j)
  rw [h]
  ext r c
  fin_cases r <;> fin_cases c <;> simp [Matrix.map_apply]

/-- The BdG commutator obstruction is nonzero on Fock space, although its
particle-hole reflected contribution cancels it in the Andreev sum. -/
theorem fock_bdg_commutator_anomaly_nonzero (i : Fin 5) :
    InfoGeometry.Physics.massiveBdGCommutatorAnomaly
      (cl55SpinorRep (creation55 i)) (cl55SpinorRep (annihilation55 i)) ≠ 0 := by
  intro hzero
  apply fock_car_creation_annihilation_do_not_commute i
  have hEntry := congrArg (fun M : InfoGeometry.Physics.BdGBlock
      InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.SpinorEnd => M 0 1) hzero
  have hcomm : cl55SpinorRep (creation55 i) * cl55SpinorRep (annihilation55 i) -
      cl55SpinorRep (annihilation55 i) * cl55SpinorRep (creation55 i) = 0 := by
    simpa [InfoGeometry.Physics.massiveBdGCommutatorAnomaly] using hEntry
  exact sub_eq_zero.mp hcomm

/-- Andreev cancellation survives transport to the exterior-Fock operator
carrier.  This is the carrier compatibility theorem: the particle-hole
involution and the commutator anomaly are both transported through the same
algebra map that realizes the CAR modes as wedge and contraction operators. -/
theorem fock_bdg_andreev_anomaly_cancels (i : Fin 5) :
    InfoGeometry.Physics.andreevSwap *
        InfoGeometry.Physics.massiveBdGCommutatorAnomaly
          (cl55SpinorRep (creation55 i)) (cl55SpinorRep (annihilation55 i)) *
        InfoGeometry.Physics.andreevSwap =
      -InfoGeometry.Physics.massiveBdGCommutatorAnomaly
          (cl55SpinorRep (creation55 i)) (cl55SpinorRep (annihilation55 i)) := by
  have h := congrArg (fun M => Matrix.map M cl55SpinorRep)
    (InfoGeometry.Physics.andreev_reflect_mass_commutator_anomaly
      (creation55 i) (annihilation55 i))
  simpa [InfoGeometry.Physics.massiveBdGCommutatorAnomaly,
    InfoGeometry.Physics.andreevSwap, Matrix.map_mul] using h

/-! ### The finite CAR carrier inside the split-Clifford/Fock colimits

The stage-five split algebra is the existing `SplitCl55Alg`, and the colimit
action is already descended from the finite Chevalley actions. The next result
pushes the CAR relation through that actual stage embedding and action. -/

local notation "splitOf" => DirectLimit.Algebra.of SplitClNNAlg
  (fun m n h => splitCliffordMap m n h)

/-- The native `Cl(5,5)` action on exterior Fock descends to an algebra
representation on the existing algebraic Fock colimit. The map is the
composition of the source-owned `Cl55 ≃ SplitCl55Alg` equivalence, stage-five
inclusion, and the already-proved direct-limit Clifford action. -/
noncomputable def cl55FockInfinityRepresentation :
    Cl55 →+* Module.End ℝ FockInfinity where
  toFun x :=
    { toFun := splitCliffordFockAction (splitOf 5 (cl55ToSplitCl55 x))
      map_add' := splitCliffordFockAction_add_right
        (splitOf 5 (cl55ToSplitCl55 x))
      map_smul' := fun r ψ => splitCliffordFockAction_smul_right r
        (splitOf 5 (cl55ToSplitCl55 x)) ψ }
  map_zero' := by
    apply LinearMap.ext
    intro ψ
    change splitCliffordFockAction (splitOf 5 (cl55ToSplitCl55 0)) ψ = 0
    simp only [map_zero]
    have hz := splitCliffordFockAction_add_left
      (0 : SplitCliffordInfinity) 0 ψ
    have hzero : splitCliffordFockAction (0 : SplitCliffordInfinity) ψ = 0 := by
      have hh : splitCliffordFockAction (0 : SplitCliffordInfinity) ψ + 0 =
          splitCliffordFockAction (0 : SplitCliffordInfinity) ψ +
            splitCliffordFockAction (0 : SplitCliffordInfinity) ψ := by
        simpa using hz
      exact (add_left_cancel hh).symm
    exact hzero
  map_one' := by
    apply LinearMap.ext
    intro ψ
    change splitCliffordFockAction (splitOf 5 (cl55ToSplitCl55 1)) ψ = ψ
    have hone : splitOf 5 (1 : SplitClNNAlg 5) =
        (1 : SplitCliffordInfinity) := by
      rw [DirectLimit.one_def 5]
      rfl
    rw [map_one, hone]
    exact splitCliffordFockAction_one ψ
  map_mul' := by
    intro x y
    apply LinearMap.ext
    intro ψ
    change splitCliffordFockAction (splitOf 5 (cl55ToSplitCl55 (x * y))) ψ =
      splitCliffordFockAction (splitOf 5 (cl55ToSplitCl55 x))
        (splitCliffordFockAction (splitOf 5 (cl55ToSplitCl55 y)) ψ)
    rw [map_mul]
    have hcol : splitOf 5 (cl55ToSplitCl55 x * cl55ToSplitCl55 y) =
        splitOf 5 (cl55ToSplitCl55 x) * splitOf 5 (cl55ToSplitCl55 y) :=
      map_mul (splitOf 5) _ _
    rw [hcol, splitCliffordFockAction_mul]
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro ψ
    change splitCliffordFockAction (splitOf 5 (cl55ToSplitCl55 (x + y))) ψ =
      splitCliffordFockAction (splitOf 5 (cl55ToSplitCl55 x)) ψ +
        splitCliffordFockAction (splitOf 5 (cl55ToSplitCl55 y)) ψ
    rw [map_add]
    have hcol : splitOf 5 (cl55ToSplitCl55 x + cl55ToSplitCl55 y) =
        splitOf 5 (cl55ToSplitCl55 x) + splitOf 5 (cl55ToSplitCl55 y) :=
      map_add (splitOf 5) _ _
    rw [hcol, splitCliffordFockAction_add_left]

/-- The algebra representation on the Fock colimit restricts on the stage-five
image to the original finite Chevalley action. This is the carrier
intertwining law behind transporting finite `Cl(5,5)` operator identities to
the common Fock colimit; it identifies the action on each finite-stage
representative, rather than merely asserting that the two carriers are
similar. -/
theorem cl55FockInfinityRepresentation_on_stage (x : Cl55) (ψ : FockStage 5) :
    cl55FockInfinityRepresentation x (fockToInfinity 5 ψ) =
      fockToInfinity 5 (towerSpinorRep 5 (cl55ToSplitCl55 x) ψ) := by
  change splitCliffordFockAction
      (splitOf 5 (cl55ToSplitCl55 x)) (fockToInfinity 5 ψ) =
    fockToInfinity 5 (towerSpinorRep 5 (cl55ToSplitCl55 x) ψ)
  exact splitCliffordFockAction_of 5 (cl55ToSplitCl55 x) ψ

/-- The full five-mode CAR relation holds as an identity of operators on the
Fock direct limit, rather than only after evaluation on one finite-stage
representative. -/
theorem colimit_fock_car_anticommutator (i : Fin 5) :
    cl55FockInfinityRepresentation (annihilation55 i) *
        cl55FockInfinityRepresentation (creation55 i) +
      cl55FockInfinityRepresentation (creation55 i) *
        cl55FockInfinityRepresentation (annihilation55 i) = 1 := by
  have h := congrArg cl55FockInfinityRepresentation
    (annihilation55_creation55_anticommutator i)
  simpa only [map_add, map_mul, map_one] using h

/-- The chiral Cl(5,5) supercharge anticommutator is transported to the
endomorphism algebra of the Fock colimit, with its two partner operators on
the diagonal chiral sectors. -/
theorem colimit_fock_chiral_supercharge_anticommutator (i j : Fin 5) :
    Matrix.map
        (cl55QPlus i * cl55QMinus j + cl55QMinus j * cl55QPlus i)
        cl55FockInfinityRepresentation =
      !![cl55FockInfinityRepresentation (creation55 i * annihilation55 j), 0;
         0, cl55FockInfinityRepresentation (annihilation55 j * creation55 i)] := by
  have h := congrArg
    (fun M : Cl55ChiralMatrix => Matrix.map M cl55FockInfinityRepresentation)
    (cl55Q_anticomm i j)
  rw [h]
  ext r c
  fin_cases r <;> fin_cases c <;> simp [Matrix.map_apply]

/-- Andreev reflection of the BdG anomaly is carried through the actual
Clifford-to-Fock-colimit operator map. This states the transported matrix
identity before simplifying it entrywise, so the source and target carriers
remain explicit. -/
theorem colimit_fock_bdg_andreev_reflection (i : Fin 5) :
    Matrix.map
        (andreevSwap *
          massiveBdGCommutatorAnomaly (creation55 i) (annihilation55 i) *
          andreevSwap)
        cl55FockInfinityRepresentation =
      Matrix.map
        (-massiveBdGCommutatorAnomaly (creation55 i) (annihilation55 i))
        cl55FockInfinityRepresentation := by
  exact congrArg
    (fun M => Matrix.map M cl55FockInfinityRepresentation)
    (andreev_reflect_mass_commutator_anomaly
      (creation55 i) (annihilation55 i))

/-- The five-mode CAR anticommutator acts as the identity on the stage-five
Fock carrier after transport through `Cl55 ≃ₐ SplitCl55Alg` and inclusion into
the algebraic Fock colimit. This is the CAR relation in the common colimit
carrier, derived from the native Clifford CAR equation. -/
theorem colimit_fock_car_anticommutator_on_stage (i : Fin 5) (ψ : FockStage 5) :
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) 5
          (cl55ToSplitCl55 (annihilation55 i)))
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m n h => splitCliffordMap m n h) 5
            (cl55ToSplitCl55 (creation55 i)))
          (fockToInfinity 5 ψ)) +
      splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) 5
          (cl55ToSplitCl55 (creation55 i)))
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m n h => splitCliffordMap m n h) 5
            (cl55ToSplitCl55 (annihilation55 i)))
          (fockToInfinity 5 ψ)) = fockToInfinity 5 ψ := by
  rw [splitCliffordFockAction_of, splitCliffordFockAction_of,
    splitCliffordFockAction_of, splitCliffordFockAction_of]
  have hcar := congrArg
    (fun x : Cl55 => towerSpinorRep 5 (cl55ToSplitCl55 x) ψ)
    (annihilation55_creation55_anticommutator i)
  have hmap :
      towerSpinorRep 5 (cl55ToSplitCl55 (annihilation55 i))
          (towerSpinorRep 5 (cl55ToSplitCl55 (creation55 i)) ψ) +
        towerSpinorRep 5 (cl55ToSplitCl55 (creation55 i))
          (towerSpinorRep 5 (cl55ToSplitCl55 (annihilation55 i)) ψ) = ψ := by
    simpa [map_add, map_mul, towerSpinorRep] using hcar
  let u := towerSpinorRep 5 (cl55ToSplitCl55 (annihilation55 i))
    (towerSpinorRep 5 (cl55ToSplitCl55 (creation55 i)) ψ)
  let v := towerSpinorRep 5 (cl55ToSplitCl55 (creation55 i))
    (towerSpinorRep 5 (cl55ToSplitCl55 (annihilation55 i)) ψ)
  have hadd : fockToInfinity 5 (u + v) =
      fockToInfinity 5 u + fockToInfinity 5 v := by
    exact (DirectLimit.Module.of ℝ ℕ FockStage
      (fun m n h => fockStageMap m n h) 5).map_add u v
  change fockToInfinity 5 u + fockToInfinity 5 v = fockToInfinity 5 ψ
  calc
    fockToInfinity 5 u + fockToInfinity 5 v = fockToInfinity 5 (u + v) := hadd.symm
    _ = fockToInfinity 5 ψ := congrArg (fockToInfinity 5) hmap

end InfoGeometry.OperatorAlgebra.Cl55CARBdGInteractionBridge

end
