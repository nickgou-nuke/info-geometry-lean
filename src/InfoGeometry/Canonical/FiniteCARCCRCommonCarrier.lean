/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CliffordFockSuperTwistorBridge
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction
import InfoGeometry.OperatorAlgebra.Cl55ChiralSuperchargeBridge
import InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
import InfoGeometry.Physics.NuclearTwoModeCARFiveGrade
import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.OperatorAlgebra.PeirceBdGFiveGradeBridge
import InfoGeometry.OperatorAlgebra.PeirceBdGOperatorBridge
import InfoGeometry.Algebra.SteinbergBraidDefectSpine
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Finite-mode CAR–CCR common operator carrier

The mode set and Clifford stage are finite, while the polynomial CCR factor is
infinite-dimensional. The polynomial CCR and exterior-Fock CAR act on distinct
tensor factors of one supertwistor module. This file records their simultaneous
operator relations at each finite mode stage and their cross-factor
commutation. It does not assert an exact CCR on a finite-dimensional carrier;
the separate finite cutoff owner records its nonzero boundary defect.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteCARCCRCommonCarrier

open InfoGeometry.Twistor.RealSupertwistor
open InfoGeometry.Twistor.RealPolynomialCCR
open InfoGeometry.Canonical.CliffordFockSuperTwistorBridge
open InfoGeometry.Canonical.CanonicalNormalOrdering
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.OperatorAlgebra.Cl55ChiralSuperchargeBridge
open InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
attribute [local instance] InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockNormedAddCommGroup
  InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockInnerProductSpace

/-- Bosonic creation on the polynomial factor of the finite supertwistor
carrier. -/
def bosonCreate (n : ℕ) (i : Fin n) : SuperOperator (Fin n) (Fin n → ℝ) :=
  bosonLift (Fin n) (Fin n → ℝ) (create i)

/-- Bosonic annihilation on the polynomial factor of the finite supertwistor
carrier. -/
def bosonAnnihilate (n : ℕ) (i : Fin n) : SuperOperator (Fin n) (Fin n → ℝ) :=
  bosonLift (Fin n) (Fin n → ℝ) (annihilate i)

/-- Fermionic creation represented through the finite Clifford stage. -/
def fermionCreate (n : ℕ) (i : Fin n) : SuperOperator (Fin n) (Fin n → ℝ) :=
  InfoGeometry.Twistor.RealSupertwistor.fermionCreate
    (Fin n) (Fin n → ℝ) (Pi.single i 1)

/-- The same exterior creation action represented by the finite Clifford
stage equivalence. -/
def cliffordFermionCreate (n : ℕ) (i : Fin n) : SuperOperator (Fin n) (Fin n → ℝ) :=
  stageCreation n i

/-- Normal-ordered integer-mode fermion current bilinear acting on the Fock
factor of the same polynomial–Fock carrier. -/
noncomputable def integerFockCurrent (n : ℕ) (a b : ℤ) :
    SuperOperator (Fin n) (IntModeSpace ℝ) :=
  fermionLift (Fin n) (IntModeSpace ℝ)
    (normalMatrixUnit (R := ℝ) (M := IntModeSpace ℝ) (intModeBasis ℝ) a b)

/-- Associative commutator of endomorphisms on the common carrier. -/
def operatorComm {E : Type*} [AddCommGroup E] [Module ℝ E]
    (X Y : Module.End ℝ E) : Module.End ℝ E := X * Y - Y * X

/-- The genuine normal-ordered integer-mode matrix-unit commutator, including
its finite polarization Schwinger term, transports to the common tensor
carrier. -/
theorem integerFockCurrent_wick_commutator (n : ℕ) (a b c d : ℤ) :
    operatorComm (integerFockCurrent n a b) (integerFockCurrent n c d) =
      fermionLift (Fin n) (IntModeSpace ℝ)
        ((if b = c then
            normalMatrixUnit (R := ℝ) (M := IntModeSpace ℝ) (intModeBasis ℝ) a d
          else 0) -
         (if a = d then
            normalMatrixUnit (R := ℝ) (M := IntModeSpace ℝ) (intModeBasis ℝ) c b
          else 0) +
         (if b = c ∧ a = d then
            (occ a - occ b) • (1 : EndFock (R := ℝ) (M := IntModeSpace ℝ))
          else 0)) := by
  have h := congrArg (fermionLift (Fin n) (IntModeSpace ℝ))
    (normalOrdered_matrixUnit_commutator_from_directSumExteriorFock ℝ a b c d)
  simpa [operatorComm, integerFockCurrent,
    InfoGeometry.Canonical.BosonizationConstructiveCurrent.comm] using h

/-- Bosonic creation on the common carrier whose fermionic factor is the full
integer-mode exterior Fock space. -/
def integerCarrierBosonCreate (n : ℕ) (i : Fin n) :
    SuperOperator (Fin n) (IntModeSpace ℝ) :=
  bosonLift (Fin n) (IntModeSpace ℝ) (create i)

/-- Bosonic annihilation on the common integer-mode Fock carrier. -/
def integerCarrierBosonAnnihilate (n : ℕ) (i : Fin n) :
    SuperOperator (Fin n) (IntModeSpace ℝ) :=
  bosonLift (Fin n) (IntModeSpace ℝ) (annihilate i)

/-- The finite polynomial CCR and the integer-mode normal-ordered CAR current
act on one operator module and commute across its tensor factors. -/
theorem integer_current_commutes_with_bosonic_CCR (n : ℕ) (i : Fin n)
    (a b : ℤ) :
    integerCarrierBosonAnnihilate n i * integerCarrierBosonCreate n i -
        integerCarrierBosonCreate n i * integerCarrierBosonAnnihilate n i =
      (1 : SuperOperator (Fin n) (IntModeSpace ℝ)) ∧
    integerCarrierBosonCreate n i * integerFockCurrent n a b =
      integerFockCurrent n a b * integerCarrierBosonCreate n i ∧
    integerCarrierBosonAnnihilate n i * integerFockCurrent n a b =
      integerFockCurrent n a b * integerCarrierBosonAnnihilate n i := by
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (bosonLift (Fin n) (IntModeSpace ℝ))
      (annihilate_create_commutator i i)
    simpa [integerCarrierBosonAnnihilate, integerCarrierBosonCreate] using h
  · exact boson_fermion_commute (ι := Fin n) (E := IntModeSpace ℝ)
      (create i)
      (normalMatrixUnit (R := ℝ) (M := IntModeSpace ℝ)
        (intModeBasis ℝ) a b)
  · exact boson_fermion_commute (ι := Fin n) (E := IntModeSpace ℝ)
      (annihilate i)
      (normalMatrixUnit (R := ℝ) (M := IntModeSpace ℝ)
        (intModeBasis ℝ) a b)

/-- The native `Cl(5,5)` CAR representation is placed on the same five-mode
polynomial–Fock carrier as the polynomial CCR. -/
def cl55CommonCarrierRep : Cl55 →ₐ[ℝ]
    SuperOperator (Fin 5) (Fin 5 → ℝ) :=
  (fermionLift (Fin 5) (Fin 5 → ℝ)).comp cl55SpinorRep

/-- The represented `Cl(5,5)` annihilation and creation operators retain their
mixed CAR relation on the common polynomial–Fock carrier. -/
theorem commonCarrier_cl55_CAR (i j : Fin 5) :
    cl55CommonCarrierRep (annihilation55 i) * cl55CommonCarrierRep (creation55 j) +
      cl55CommonCarrierRep (creation55 j) * cl55CommonCarrierRep (annihilation55 i) =
        if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    have h := congrArg cl55CommonCarrierRep (annihilation55_creation55_anticommutator i)
    simpa [cl55CommonCarrierRep] using h
  · have h := congrArg cl55CommonCarrierRep
      (annihilation55_creation55_anticommutator_eq i j)
    simpa [cl55CommonCarrierRep, hij] using h

/-- Bosonic polynomial creation commutes with every represented `Cl(5,5)`
operator because both are lifted to the same tensor-product endomorphism ring. -/
theorem commonCarrier_boson_cl55_commute (b : Operator (Fin 5)) (x : Cl55) :
    bosonLift (Fin 5) (Fin 5 → ℝ) b * cl55CommonCarrierRep x =
      cl55CommonCarrierRep x * bosonLift (Fin 5) (Fin 5 → ℝ) b := by
  exact boson_fermion_commute (ι := Fin 5) (E := Fin 5 → ℝ) b
    (cl55SpinorRep x)

/-- The five-dimensional polynomial CCR is orthogonal to the represented
`Cl(5,5)` CAR sector on the common operator carrier. -/
theorem commonCarrier_CCR_CAR_sectors_commute (i j : Fin 5) :
    bosonLift (Fin 5) (Fin 5 → ℝ) (create i) * cl55CommonCarrierRep (creation55 j) =
      cl55CommonCarrierRep (creation55 j) * bosonLift (Fin 5) (Fin 5 → ℝ) (create i) ∧
    bosonLift (Fin 5) (Fin 5 → ℝ) (annihilate i) * cl55CommonCarrierRep (annihilation55 j) =
      cl55CommonCarrierRep (annihilation55 j) * bosonLift (Fin 5) (Fin 5 → ℝ) (annihilate i) := by
  exact ⟨commonCarrier_boson_cl55_commute (create i) (creation55 j),
    commonCarrier_boson_cl55_commute (annihilate i) (annihilation55 j)⟩

/-- Positive chiral supercharge block with entries acting on the common
polynomial–Fock carrier. -/
def commonCarrierQPlus (i : Fin 5) :
    Matrix (Fin 2) (Fin 2) (SuperOperator (Fin 5) (Fin 5 → ℝ)) :=
  !![0, cl55CommonCarrierRep (creation55 i); 0, 0]

/-- Negative chiral supercharge block with entries acting on the common
polynomial–Fock carrier. -/
def commonCarrierQMinus (i : Fin 5) :
    Matrix (Fin 2) (Fin 2) (SuperOperator (Fin 5) (Fin 5 → ℝ)) :=
  !![0, 0; cl55CommonCarrierRep (annihilation55 i), 0]

/-- Upper matrix unit in the common-carrier block algebra. -/
def commonCarrierBlockE01 :
    Matrix (Fin 2) (Fin 2) (SuperOperator (Fin 5) (Fin 5 → ℝ)) :=
  !![0, 1; 0, 0]

/-- Lower matrix unit in the common-carrier block algebra. -/
def commonCarrierBlockE10 :
    Matrix (Fin 2) (Fin 2) (SuperOperator (Fin 5) (Fin 5 → ℝ)) :=
  !![0, 0; 1, 0]

/-- The common-carrier block algebra is genuinely noncommutative: its two
opposite matrix units multiply to the two distinct diagonal projections. -/
theorem commonCarrierBlock_noncommutative_witness :
    commonCarrierBlockE01 * commonCarrierBlockE10 ≠
      commonCarrierBlockE10 * commonCarrierBlockE01 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2)
      (SuperOperator (Fin 5) (Fin 5 → ℝ)) => M 0 0) h
  exact (one_ne_zero :
      (1 : SuperOperator (Fin 5) (Fin 5 → ℝ)) ≠ 0) (by
        simpa [commonCarrierBlockE01, commonCarrierBlockE10,
          Matrix.mul_apply, Fin.sum_univ_two] using h00)

/-- The chiral supercharge anticommutator closes on its two represented CAR
partner operators, now as a block operator over the shared CCR carrier. -/
theorem commonCarrier_chiral_supercharge_anticommutator (i j : Fin 5) :
    commonCarrierQPlus i * commonCarrierQMinus j +
      commonCarrierQMinus j * commonCarrierQPlus i =
        !![cl55CommonCarrierRep (creation55 i * annihilation55 j), 0;
           0, cl55CommonCarrierRep (annihilation55 j * creation55 i)] := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [commonCarrierQPlus, commonCarrierQMinus, cl55CommonCarrierRep]

/-- Diagonal bosonic creation acts identically on both chiral blocks and
commutes with the represented positive supercharge. -/
theorem commonCarrier_boson_block_commutes_QPlus (i j : Fin 5) :
    !![bosonLift (Fin 5) (Fin 5 → ℝ) (create i), 0;
       0, bosonLift (Fin 5) (Fin 5 → ℝ) (create i)] * commonCarrierQPlus j =
      commonCarrierQPlus j *
        !![bosonLift (Fin 5) (Fin 5 → ℝ) (create i), 0;
           0, bosonLift (Fin 5) (Fin 5 → ℝ) (create i)] := by
  apply Matrix.ext
  intro r c
  fin_cases r <;> fin_cases c
  · simp [commonCarrierQPlus]
  · simpa [commonCarrierQPlus] using
      commonCarrier_boson_cl55_commute (create i) (creation55 j)
  · simp [commonCarrierQPlus]
  · simp [commonCarrierQPlus]

/-- Every bosonic operator on the polynomial factor, placed diagonally on the
two chiral blocks, commutes with both represented Cl(5,5) supercharges.  This
uses the existing tensor-factor commutation law, so it applies to the CCR
annihilator as well as creation and does not identify CAR with CCR. -/
theorem commonCarrier_boson_block_commutes_chiral_supercharges
    (b : Operator (Fin 5)) (j : Fin 5) :
    (!![bosonLift (Fin 5) (Fin 5 → ℝ) b, 0;
        0, bosonLift (Fin 5) (Fin 5 → ℝ) b] * commonCarrierQPlus j =
      commonCarrierQPlus j *
        !![bosonLift (Fin 5) (Fin 5 → ℝ) b, 0;
          0, bosonLift (Fin 5) (Fin 5 → ℝ) b]) ∧
    (!![bosonLift (Fin 5) (Fin 5 → ℝ) b, 0;
        0, bosonLift (Fin 5) (Fin 5 → ℝ) b] * commonCarrierQMinus j =
      commonCarrierQMinus j *
        !![bosonLift (Fin 5) (Fin 5 → ℝ) b, 0;
          0, bosonLift (Fin 5) (Fin 5 → ℝ) b]) := by
  constructor
  · apply Matrix.ext
    intro r c
    fin_cases r <;> fin_cases c
    · simp [commonCarrierQPlus]
    · simpa [commonCarrierQPlus] using
        commonCarrier_boson_cl55_commute b (creation55 j)
    · simp [commonCarrierQPlus]
    · simp [commonCarrierQPlus]
  · apply Matrix.ext
    intro r c
    fin_cases r <;> fin_cases c
    · simp [commonCarrierQMinus]
    · simp [commonCarrierQMinus]
    · simpa [commonCarrierQMinus] using
        commonCarrier_boson_cl55_commute b (annihilation55 j)
    · simp [commonCarrierQMinus]

/-- The polynomial CCR creation and annihilation operators both commute with
the complete two-chirality CAR current on the shared carrier. -/
theorem commonCarrier_CCR_generators_commute_with_CAR_current (i j : Fin 5) :
    (let bCreate :=
      !![bosonLift (Fin 5) (Fin 5 → ℝ) (create i), 0;
        0, bosonLift (Fin 5) (Fin 5 → ℝ) (create i)]
     let bAnnihilate :=
      !![bosonLift (Fin 5) (Fin 5 → ℝ) (annihilate i), 0;
        0, bosonLift (Fin 5) (Fin 5 → ℝ) (annihilate i)]
     bCreate * (commonCarrierQPlus j + commonCarrierQMinus j) =
       (commonCarrierQPlus j + commonCarrierQMinus j) * bCreate) ∧
    (let bCreate :=
      !![bosonLift (Fin 5) (Fin 5 → ℝ) (create i), 0;
        0, bosonLift (Fin 5) (Fin 5 → ℝ) (create i)]
     let bAnnihilate :=
      !![bosonLift (Fin 5) (Fin 5 → ℝ) (annihilate i), 0;
        0, bosonLift (Fin 5) (Fin 5 → ℝ) (annihilate i)]
     bAnnihilate * (commonCarrierQPlus j + commonCarrierQMinus j) =
       (commonCarrierQPlus j + commonCarrierQMinus j) * bAnnihilate) := by
  have hCreate := commonCarrier_boson_block_commutes_chiral_supercharges
    (create i) j
  have hAnnihilate := commonCarrier_boson_block_commutes_chiral_supercharges
    (annihilate i) j
  rcases hCreate with ⟨hCreatePlus, hCreateMinus⟩
  rcases hAnnihilate with ⟨hAnnihilatePlus, hAnnihilateMinus⟩
  constructor
  · dsimp
    rw [mul_add, hCreatePlus, hCreateMinus, add_mul]
  · dsimp
    rw [mul_add, hAnnihilatePlus, hAnnihilateMinus, add_mul]

/-- Bosonic creation and annihilation satisfy the real polynomial CCR on the
common tensor carrier. -/
theorem bosonAnnihilate_create_CCR (n : ℕ) (i j : Fin n) :
    bosonAnnihilate n i * bosonCreate n j - bosonCreate n j * bosonAnnihilate n i =
      (if i = j then 1 else 0 : ℝ) • (1 : SuperOperator (Fin n) (Fin n → ℝ)) := by
  have h := congrArg (bosonLift (Fin n) (Fin n → ℝ))
    (annihilate_create_commutator i j)
  simpa [bosonAnnihilate, bosonCreate] using h

/-- Fermionic creation and annihilation satisfy CAR on the same carrier. -/
theorem fermionAnnihilate_create_CAR (n : ℕ) (i j : Fin n) :
    fermionAnnihilate (Fin n) (Fin n → ℝ) (LinearMap.proj i) * fermionCreate n j +
      fermionCreate n j * fermionAnnihilate (Fin n) (Fin n → ℝ) (LinearMap.proj i) =
        (if i = j then 1 else 0 : ℝ) •
          (1 : SuperOperator (Fin n) (Fin n → ℝ)) := by
  simpa [fermionCreate] using
    InfoGeometry.Twistor.RealSupertwistor.coordinate_fermionic_CAR
      (ι := Fin n) (n := n) i j

/-- Bosonic creation and fermionic creation commute because they act on the
two tensor factors of the common carrier. -/
theorem bosonCreate_commute_fermionCreate (n : ℕ) (i j : Fin n) :
    bosonCreate n i * fermionCreate n j = fermionCreate n j * bosonCreate n i := by
  exact boson_fermion_commute (ι := Fin n) (E := Fin n → ℝ) (create i)
    (InfoGeometry.Canonical.KahlerAtiyahCartanForms.wedgeOperator (Pi.single j 1))

/-- Bosonic annihilation and fermionic creation commute on the common carrier. -/
theorem bosonAnnihilate_commute_fermionCreate (n : ℕ) (i j : Fin n) :
    bosonAnnihilate n i * fermionCreate n j = fermionCreate n j * bosonAnnihilate n i := by
  exact boson_fermion_commute (ι := Fin n) (E := Fin n → ℝ) (annihilate i)
    (InfoGeometry.Canonical.KahlerAtiyahCartanForms.wedgeOperator (Pi.single j 1))

/-- The finite Clifford-stage generators retain their CAR after transport to
the same polynomial/exterior carrier. -/
theorem cliffordFermionCreation_contraction_CAR (n : ℕ) (i : Fin n) :
    stageContraction n i * cliffordFermionCreate n i +
      cliffordFermionCreate n i * stageContraction n i =
        (1 : SuperOperator (Fin n) (Fin n → ℝ)) := by
  simpa [cliffordFermionCreate] using stageCreation_contraction_CAR n i

/-- The finite Clifford-stage creator is the same operator as exterior wedge
creation on the common supertwistor carrier. -/
theorem cliffordFermionCreate_eq_fermionCreate (n : ℕ) (i : Fin n) :
    cliffordFermionCreate n i = fermionCreate n i := by
  simp only [cliffordFermionCreate, stageCreation, cliffordStageRep,
    AlgHom.comp_apply, fermionCreate]
  change fermionLift (Fin n) (Fin n → ℝ)
    ((InfoGeometry.Clifford.FockOccupationCarrierEquiv.exteriorFockCliffordOperatorEquiv n).symm
      (InfoGeometry.Clifford.FockOccupationCarrierEquiv.exteriorFockCliffordOperatorEquiv n
        (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockExtActionCLM n i).toLinearMap)) = _
  rw [(InfoGeometry.Clifford.FockOccupationCarrierEquiv.exteriorFockCliffordOperatorEquiv n).symm_apply_apply]
  apply congrArg (fermionLift (Fin n) (Fin n → ℝ))
  apply LinearMap.ext
  intro ψ
  change InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockExtActionCLM n i ψ = _
  rw [InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockExtActionCLM_apply,
    Pi.basisFun_apply,
    InfoGeometry.Canonical.KahlerAtiyahCartanForms.wedgeOperator_apply]
  rfl

/-- The finite Clifford-stage contraction is the same operator as the
coordinate annihilator on the common supertwistor carrier. -/
theorem stageContraction_eq_fermionAnnihilate (n : ℕ) (i : Fin n) :
    stageContraction n i =
      fermionAnnihilate (Fin n) (Fin n → ℝ) (LinearMap.proj i) := by
  simp only [stageContraction, cliffordStageRep,
    AlgHom.comp_apply, fermionAnnihilate]
  change fermionLift (Fin n) (Fin n → ℝ)
    ((InfoGeometry.Clifford.FockOccupationCarrierEquiv.exteriorFockCliffordOperatorEquiv n).symm
      (InfoGeometry.Clifford.FockOccupationCarrierEquiv.exteriorFockCliffordOperatorEquiv n
        (InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockIntActionCLM n i).toLinearMap)) = _
  rw [(InfoGeometry.Clifford.FockOccupationCarrierEquiv.exteriorFockCliffordOperatorEquiv n).symm_apply_apply]
  apply congrArg (fermionLift (Fin n) (Fin n → ℝ))
  apply LinearMap.ext
  intro ψ
  change InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockIntActionCLM n i ψ = _
  rw [InfoGeometry.Clifford.ClNNNeutralChevalleyBridge.fockIntActionCLM_apply,
    InfoGeometry.Canonical.KahlerAtiyahCartanForms.contractionOperator]
  rfl

/-- The finite common-carrier theorem packages the bosonic CCR, fermionic CAR,
and cross-factor commutation without identifying their distinct brackets. -/
theorem finite_car_ccr_supercarrier (n : ℕ) (i j : Fin n) :
    (bosonAnnihilate n i * bosonCreate n j - bosonCreate n j * bosonAnnihilate n i =
      (if i = j then 1 else 0 : ℝ) • (1 : SuperOperator (Fin n) (Fin n → ℝ))) ∧
    (fermionAnnihilate (Fin n) (Fin n → ℝ) (LinearMap.proj i) * fermionCreate n j +
      fermionCreate n j * fermionAnnihilate (Fin n) (Fin n → ℝ) (LinearMap.proj i) =
        (if i = j then 1 else 0 : ℝ) •
          (1 : SuperOperator (Fin n) (Fin n → ℝ))) ∧
    bosonAnnihilate n i * fermionCreate n j = fermionCreate n j * bosonAnnihilate n i ∧
    (stageContraction n i * cliffordFermionCreate n i +
      cliffordFermionCreate n i * stageContraction n i =
        (1 : SuperOperator (Fin n) (Fin n → ℝ))) := by
  exact ⟨bosonAnnihilate_create_CCR n i j,
    fermionAnnihilate_create_CAR n i j,
    bosonAnnihilate_commute_fermionCreate n i j,
    cliffordFermionCreation_contraction_CAR n i⟩

/-! ## Finite CCR cutoff tensored with the finite CAR Fock carrier

The polynomial supercarrier above supplies exact CCR but has an infinite
polynomial factor.  Here the four-level cutoff and the existing four-state CAR
Fock module act on their algebraic tensor product, a genuinely finite
state-space carrier.  The CCR commutator retains the cutoff boundary operator. -/

open scoped TensorProduct
open InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction
open InfoGeometry.Physics.NuclearTwoModeCARFiveGrade

/-- The four-dimensional state space on which the finite CCR cutoff acts. -/
abbrev CutoffState := Fin 4 → ℂ

/-- The tensor product of the cutoff states with the four-state CAR Fock
module. -/
abbrev CutoffCARState := TensorProduct ℂ CutoffState Fock4

/-- Endomorphisms of the finite cutoff–CAR tensor carrier. -/
abbrev CutoffCAROperator := Module.End ℂ CutoffCARState

/-- Lift a cutoff matrix to the first tensor factor. -/
def cutoffCCRAction (A : TwistorOperator) : CutoffCAROperator :=
  TensorProduct.map (Matrix.toLin' A) (LinearMap.id : Fock4 →ₗ[ℂ] Fock4)

/-- Lift a finite CAR operator to the second tensor factor. -/
def cutoffCARAction (T : Op) : CutoffCAROperator :=
  TensorProduct.map (LinearMap.id : CutoffState →ₗ[ℂ] CutoffState) T

/-- The cutoff action preserves matrix multiplication. -/
theorem cutoffCCRAction_mul (A B : TwistorOperator) :
    cutoffCCRAction (A * B) = cutoffCCRAction A * cutoffCCRAction B := by
  apply TensorProduct.ext'
  intro x ψ
  simp [cutoffCCRAction]

/-- The CAR action preserves operator multiplication. -/
theorem cutoffCARAction_mul (S T : Op) :
    cutoffCARAction (S * T) = cutoffCARAction S * cutoffCARAction T := by
  apply TensorProduct.ext'
  intro x ψ
  simp [cutoffCARAction]

/-- Operators on the two finite tensor factors commute on the common state
space. -/
theorem cutoffCCRAction_commutes_cutoffCARAction
    (A : TwistorOperator) (T : Op) :
    cutoffCCRAction A * cutoffCARAction T =
      cutoffCARAction T * cutoffCCRAction A := by
  apply TensorProduct.ext'
  intro x ψ
  simp [cutoffCCRAction, cutoffCARAction]

/-- The finite tensor-carrier CCR relation is precisely the lifted boundary
commutator from the four-level cutoff owner. -/
theorem cutoffCCR_boundary_on_finite_CAR_carrier :
    cutoffCCRAction twistorCoordinate * cutoffCCRAction twistorDerivative -
      cutoffCCRAction twistorDerivative * cutoffCCRAction twistorCoordinate =
        cutoffCCRAction (FiniteTwistorCCRGeneratingFunction.commutator
          twistorCoordinate twistorDerivative) := by
  rw [← cutoffCCRAction_mul, ← cutoffCCRAction_mul]
  have hsub : ∀ A B : TwistorOperator,
      cutoffCCRAction (A - B) = cutoffCCRAction A - cutoffCCRAction B := by
    intro A B
    apply TensorProduct.ext'
    intro x ψ
    simp [cutoffCCRAction, Matrix.toLin'_apply, LinearMap.sub_apply]
    exact TensorProduct.sub_tmul (Matrix.mulVec A x) (Matrix.mulVec B x) ψ
  rw [← hsub]
  rfl

/-- A coefficient readout on the tensor carrier, used to detect a nonzero
state without identifying the tensor product with a coordinate surrogate. -/
def cutoffCARReadout : CutoffCARState →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    (LinearMap.mk₂ ℂ (fun x ψ => x 1 * ψ 0)
      (fun x y ψ => by simp [add_mul])
      (fun c x ψ => by simp [smul_eq_mul, mul_left_comm, mul_comm])
      (fun x ψ χ => by simp [mul_add])
      (fun c x ψ => by simp [smul_eq_mul, mul_assoc, mul_comm]))

/-- The finite cutoff anomaly remains nonidentity after coupling to the CAR
Fock factor.  The readout detects a level on which the boundary commutator
vanishes while the identity acts nontrivially. -/
theorem cutoffCCR_boundary_is_not_identity_on_finite_CAR_carrier :
    cutoffCCRAction (FiniteTwistorCCRGeneratingFunction.commutator
      twistorCoordinate twistorDerivative) ≠ 1 := by
  intro h
  let x : CutoffState := Pi.single 1 1
  let ψ : Fock4 := Pi.single 0 1
  have hEval := congrArg
    (fun T : CutoffCAROperator => cutoffCARReadout (T (x ⊗ₜ[ℂ] ψ))) h
  rw [FiniteTwistorCCRGeneratingFunction.finite_twistor_commutator] at hEval
  simp [cutoffCCRAction, cutoffCARReadout, x, ψ, Matrix.toLin'_apply] at hEval

/-- The exact two-mode CAR identity survives the finite tensor lift. -/
theorem cutoffCARAction_CAR_one :
    cutoffCARAction annihilationOne * cutoffCARAction creationOne +
      cutoffCARAction creationOne * cutoffCARAction annihilationOne = 1 := by
  rw [← cutoffCARAction_mul, ← cutoffCARAction_mul]
  have hadd : ∀ S T : Op,
      cutoffCARAction (S + T) = cutoffCARAction S + cutoffCARAction T := by
    intro S T
    apply TensorProduct.ext'
    intro x ψ
    simp [cutoffCARAction, TensorProduct.tmul_add]
  rw [← hadd, CAR_one]
  change TensorProduct.map (LinearMap.id : CutoffState →ₗ[ℂ] CutoffState)
    (LinearMap.id : Fock4 →ₗ[ℂ] Fock4) = LinearMap.id
  exact TensorProduct.map_id

/-! ## The finite CAR mass interaction inside the BdG block -/

/-- The first-mode CAR annihilator, acting on the CAR factor of the common
finite cutoff–CAR carrier. -/
def finiteCARKinetic : CutoffCAROperator := cutoffCARAction annihilationOne

/-- The first-mode CAR creator, acting on the CAR factor of the common finite
cutoff–CAR carrier. -/
def finiteCARMass : CutoffCAROperator := cutoffCARAction creationOne

/-- The lifted CAR relation gives the anticommutator of the kinetic and mass
operators on the unified finite carrier. -/
theorem finiteCAR_kinetic_mass_anticommutator :
    finiteCARKinetic * finiteCARMass + finiteCARMass * finiteCARKinetic = 1 := by
  rw [finiteCARKinetic, finiteCARMass, ← cutoffCARAction_mul,
    ← cutoffCARAction_mul]
  have hadd : ∀ S T : Op,
      cutoffCARAction (S + T) = cutoffCARAction S + cutoffCARAction T := by
    intro S T
    apply TensorProduct.ext'
    intro x ψ
    simp [cutoffCARAction, TensorProduct.tmul_add]
  rw [← hadd, CAR_one]
  change TensorProduct.map (LinearMap.id : CutoffState →ₗ[ℂ] CutoffState)
    (LinearMap.id : Fock4 →ₗ[ℂ] Fock4) = LinearMap.id
  exact TensorProduct.map_id

/-- The finite CAR kinetic and mass operators do not commute.  A vacuum
vector in the CAR factor and a nonzero cutoff vector detect the commutator. -/
theorem finiteCAR_kinetic_mass_commutator_ne_zero :
    finiteCARKinetic * finiteCARMass - finiteCARMass * finiteCARKinetic ≠ 0 := by
  intro hzero
  let x : CutoffState := Pi.single 1 1
  let ψ : Fock4 := ![1, 0, 0, 0]
  have hread := congrArg
    (fun T : CutoffCAROperator => cutoffCARReadout (T (x ⊗ₜ[ℂ] ψ))) hzero
  simp [finiteCARKinetic, finiteCARMass, cutoffCARAction,
    cutoffCARReadout, x, ψ, annihilationOne, creationOne,
    Module.End.mul_apply] at hread

/-- The actual first-mode CAR kinetic/mass pair has a nonzero BdG square
anomaly on the shared finite carrier. -/
theorem finiteCAR_BdG_anomaly_is_nonzero :
    InfoGeometry.Physics.massiveBdGCommutatorAnomaly
      finiteCARKinetic finiteCARMass ≠ 0 := by
  intro hz
  exact finiteCAR_kinetic_mass_commutator_ne_zero
    (sub_eq_zero.mpr
      ((InfoGeometry.Physics.massiveBdGCommutatorAnomaly_eq_zero_iff_commute
        finiteCARKinetic finiteCARMass).mp hz))

/-- Andreev reflection cancels the nonzero particle–hole interaction anomaly
for the concrete finite CAR mass pair on the common CCR–CAR carrier. -/
theorem finiteCAR_BdG_andreev_anomaly_cancellation :
    InfoGeometry.Physics.massiveBdGCommutatorAnomaly
        finiteCARKinetic finiteCARMass +
      InfoGeometry.Physics.andreevSwap *
        InfoGeometry.Physics.massiveBdGCommutatorAnomaly
          finiteCARKinetic finiteCARMass *
        InfoGeometry.Physics.andreevSwap = 0 := by
  have h := InfoGeometry.Physics.andreev_reflect_mass_commutator_anomaly
    finiteCARKinetic finiteCARMass
  rw [h]
  exact add_neg_cancel (InfoGeometry.Physics.massiveBdGCommutatorAnomaly
    finiteCARKinetic finiteCARMass)

/-- The square of the concrete finite CAR BdG operator splits into its
ordered even contribution and the nonzero interaction anomaly. -/
theorem finiteCAR_BdG_square_retains_interaction_anomaly :
    InfoGeometry.Physics.massiveBdGHamiltonian finiteCARKinetic finiteCARMass *
        InfoGeometry.Physics.massiveBdGHamiltonian finiteCARKinetic finiteCARMass =
      InfoGeometry.Physics.massiveBdGSquareEven finiteCARKinetic finiteCARMass +
        InfoGeometry.Physics.massiveBdGCommutatorAnomaly
          finiteCARKinetic finiteCARMass :=
  InfoGeometry.Physics.massiveBdGHamiltonian_sq_split
    finiteCARKinetic finiteCARMass

/-! ## Cyclotomic Higgs residue on the common finite carrier

The CAR relations force the square of this BdG operator to be an off-diagonal
commutator block. Its square is `-1`, so the operator-valued twelfth
cyclotomic polynomial reduces to the negative BdG square and has quartic
residue `-1`. Particle–hole conjugation changes its sign.
-/

/-- The lifted CAR annihilator and creator remain square-zero operators. -/
theorem finiteCAR_kinetic_sq : finiteCARKinetic * finiteCARKinetic = 0 := by
  rw [finiteCARKinetic, ← cutoffCARAction_mul]
  simp [cutoffCARAction]

theorem finiteCAR_mass_sq : finiteCARMass * finiteCARMass = 0 := by
  rw [finiteCARMass, ← cutoffCARAction_mul]
  simp [cutoffCARAction]

/-- The kinetic–mass commutator is an involution, directly from the two
square-zero laws and the CAR anticommutator. -/
theorem finiteCAR_kinetic_mass_commutator_sq :
    (finiteCARKinetic * finiteCARMass - finiteCARMass * finiteCARKinetic) *
        (finiteCARKinetic * finiteCARMass - finiteCARMass * finiteCARKinetic) = 1 := by
  let D := finiteCARKinetic
  let M := finiteCARMass
  let P := D * M
  have hCAR := finiteCAR_kinetic_mass_anticommutator
  have hD : D * D = 0 := finiteCAR_kinetic_sq
  have hM : M * M = 0 := finiteCAR_mass_sq
  have hMD : M * D = 1 - D * M := by
    calc
      M * D = D * M + M * D - D * M := by abel
      _ = 1 - D * M := by rw [hCAR]
  have hIdem : P * P = P := by
    dsimp [P]
    calc
      D * M * (D * M) = D * (M * D) * M := by noncomm_ring
      _ = D * (1 - D * M) * M := by rw [hMD]
      _ = D * M := by noncomm_ring [hD, hM]
  have hK : D * M - M * D = P + P - 1 := by
    rw [hMD]
    dsimp [P]
    abel
  have hKinv : D * M - M * D =
      PureNonCommutativeOperatorSpine.invS P := by
    rw [hMD]
    dsimp [PureNonCommutativeOperatorSpine.invS, P]
  rw [hKinv]
  exact PureNonCommutativeOperatorSpine.invS_sq hIdem

/-- The finite CAR BdG square is the chiral block of the CAR commutator. -/
theorem finiteCAR_BdG_square_eq_commutator_block :
    let H := InfoGeometry.Physics.massiveBdGHamiltonian
      finiteCARKinetic finiteCARMass
    H * H =
      !![0, finiteCARKinetic * finiteCARMass - finiteCARMass * finiteCARKinetic;
        finiteCARMass * finiteCARKinetic - finiteCARKinetic * finiteCARMass, 0] := by
  dsimp only
  rw [InfoGeometry.Physics.massiveBdGHamiltonian_sq_with_commutator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteCAR_kinetic_sq, finiteCAR_mass_sq, add_comm]

/-- On the common finite CCR–CAR carrier, the BdG square has square `-1`. -/
theorem finiteCAR_BdG_fourth_power_eq_neg_one :
    (InfoGeometry.Physics.massiveBdGHamiltonian
      finiteCARKinetic finiteCARMass) ^ 4 = -1 := by
  let H := InfoGeometry.Physics.massiveBdGHamiltonian
    finiteCARKinetic finiteCARMass
  let K := finiteCARKinetic * finiteCARMass -
    finiteCARMass * finiteCARKinetic
  have hHsq : H * H = !![0, K; -K, 0] := by
    rw [finiteCAR_BdG_square_eq_commutator_block]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [K] <;> abel
  have hKsq : K * K = 1 := by
    simpa [K] using finiteCAR_kinetic_mass_commutator_sq
  have hBlockSq :
      (!![0, K; -K, 0] : InfoGeometry.Physics.BdGBlock CutoffCAROperator) ^ 2 = -1 := by
    have hKneg : K * -K = -1 := by
      calc
        K * -K = -(K * K) := by
          change K.comp (-K) = -(K.comp K)
          exact LinearMap.comp_neg K K
        _ = -1 := by rw [hKsq]
    have hNegK : -K * K = -1 := by
      calc
        -K * K = -(K * K) := by
          change (-K).comp K = -(K.comp K)
          exact LinearMap.neg_comp K K
        _ = -1 := by rw [hKsq]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, hKsq,
        hKneg, hNegK, neg_mul, mul_neg, neg_neg] <;> abel
  have hPower : H ^ 4 = (H * H) * (H * H) := by
    calc
      H ^ 4 = H ^ (2 + 2) := by norm_num
      _ = H ^ 2 * H ^ 2 := by rw [pow_add]
      _ = (H * H) * (H * H) := by rw [pow_two]
  calc
    (InfoGeometry.Physics.massiveBdGHamiltonian
        finiteCARKinetic finiteCARMass) ^ 4 = H ^ 4 := rfl
    _ = (H * H) * (H * H) := hPower
    _ = (!![0, K; -K, 0] : InfoGeometry.Physics.BdGBlock
        CutoffCAROperator) ^ 2 := by rw [hHsq, pow_two]
    _ = -1 := hBlockSq

/-- Exact finite-carrier Higgs/cyclotomic law: the BdG Higgs polynomial is
minus the square, is Andreev-odd, and its square is `-1`. -/
theorem finiteCAR_operatorCyclotomicHiggs_residue :
    let H := InfoGeometry.Physics.massiveBdGHamiltonian
      finiteCARKinetic finiteCARMass
    InfoGeometry.Physics.operatorCyclotomicHiggs H = -(H * H) ∧
    InfoGeometry.Physics.andreevSwap *
        InfoGeometry.Physics.operatorCyclotomicHiggs H *
        InfoGeometry.Physics.andreevSwap =
      -InfoGeometry.Physics.operatorCyclotomicHiggs H ∧
    InfoGeometry.Physics.operatorCyclotomicHiggs H *
        InfoGeometry.Physics.operatorCyclotomicHiggs H = -1 := by
  intro H
  have hFourth : H ^ 4 = -1 := finiteCAR_BdG_fourth_power_eq_neg_one
  have hHiggs : InfoGeometry.Physics.operatorCyclotomicHiggs H = -(H * H) := by
    unfold InfoGeometry.Physics.operatorCyclotomicHiggs
    calc
      H ^ 4 - H ^ 2 + 1 = -1 - H ^ 2 + 1 := by rw [hFourth]
      _ = -(H * H) := by rw [pow_two]; abel
  have hSquareOdd :
      InfoGeometry.Physics.andreevSwap * (H * H) *
          InfoGeometry.Physics.andreevSwap = -(H * H) := by
    rw [finiteCAR_BdG_square_eq_commutator_block,
      InfoGeometry.Physics.andreevSwap_conj]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.neg_apply]
  have hHiggsOdd :
      InfoGeometry.Physics.andreevSwap *
          InfoGeometry.Physics.operatorCyclotomicHiggs H *
          InfoGeometry.Physics.andreevSwap =
        -InfoGeometry.Physics.operatorCyclotomicHiggs H := by
    calc
      InfoGeometry.Physics.andreevSwap *
          InfoGeometry.Physics.operatorCyclotomicHiggs H *
          InfoGeometry.Physics.andreevSwap =
            -(InfoGeometry.Physics.andreevSwap * (H * H) *
            InfoGeometry.Physics.andreevSwap) := by
              rw [hHiggs]
              calc
                (InfoGeometry.Physics.andreevSwap * (-(H * H))) *
                    InfoGeometry.Physics.andreevSwap =
                    (-(InfoGeometry.Physics.andreevSwap * (H * H))) *
                      InfoGeometry.Physics.andreevSwap := by
                        exact congrArg (fun T : InfoGeometry.Physics.BdGBlock
                          CutoffCAROperator => T * InfoGeometry.Physics.andreevSwap)
                          (Matrix.mul_neg InfoGeometry.Physics.andreevSwap (H * H))
                _ = -(InfoGeometry.Physics.andreevSwap * (H * H) *
                    InfoGeometry.Physics.andreevSwap) := by
                      exact Matrix.neg_mul
                        (InfoGeometry.Physics.andreevSwap * (H * H))
                        InfoGeometry.Physics.andreevSwap
      _ = -(-(H * H)) := by rw [hSquareOdd]
      _ = -InfoGeometry.Physics.operatorCyclotomicHiggs H := by rw [hHiggs]
  have hResidue :
      InfoGeometry.Physics.operatorCyclotomicHiggs H *
          InfoGeometry.Physics.operatorCyclotomicHiggs H = -1 := by
    calc
      InfoGeometry.Physics.operatorCyclotomicHiggs H *
          InfoGeometry.Physics.operatorCyclotomicHiggs H =
          (H * H) * (H * H) := by
            rw [hHiggs]
            calc
              (-(H * H)) * (-(H * H)) = -((H * H) * (-(H * H))) :=
                Matrix.neg_mul (H * H) (-(H * H))
              _ = -(-((H * H) * (H * H))) :=
                congrArg Neg.neg (Matrix.mul_neg (H * H) (H * H))
              _ = (H * H) * (H * H) := by abel
      _ = H ^ 4 := by
        calc
          (H * H) * (H * H) = H ^ 2 * H ^ 2 := by rw [pow_two]
          _ = H ^ (2 + 2) := by rw [pow_add]
          _ = H ^ 4 := by norm_num
      _ = -1 := hFourth
  exact ⟨hHiggs, hHiggsOdd, hResidue⟩

/-! ## CCR boundary defect as a symmetry of the CAR BdG interaction

The finite CCR cutoff defect is nontrivial on the shared carrier, while the
CAR kinetic and mass operators act on the other tensor factor.  Its diagonal
particle–hole lift therefore commutes with the full BdG interaction and with
the operator-valued cyclotomic Higgs polynomial.  This records the actual
compatibility between the two finite sectors, rather than identifying their
different commutator laws.
-/

/-- The finite CCR boundary commutator, lifted to the common cutoff–CAR
carrier. -/
def finiteCCRBoundary : CutoffCAROperator :=
  cutoffCCRAction (FiniteTwistorCCRGeneratingFunction.commutator
    twistorCoordinate twistorDerivative)

/-- The CCR boundary acts in the same way in particle and hole sectors. -/
def finiteCCRBoundaryBdGLift : InfoGeometry.Physics.BdGBlock CutoffCAROperator :=
  !![finiteCCRBoundary, 0; 0, finiteCCRBoundary]

/-- The support of the finite CCR boundary defect.  The cutoff commutator has
eigenvalues `1, 0, 0, -1`; its square is therefore the projection onto the two
boundary levels. -/
def finiteCCRBoundarySupport : CutoffCAROperator :=
  finiteCCRBoundary * finiteCCRBoundary

/-- The cutoff boundary commutator is tripotent: its two nonzero boundary
eigenvalues are opposite, and its interior eigenvalues vanish. -/
theorem finiteCCRBoundary_tripotent :
    finiteCCRBoundary * finiteCCRBoundary * finiteCCRBoundary =
      finiteCCRBoundary := by
  have hCube :
      (FiniteTwistorCCRGeneratingFunction.commutator
          twistorCoordinate twistorDerivative) ^ 3 =
        FiniteTwistorCCRGeneratingFunction.commutator
          twistorCoordinate twistorDerivative := by
    rw [FiniteTwistorCCRGeneratingFunction.finite_twistor_commutator]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pow_succ, pow_two, Matrix.mul_apply, Fin.sum_univ_four]
  have hCube' :
      FiniteTwistorCCRGeneratingFunction.commutator twistorCoordinate twistorDerivative *
        FiniteTwistorCCRGeneratingFunction.commutator twistorCoordinate twistorDerivative *
        FiniteTwistorCCRGeneratingFunction.commutator twistorCoordinate twistorDerivative =
      FiniteTwistorCCRGeneratingFunction.commutator twistorCoordinate twistorDerivative := by
    simpa [pow_succ, pow_two, mul_assoc] using hCube
  simpa [finiteCCRBoundary, cutoffCCRAction_mul] using
    congrArg (cutoffCCRAction) hCube'

/-- The square of the cutoff CCR defect is an idempotent boundary support
projection on the finite CAR–CCR carrier. -/
theorem finiteCCRBoundarySupport_idempotent :
    finiteCCRBoundarySupport * finiteCCRBoundarySupport =
      finiteCCRBoundarySupport := by
  dsimp [finiteCCRBoundarySupport]
  calc
    (finiteCCRBoundary * finiteCCRBoundary) *
        (finiteCCRBoundary * finiteCCRBoundary) =
      (finiteCCRBoundary * finiteCCRBoundary * finiteCCRBoundary) *
        finiteCCRBoundary := by noncomm_ring
    _ = finiteCCRBoundary * finiteCCRBoundary := by
      rw [finiteCCRBoundary_tripotent]

/-- The boundary support acts as the identity on the signed boundary defect. -/
theorem finiteCCRBoundary_support_fixes_defect :
    finiteCCRBoundarySupport * finiteCCRBoundary = finiteCCRBoundary := by
  dsimp [finiteCCRBoundarySupport]
  exact finiteCCRBoundary_tripotent

/-- The finite CCR boundary defect commutes with each CAR interaction entry
because the two operators act on distinct tensor factors. -/
theorem finiteCCRBoundary_commutes_with_CAR_mass_pair :
    finiteCCRBoundary * finiteCARKinetic = finiteCARKinetic * finiteCCRBoundary ∧
    finiteCCRBoundary * finiteCARMass = finiteCARMass * finiteCCRBoundary := by
  constructor
  · exact cutoffCCRAction_commutes_cutoffCARAction
      (FiniteTwistorCCRGeneratingFunction.commutator
        twistorCoordinate twistorDerivative) annihilationOne
  · exact cutoffCCRAction_commutes_cutoffCARAction
      (FiniteTwistorCCRGeneratingFunction.commutator
        twistorCoordinate twistorDerivative) creationOne

/-- Squaring a commuting operator preserves the commutation relation. -/
theorem square_commutes_of_commutes
    {R : Type*} [Ring R] (a b : R) (h : a * b = b * a) :
    (a * a) * b = b * (a * a) := by
  calc
    (a * a) * b = a * (a * b) := by rw [mul_assoc]
    _ = a * (b * a) := by rw [h]
    _ = (a * b) * a := by rw [mul_assoc]
    _ = (b * a) * a := by rw [h]
    _ = b * (a * a) := by rw [mul_assoc]

/-- The idempotent support projection of the finite CCR anomaly commutes with
both CAR interaction generators. -/
theorem finiteCCRBoundarySupport_commutes_with_CAR_mass_pair :
    finiteCCRBoundarySupport * finiteCARKinetic =
        finiteCARKinetic * finiteCCRBoundarySupport ∧
    finiteCCRBoundarySupport * finiteCARMass =
        finiteCARMass * finiteCCRBoundarySupport := by
  rcases finiteCCRBoundary_commutes_with_CAR_mass_pair with ⟨hK, hM⟩
  exact ⟨square_commutes_of_commutes finiteCCRBoundary finiteCARKinetic hK,
    square_commutes_of_commutes finiteCCRBoundary finiteCARMass hM⟩

/-- In a matrix algebra over any operator ring, a scalar diagonal block
commutes with the BdG block whenever its entry commutes with the two
interaction generators. -/
theorem scalar_diagonal_commutes_with_massiveBdG
    {R : Type*} [Ring R] (C D M : R)
    (hD : C * D = D * C) (hM : C * M = M * C) :
    (!![C, 0; 0, C] : InfoGeometry.Physics.BdGBlock R) *
        InfoGeometry.Physics.massiveBdGHamiltonian D M =
      InfoGeometry.Physics.massiveBdGHamiltonian D M * !![C, 0; 0, C] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.massiveBdGHamiltonian, Matrix.mul_apply,
      Fin.sum_univ_two, hD, hM, mul_neg, neg_mul]

/-- The diagonal particle–hole lift of the cutoff CCR boundary defect
commutes with the finite CAR BdG Hamiltonian. -/
theorem finiteCCRBoundaryBdGLift_commutes_with_massiveBdG :
    finiteCCRBoundaryBdGLift *
        InfoGeometry.Physics.massiveBdGHamiltonian
          finiteCARKinetic finiteCARMass =
      InfoGeometry.Physics.massiveBdGHamiltonian
          finiteCARKinetic finiteCARMass * finiteCCRBoundaryBdGLift := by
  rcases finiteCCRBoundary_commutes_with_CAR_mass_pair with ⟨hK, hM⟩
  exact scalar_diagonal_commutes_with_massiveBdG finiteCCRBoundary
    finiteCARKinetic finiteCARMass hK hM

/-- The boundary-support projection acts identically in particle and hole
blocks. -/
def finiteCCRBoundarySupportBdGLift :
    InfoGeometry.Physics.BdGBlock CutoffCAROperator :=
  !![finiteCCRBoundarySupport, 0; 0, finiteCCRBoundarySupport]

/-- The particle–hole lift of the cutoff boundary support is itself a
projection on the BdG carrier. -/
theorem finiteCCRBoundarySupportBdGLift_idempotent :
    finiteCCRBoundarySupportBdGLift * finiteCCRBoundarySupportBdGLift =
      finiteCCRBoundarySupportBdGLift := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteCCRBoundarySupportBdGLift,
      finiteCCRBoundarySupport_idempotent, Matrix.mul_apply, Fin.sum_univ_two]

/-- The boundary-support projection commutes with the massive CAR BdG
Hamiltonian. Thus the finite cutoff boundary sector is invariant under the
actual noncommuting mass interaction. -/
theorem finiteCCRBoundarySupportBdGLift_commutes_with_massiveBdG :
    finiteCCRBoundarySupportBdGLift *
        InfoGeometry.Physics.massiveBdGHamiltonian
          finiteCARKinetic finiteCARMass =
      InfoGeometry.Physics.massiveBdGHamiltonian
          finiteCARKinetic finiteCARMass * finiteCCRBoundarySupportBdGLift := by
  rcases finiteCCRBoundarySupport_commutes_with_CAR_mass_pair with ⟨hK, hM⟩
  exact scalar_diagonal_commutes_with_massiveBdG finiteCCRBoundarySupport
    finiteCARKinetic finiteCARMass hK hM

/-- The cutoff CCR boundary symmetry also commutes with the BdG cyclotomic
Higgs operator.  The claim follows from multiplication compatibility with
the actual Hamiltonian powers, not from diagonalizing either operator. -/
theorem finiteCCRBoundaryBdGLift_commutes_with_operatorCyclotomicHiggs :
    finiteCCRBoundaryBdGLift *
        InfoGeometry.Physics.operatorCyclotomicHiggs
          (InfoGeometry.Physics.massiveBdGHamiltonian
            finiteCARKinetic finiteCARMass) =
      InfoGeometry.Physics.operatorCyclotomicHiggs
          (InfoGeometry.Physics.massiveBdGHamiltonian
            finiteCARKinetic finiteCARMass) * finiteCCRBoundaryBdGLift := by
  let H := InfoGeometry.Physics.massiveBdGHamiltonian
    finiteCARKinetic finiteCARMass
  have hBH : finiteCCRBoundaryBdGLift * H = H * finiteCCRBoundaryBdGLift :=
    finiteCCRBoundaryBdGLift_commutes_with_massiveBdG
  have hBpow : ∀ n : ℕ,
      finiteCCRBoundaryBdGLift * H ^ n = H ^ n * finiteCCRBoundaryBdGLift := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      calc
        finiteCCRBoundaryBdGLift * (H ^ n * H) =
            (finiteCCRBoundaryBdGLift * H ^ n) * H := by rw [← mul_assoc]
        _ = (H ^ n * finiteCCRBoundaryBdGLift) * H := by rw [ih]
        _ = H ^ n * (finiteCCRBoundaryBdGLift * H) := by rw [mul_assoc]
        _ = H ^ n * (H * finiteCCRBoundaryBdGLift) := by rw [hBH]
        _ = (H ^ n * H) * finiteCCRBoundaryBdGLift := by rw [mul_assoc]
  unfold InfoGeometry.Physics.operatorCyclotomicHiggs
  change finiteCCRBoundaryBdGLift * (H ^ 4 - H ^ 2 + 1) =
    (H ^ 4 - H ^ 2 + 1) * finiteCCRBoundaryBdGLift
  let X := H ^ 4
  let Y := H ^ 2
  have hBX : finiteCCRBoundaryBdGLift * X = X * finiteCCRBoundaryBdGLift := by
    dsimp [X]
    exact hBpow 4
  have hBY : finiteCCRBoundaryBdGLift * Y = Y * finiteCCRBoundaryBdGLift := by
    dsimp [Y]
    exact hBpow 2
  change finiteCCRBoundaryBdGLift * (X - Y + 1) =
    (X - Y + 1) * finiteCCRBoundaryBdGLift
  noncomm_ring [hBX, hBY]

/-! ## Particle–hole grading of the finite CAR interaction -/

/-- The CAR creator and annihilator occupy both extreme chiral five-grades in
the BdG interaction anomaly. Each component is nonzero, and Andreev reflection
cancels each component with its reflected partner. -/
theorem finiteCAR_BdG_extreme_grades_and_Andreev_cancellation :
    (InfoGeometry.Physics.Algebra.fiveGradeProjector
        (InfoGeometry.Physics.chiralGrading
          (A := CutoffCAROperator)) .posTwo
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly
          finiteCARKinetic finiteCARMass) ≠ 0 ∧
      InfoGeometry.Physics.Algebra.fiveGradeProjector
        (InfoGeometry.Physics.chiralGrading
          (A := CutoffCAROperator)) .negTwo
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly
          finiteCARKinetic finiteCARMass) ≠ 0) ∧
    InfoGeometry.Physics.andreevSwap *
        InfoGeometry.Physics.Algebra.fiveGradeProjector
          (InfoGeometry.Physics.chiralGrading
            (A := CutoffCAROperator)) .posTwo
          (InfoGeometry.Physics.massiveBdGCommutatorAnomaly
            finiteCARKinetic finiteCARMass) *
        InfoGeometry.Physics.andreevSwap +
      InfoGeometry.Physics.Algebra.fiveGradeProjector
        (InfoGeometry.Physics.chiralGrading
          (A := CutoffCAROperator)) .negTwo
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly
          finiteCARKinetic finiteCARMass) = 0 ∧
    InfoGeometry.Physics.andreevSwap *
        InfoGeometry.Physics.Algebra.fiveGradeProjector
          (InfoGeometry.Physics.chiralGrading
            (A := CutoffCAROperator)) .negTwo
          (InfoGeometry.Physics.massiveBdGCommutatorAnomaly
            finiteCARKinetic finiteCARMass) *
        InfoGeometry.Physics.andreevSwap +
      InfoGeometry.Physics.Algebra.fiveGradeProjector
        (InfoGeometry.Physics.chiralGrading
          (A := CutoffCAROperator)) .posTwo
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly
          finiteCARKinetic finiteCARMass) = 0 := by
  have hDM : finiteCARKinetic * finiteCARMass ≠
      finiteCARMass * finiteCARKinetic := by
    intro h
    apply finiteCAR_kinetic_mass_commutator_ne_zero
    exact sub_eq_zero.mpr h
  have hGrades :=
    InfoGeometry.OperatorAlgebra.PeirceBdGFiveGradeBridge.massiveBdG_noncommutation_has_both_extreme_grades
      finiteCARKinetic finiteCARMass
  have hComponents :=
    InfoGeometry.OperatorAlgebra.PeirceBdGFiveGradeBridge.andreev_reflect_chiral_anomaly_grade_components
      finiteCARKinetic finiteCARMass
  rcases hGrades.mpr hDM with ⟨hPos, hNeg⟩
  rcases hComponents with ⟨hRefPos, hRefNeg⟩
  refine ⟨⟨hPos, hNeg⟩, ?_, ?_⟩
  · rw [hRefPos]
    exact neg_add_cancel
      (InfoGeometry.Physics.Algebra.fiveGradeProjector
        (InfoGeometry.Physics.chiralGrading (A := CutoffCAROperator)) .negTwo
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly
          finiteCARKinetic finiteCARMass))
  · rw [hRefNeg]
    exact neg_add_cancel
      (InfoGeometry.Physics.Algebra.fiveGradeProjector
        (InfoGeometry.Physics.chiralGrading (A := CutoffCAROperator)) .posTwo
        (InfoGeometry.Physics.massiveBdGCommutatorAnomaly
          finiteCARKinetic finiteCARMass))

end InfoGeometry.Canonical.FiniteCARCCRCommonCarrier

end
