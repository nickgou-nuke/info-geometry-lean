import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Algebra.CuntzN
import InfoGeometry.Algebra.CuntzInductiveLimit
import InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge
import InfoGeometry.Canonical.CuntzKTowerCommutation
import InfoGeometry.Canonical.CliffordCARGeneratorTopological
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Clifford.CliffordBitWordEquivalence
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Clifford.SupergradedCliffordColimit
import InfoGeometry.Clifford.Cl11InfiniteCarrier
import InfoGeometry.Physics.ChiralSUSYBlockFactorization

/-!
# `Cl(1,1)` colimit, Cuntz/Cantor hopping, and chiral charges

The common algebraic carrier is the `Cl(1,1)` tensor-tower colimit.  A Cuntz
operator ring and its Cantor orbit are target representations of that carrier,
not definitions of the carrier itself.  This file supplies the universal
descent from compatible finite-stage ring maps and records the existing
chiral supercharge laws on the same target ring.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11CuntzCantorChiralFramework

open InfoGeometry.Algebra
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Algebra.Cuntz
open InfoGeometry.Topology
open InfoGeometry.Topology.CuntzO2Carrier
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CliffordCARGeneratorTopological
open InfoGeometry.Canonical.CantorCuntzBasis
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Clifford.Cl11InfiniteCarrier
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Algebra.CliffordBitWordEquivalence
open InfoGeometry.Clifford.SupergradedCliffordColimit
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Physics
open InfoGeometry.Canonical.CurrentSugawaraBridge

variable {Op : Type} [Ring Op] [StarRing Op]

/-! ## Compatible finite-stage representation data -/

structure CompatibleCuntzRepresentation where
  cuntz : CuntzNAlgebra (N := 2) Op
  stageMap : ∀ n : ℕ,
    InfoGeometry.Clifford.Cl11InfiniteCarrier.Stage n →+* Op
  stage_compat : ∀ (n : ℕ)
      (x : InfoGeometry.Clifford.Cl11InfiniteCarrier.Stage n),
    stageMap (n + 1)
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond n x) =
      stageMap n x
  seed : Op

namespace CompatibleCuntzRepresentation

variable (R : CompatibleCuntzRepresentation (Op := Op))

/-! ## Universal descent to the common colimit carrier -/

def compatibleCone : CompatibleCone
    InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond R.stageMap := by
  intro n x
  exact R.stage_compat n x

def representation (R : CompatibleCuntzRepresentation (Op := Op)) :
    InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier →+* Op :=
  let hcone : CompatibleCone
      InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond R.stageMap := by
    intro n x
    exact R.stage_compat n x
  directLimitLift
    InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond R.stageMap hcone

@[simp] theorem representation_stage (n : ℕ)
    (x : InfoGeometry.Clifford.Cl11InfiniteCarrier.Stage n) :
    representation R
        (InfoGeometry.Clifford.Cl11InfiniteCarrier.intoCarrier n x) =
      R.stageMap n x := by
  change directLimitLift
      InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond R.stageMap
      (compatibleCone R)
      (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n x) =
    R.stageMap n x
  exact directLimitLift_of
    InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond R.stageMap
    (compatibleCone R) n x

theorem representation_finiteAdvance (m k : ℕ)
    (x : InfoGeometry.Clifford.Cl11InfiniteCarrier.Stage m) :
    representation R
        (InfoGeometry.Clifford.Cl11InfiniteCarrier.intoCarrier
          (m + k) (InfoGeometry.Clifford.Cl11InfiniteCarrier.finiteAdvance m k x)) =
      R.stageMap m x := by
  rw [representation_stage]
  exact compatibleCone_bondMap
    InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond R.stageMap R.stage_compat
    m (m + k) (Nat.le_add_right m k) x

theorem representation_commutator (K X : CompatibleCarrier) :
    representation R (ringCommutator K X) =
      ringCommutator (representation R K) (representation R X) := by
  simp only [ringCommutator, map_sub, map_mul]

/-! ## Cuntz/Cantor hopping readout -/

def cantorOrbit (R : CompatibleCuntzRepresentation (Op := Op))
    (w : List Bool) : Op :=
  orbit R.cuntz R.seed w

@[simp] theorem cantorOrbit_root :
    cantorOrbit R [] = R.seed := by
  rfl

theorem cantorOrbit_branch (b : Bool) (w : List Bool) :
    cantorOrbit R (b :: w) =
      (if b then CuntzO2Carrier.S_right R.cuntz
      else CuntzO2Carrier.S_left R.cuntz) * cantorOrbit R w := by
  exact orbit_branch_recursion R.cuntz R.seed b w

theorem cantorOrbit_branch_adjoint_same (b : Bool) (w : List Bool) :
    star (if b then CuntzO2Carrier.S_right R.cuntz
      else CuntzO2Carrier.S_left R.cuntz) * R.cantorOrbit (b :: w) =
      cantorOrbit R w := by
  exact orbit_branch_adjoint_same R.cuntz R.seed b w

theorem cantor_root_branching (ξ : ℕ → Bool) :
    (CuntzO2Carrier.leftRangeProjection R.cuntz * R.seed +
      CuntzO2Carrier.rightRangeProjection R.cuntz * R.seed = R.seed) ∧
      ξ = boundaryCons (boundaryHead ξ) (boundaryTail ξ) := by
  exact cantorCuntz_root_branching R.cuntz R.seed ξ

/-! ## Chiral supercharge readout on the representation target -/

def qPlus (a : Op) : ChiralBlock Op := chiralQPlus a

def qMinus (b : Op) : ChiralBlock Op := chiralQMinus b

def chiralHamiltonian (a b : Op) : ChiralBlock Op :=
  chiralSUSYHamiltonian a b

theorem qPlus_square (a : Op) :
    qPlus a * qPlus a = 0 := by
  exact chiralQPlus_sq a

theorem qMinus_square (b : Op) :
    qMinus b * qMinus b = 0 := by
  exact chiralQMinus_sq b

theorem chiral_dirac_square (a b : Op) :
    chiralDirac a b * chiralDirac a b = chiralHamiltonian a b := by
  exact chiralDirac_sq_eq_susyHamiltonian a b

end CompatibleCuntzRepresentation

/-! ## Current and Sugawara readout from the same colimit carrier -/

structure CarrierCurrentInterface
    (𝕜 V : Type*) [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V] where
  carrierAction :
    InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier →+*
      (V →ₗ[𝕜] V)
  modeCarrier : Int →
    InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier
  heisenberg : CurrentHeisenbergRep 𝕜 V
  mode_readout : ∀ m : Int,
    carrierAction (modeCarrier m) = heisenberg.J m

namespace CarrierCurrentInterface

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable (C : CarrierCurrentInterface 𝕜 V)

theorem mode_commutator_readout
    (m n : Int) :
    (C.carrierAction (C.modeCarrier m)).commutator
        (C.carrierAction (C.modeCarrier n)) =
      (C.heisenberg.J m).commutator (C.heisenberg.J n) := by
  rw [C.mode_readout, C.mode_readout]

noncomputable def sugawara : CurrentSugawaraMorphism 𝕜 V :=
  CurrentSugawaraMorphism.ofHeisenberg C.heisenberg

theorem sugawara_lgen_readout (n : Int) :
    (C.sugawara).virasoro
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n) =
      C.heisenberg.sugawaraStressMode n := by
  exact C.heisenberg.currentSugawaraRepresentation_lgen_apply n

theorem sugawara_central_readout :
    (C.sugawara).virasoro
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜) =
      (1 : V →ₗ[𝕜] V) := by
  exact C.heisenberg.currentSugawaraRepresentation_central

end CarrierCurrentInterface

/-! ## One package for the carrier, Cuntz/Cantor hopping, and current algebra -/

structure Framework
    (𝕜 V : Type*) [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (Op : Type) [Ring Op] [StarRing Op] where
  cuntzRepresentation : CompatibleCuntzRepresentation (Op := Op)
  currentInterface : CarrierCurrentInterface 𝕜 V

namespace Framework

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable {Op : Type} [Ring Op] [StarRing Op]
variable (F : Framework 𝕜 V Op)

def carrierRepresentation (F : Framework 𝕜 V Op) :
    InfoGeometry.Clifford.Cl11InfiniteCarrier.CompatibleCarrier →+* Op :=
  CompatibleCuntzRepresentation.representation F.cuntzRepresentation

noncomputable def sugawaraMorphism (F : Framework 𝕜 V Op) :
    CurrentSugawaraMorphism 𝕜 V :=
  CurrentSugawaraMorphism.ofHeisenberg F.currentInterface.heisenberg

theorem carrier_stage_readout (n : ℕ)
    (x : InfoGeometry.Clifford.Cl11InfiniteCarrier.Stage n) :
    carrierRepresentation F
        (InfoGeometry.Clifford.Cl11InfiniteCarrier.intoCarrier n x) =
      F.cuntzRepresentation.stageMap n x := by
  exact CompatibleCuntzRepresentation.representation_stage
    F.cuntzRepresentation n x

theorem virasoro_lgen_readout (n : Int) :
    (sugawaraMorphism F).virasoro
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n) =
      F.currentInterface.heisenberg.sugawaraStressMode n := by
  exact CarrierCurrentInterface.sugawara_lgen_readout
    F.currentInterface n

theorem virasoro_central_readout :
    (sugawaraMorphism F).virasoro
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜) =
      (1 : V →ₗ[𝕜] V) := by
  exact CarrierCurrentInterface.sugawara_central_readout
    F.currentInterface

end Framework

/-! ## Coherent Clifford/UHF carrier identification

The finite Clifford tower and the BitWord-indexed UHF tower are identified by
the existing `CliffordBitWordEquivalence` owner.  In particular, this is a
coherent identification of towers, not an independent reindexing at each
stage.  The universal Cuntz quotient remains a separate representation
target; the theorem below transports only the finite matrix/Cuntz core.
-/

namespace CarrierEquivalenceReadout

abbrev uhfCarrier :=
  InfoGeometry.Algebra.PrimonColimitAlgebra.PrimonUHFAlgebra

abbrev clCarrier :=
  InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

noncomputable def commonCarrierEquiv : clCarrier ≃+* uhfCarrier :=
  cliffordBitWordColimitEquiv

theorem finite_stage_coherence (n : ℕ)
    (A : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n) :
    clStageEquiv (n + 1)
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond n A) =
      InfoGeometry.Algebra.PrimonColimitAlgebra.matrixBond n
        (clStageEquiv n A) := by
  exact clStageEquiv_bond n A

@[simp] theorem commonCarrierEquiv_stage (n : ℕ)
    (A : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n) :
    commonCarrierEquiv
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n A) =
      InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n
        (clStageEquiv n A) := by
  exact cliffordBitWordColimitEquiv_ofStage n A

theorem commonCarrierEquiv_trace_stage (n : ℕ)
    (A : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (commonCarrierEquiv
          (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n A)) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace n A := by
  rw [commonCarrierEquiv_stage,
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity_stage]
  exact normalizedTrace_clStageEquiv n A

@[simp] theorem commonCarrierEquiv_core_unit (n : ℕ)
    (u v : BitWord n) :
    commonCarrierEquiv
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
          (cl11CuntzCoreUnit n u v)) =
      InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n
        (cuntzCoreUnit n u v) := by
  simpa [cl11CuntzCoreUnit, cuntzCoreUnit] using
    (commonCarrierEquiv_stage n (cl11CuntzCoreUnit n u v))

theorem commonCarrierEquiv_core_unit_mul (n : ℕ)
    (u v x y : BitWord n) :
    cl11CuntzCoreUnit n u v * cl11CuntzCoreUnit n x y =
      if v = x then cl11CuntzCoreUnit n u y else 0 := by
  exact cl11CuntzCoreUnit_mul n u v x y

@[simp] theorem commonCarrierEquiv_core_unit_product (n : ℕ)
    (u v x y : BitWord n) :
    commonCarrierEquiv
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
          (cl11CuntzCoreUnit n u v * cl11CuntzCoreUnit n x y)) =
      InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n
        (cuntzCoreUnit n u v * cuntzCoreUnit n x y) := by
  calc
    commonCarrierEquiv
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
          (cl11CuntzCoreUnit n u v * cl11CuntzCoreUnit n x y)) =
        commonCarrierEquiv
          (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
              (cl11CuntzCoreUnit n u v) *
            InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
              (cl11CuntzCoreUnit n x y)) := by
      exact congrArg commonCarrierEquiv
        ((InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n).map_mul
          (cl11CuntzCoreUnit n u v) (cl11CuntzCoreUnit n x y))
    _ = commonCarrierEquiv
          (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
              (cl11CuntzCoreUnit n u v)) *
        commonCarrierEquiv
          (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n
              (cl11CuntzCoreUnit n x y)) := by
      exact map_mul commonCarrierEquiv _ _
    _ = InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n
          (cuntzCoreUnit n u v * cuntzCoreUnit n x y) := by
      rw [commonCarrierEquiv_core_unit, commonCarrierEquiv_core_unit]
      exact ((InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n).map_mul _ _).symm

@[simp] theorem commonCarrierEquiv_creation_element (n : ℕ) (k : Fin n) :
    commonCarrierEquiv (algebraicCreationElement n k) =
      InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n
        (clStageEquiv n (jwCreation n k)) := by
  exact commonCarrierEquiv_stage n (jwCreation n k)

@[simp] theorem commonCarrierEquiv_annihilation_element (n : ℕ) (k : Fin n) :
    commonCarrierEquiv (algebraicAnnihilationElement n k) =
      InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n
        (clStageEquiv n (jwAnnihilation n k)) := by
  exact commonCarrierEquiv_stage n (jwAnnihilation n k)

theorem commonCarrierEquiv_creation_action_ofStage
    (n : ℕ) (k : Fin n)
    (A : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n) :
    commonCarrierEquiv
        (algebraicCreationAction n k
          (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n A)) =
      InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n
        (clStageEquiv n (jwCreation n k * A)) := by
  rw [algebraicCreationAction_ofStage]
  exact commonCarrierEquiv_stage n (jwCreation n k * A)

theorem commonCarrierEquiv_annihilation_action_ofStage
    (n : ℕ) (k : Fin n)
    (A : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n) :
    commonCarrierEquiv
        (algebraicAnnihilationAction n k
          (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n A)) =
      InfoGeometry.Algebra.PrimonColimitAlgebra.toColimit n
        (clStageEquiv n (jwAnnihilation n k * A)) := by
  rw [algebraicAnnihilationAction_ofStage]
  exact commonCarrierEquiv_stage n (jwAnnihilation n k * A)

/-- The common-carrier equivalence transports the native inner commutator. -/
theorem commonCarrierEquiv_commutator (K X : clCarrier) :
    commonCarrierEquiv (ringCommutator K X) =
      ringCommutator (commonCarrierEquiv K) (commonCarrierEquiv X) := by
  simp [ringCommutator]

theorem commonCarrierEquiv_trace_commutator_zero (K X : clCarrier) :
    InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
        (commonCarrierEquiv (ringCommutator K X)) = 0 := by
  rw [commonCarrierEquiv_commutator]
  change InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity
      (commonCarrierEquiv K * commonCarrierEquiv X -
        commonCarrierEquiv X * commonCarrierEquiv K) = 0
  exact InfoGeometry.Algebra.PrimonColimitAlgebra.tauInfinity_commutator_zero _ _

end CarrierEquivalenceReadout

/-! ## Toeplitz/Cuntz quotient, shift, and finite tilted-Fock readouts -/

namespace FiniteCuntzTiltFockReadout

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Canonical.CuntzKTowerCommutation

theorem toeplitz_orthogonality (n : ℕ) (i j : Fin n) :
    toeplitzSdag n i * toeplitzS n j = if i = j then 1 else 0 := by
  exact InfoGeometry.Algebra.CuntzTensorQuotient.toeplitz_orthogonality n i j

theorem cuntz_orthogonality (n : ℕ) (i j : Fin n) :
    cuntzSdag n i * cuntzS n j = if i = j then 1 else 0 := by
  exact InfoGeometry.Algebra.CuntzTensorQuotient.cuntz_orthogonality n i j

theorem cuntz_ranges_sum_one (n : ℕ) :
    (∑ i : Fin n, cuntzS n i * cuntzSdag n i) = 1 := by
  exact InfoGeometry.Algebra.CuntzTensorQuotient.cuntz_ranges_sum_one n

theorem finite_tilted_fock_atom
    {P : PrimeRegister} {R : Type*} [AddGroup R] [DecidableEq ℕ]
    (p : ℕ) (hp : p ∈ P.primes) :
    compOp (switchOp (P := P) (R := R) p hp)
        (switchOp (P := P) (R := R) p hp) = idOp ∧
    compOp (tiltOp (P := P) (R := R) p)
        (tiltOp (P := P) (R := R) p) = idOp ∧
    compOp (tiltOp (P := P) (R := R) p)
        (switchOp (P := P) (R := R) p hp) =
      negOp (compOp (switchOp (P := P) (R := R) p hp)
        (tiltOp (P := P) (R := R) p)) ∧
    compOp (splitDOp (P := P) (R := R) p hp)
        (splitDOp (P := P) (R := R) p hp) = negOp idOp := by
  exact ⟨switchOp_sq p hp, tiltOp_sq p,
    tilt_switch_anticomm p hp, splitDOp_sq p hp⟩

structure CompatibleShiftPhase where
  shift : ∀ n : ℕ, TowerStage n
  phase : ∀ n : ℕ, TowerStage n
  shift_compat : ∀ n,
    InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n (shift n) = shift (n + 1)
  phase_compat : ∀ n,
    InfoGeometry.Clifford.Cl11TensorTower.stageEmbed n (phase n) = phase (n + 1)
  commute : ∀ n, shift n * phase n = phase n * shift n

namespace CompatibleShiftPhase

variable (C : CompatibleShiftPhase)

theorem colimit_commutes :
    limitElement C.shift * limitK C.phase =
      limitK C.phase * limitElement C.shift := by
  exact S_left_commutes_K_limit C.shift C.phase
    C.shift_compat C.phase_compat C.commute 0

theorem stage_readout (n : ℕ) :
    ofStage n (C.shift n) * ofStage n (C.phase n) =
      ofStage n (C.phase n) * ofStage n (C.shift n) :=
  by
    simpa only [map_mul] using
      congrArg (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n)
        (C.commute n)

end CompatibleShiftPhase

end FiniteCuntzTiltFockReadout

end InfoGeometry.Canonical.Cl11CuntzCantorChiralFramework
