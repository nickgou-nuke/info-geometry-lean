import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
import InfoGeometry.Lie.SplitOctonionEllCrossChannel
import InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
import InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
import InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
import InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport
import InfoGeometry.Lie.SplitOctonionCircularZ3Grading
import InfoGeometry.Lie.SplitOctonionEllCircularCAR
import InfoGeometry.Lie.SplitOctonionAnnihilatorDimension

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge

open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionCircularZ3Grading
open InfoGeometry.Lie.SplitOctonionEllCircularCAR
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

def canonicalExteriorTransport (T : Module.End ℝ Exterior3) : EndCZ :=
  transportEndGeneric exterior3CircularPeirceEquiv T

@[simp] theorem canonicalExteriorTransport_apply
    (T : Module.End ℝ Exterior3) (x : CZ) :
    canonicalExteriorTransport T x =
      exterior3CircularPeirceEquiv (T (exterior3CircularPeirceEquiv.symm x)) := by
  rfl

theorem canonicalExteriorTransport_mul (S T : Module.End ℝ Exterior3) :
    canonicalExteriorTransport (S * T) =
      canonicalExteriorTransport S * canonicalExteriorTransport T := by
  apply LinearMap.ext
  intro x
  simp [canonicalExteriorTransport, transportEndGeneric, Module.End.mul_apply]

theorem canonicalExteriorTransport_add (S T : Module.End ℝ Exterior3) :
    canonicalExteriorTransport (S + T) =
      canonicalExteriorTransport S + canonicalExteriorTransport T := by
  apply LinearMap.ext
  intro x
  simp [canonicalExteriorTransport, transportEndGeneric]

theorem canonicalExteriorTransport_one :
    canonicalExteriorTransport (1 : Module.End ℝ Exterior3) = (1 : EndCZ) := by
  apply LinearMap.ext
  intro x
  simp [canonicalExteriorTransport, transportEndGeneric]

theorem canonicalExteriorTransport_smul (c : ℝ) (T : Module.End ℝ Exterior3) :
    canonicalExteriorTransport (c • T) = c • canonicalExteriorTransport T := by
  apply LinearMap.ext
  intro x
  simp [canonicalExteriorTransport, transportEndGeneric]

theorem canonicalExteriorTransport_CAR (i : Fin 3) :
    canonicalExteriorTransport (exteriorContract3 (modeCovector i)) *
        canonicalExteriorTransport (exteriorWedge3 (modeVector i)) +
        canonicalExteriorTransport (exteriorWedge3 (modeVector i)) *
          canonicalExteriorTransport (exteriorContract3 (modeCovector i)) =
      (1 : EndCZ) := by
  rw [← canonicalExteriorTransport_mul, ← canonicalExteriorTransport_mul,
    ← canonicalExteriorTransport_add, exteriorContract3_wedge3_CAR]
  rw [canonicalExteriorTransport_smul, canonicalExteriorTransport_one]
  simp [modeCovector_modeVector]

theorem canonicalExteriorTransport_wedge_sq (i : Fin 3) :
    canonicalExteriorTransport (exteriorWedge3 (modeVector i)) *
        canonicalExteriorTransport (exteriorWedge3 (modeVector i)) = 0 := by
  rw [← canonicalExteriorTransport_mul]
  rw [exteriorWedge3_sq]
  apply LinearMap.ext
  intro x
  simp [canonicalExteriorTransport, transportEndGeneric]

theorem canonicalExteriorTransport_contract_sq (i : Fin 3) :
    canonicalExteriorTransport (exteriorContract3 (modeCovector i)) *
        canonicalExteriorTransport (exteriorContract3 (modeCovector i)) = 0 := by
  rw [← canonicalExteriorTransport_mul]
  rw [exteriorContract3_sq]
  apply LinearMap.ext
  intro x
  simp [canonicalExteriorTransport, transportEndGeneric]

def rightRegular (x : CZ) : EndCZ := rightMultiplication x

@[simp] theorem rightRegular_apply (x y : CZ) :
    rightRegular x y = y * x := rfl

theorem coordinateEquiv_rightRegular (x : CZ) (c : Coordinate) :
    coordinateEquiv (rightRegular x (coordinateEquiv.symm c)) =
      rightCoordinateOperator x c := by
  rfl

/-! The coordinate readout is a genuine conjugation of the native
right-regular endomorphism.  This is the carrier-alignment lemma needed
before comparing it with any transported exterior operator. -/
theorem rightRegular_eq_coordinate_conjugate (x : CZ) :
    rightRegular x =
      coordinateEquiv.symm.toLinearMap ∘ₗ
        rightCoordinateOperator x ∘ₗ coordinateEquiv.toLinearMap := by
  apply LinearMap.ext
  intro y
  simp [rightRegular, rightCoordinateOperator]

theorem rightRegular_anticommutator (a b : CZ) :
    rightRegular a * rightRegular b + rightRegular b * rightRegular a =
      rightRegular (a * b + b * a) := by
  apply LinearMap.ext
  intro y
  change (y * b) * a + (y * a) * b = y * (a * b + b * a)
  rw [mul_add]
  have hab := canonical_right_alternative (a + b) y
  have ha := canonical_right_alternative a y
  have hb := canonical_right_alternative b y
  change (y * (a + b)) * (a + b) = y * ((a + b) * (a + b)) at hab
  change (y * a) * a = y * (a * a) at ha
  change (y * b) * b = y * (b * b) at hb
  simp only [add_mul, mul_add] at hab
  rw [ha, hb] at hab
  have hab' :
      y * (a * a) + ((y * b) * a + (y * a) * b) =
        y * (a * a) + (y * (b * a) + y * (a * b)) := by
    calc
      y * (a * a) + ((y * b) * a + (y * a) * b) =
          y * (a * a) + y * (b * a) + (y * (a * b) + y * (b * b)) -
            y * (b * b) := by
              rw [← hab]
              abel
      _ = y * (a * a) + (y * (b * a) + y * (a * b)) := by
            abel
  simpa [add_comm, add_left_comm, add_assoc] using add_left_cancel hab'

theorem rightRegular_sq_zero_of_sq_zero (x : CZ) (hx : x * x = 0) :
    rightRegular x * rightRegular x = 0 := by
  apply LinearMap.ext
  intro y
  change (y * x) * x = 0
  rw [canonical_right_alternative, hx]
  exact InfoGeometry.Algebra.Zorn.SplitQuaternionCore.zMul_zero_right y

theorem rightRegular_rootPlus_sq (i : Fin 3) :
    rightRegular (rootPlus i) * rightRegular (rootPlus i) = 0 :=
  rightRegular_sq_zero_of_sq_zero (rootPlus i) (rootPlus_sq i)

theorem rightRegular_rootMinus_sq (i : Fin 3) :
    rightRegular (rootMinus i) * rightRegular (rootMinus i) = 0 :=
  rightRegular_sq_zero_of_sq_zero (rootMinus i) (rootMinus_sq i)

theorem rightRegular_root_CAR (i : Fin 3) :
    rightRegular (rootMinus i) * rightRegular (rootPlus i) +
        rightRegular (rootPlus i) * rightRegular (rootMinus i) = (1 : EndCZ) := by
  rw [rightRegular_anticommutator]
  have hanti : rootMinus i * rootPlus i + rootPlus i * rootMinus i = (1 : CZ) := by
    simpa [add_comm] using root_anticommutator i
  rw [hanti]
  apply LinearMap.ext
  intro y
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul y 1 = y
  exact InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.zMul_one y

theorem rightRegular_root_anticommutator (i j : Fin 3) :
    rightRegular (rootMinus j) * rightRegular (rootPlus i) +
        rightRegular (rootPlus i) * rightRegular (rootMinus j) =
      if i = j then (1 : EndCZ) else 0 := by
  rw [rightRegular_anticommutator]
  rw [show rootMinus j * rootPlus i + rootPlus i * rootMinus j =
      rootPlus i * rootMinus j + rootMinus j * rootPlus i by ac_rfl]
  rw [rootPlus_mul_rootMinus_anticommutator]
  split
  · apply LinearMap.ext
    intro y
    change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul y 1 = y
    exact InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.zMul_one y
  ·
    apply LinearMap.ext
    intro y
    change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul y 0 = 0
    exact InfoGeometry.Algebra.Zorn.SplitQuaternionCore.zMul_zero_right y

theorem rightRegular_root_anticommutator_off_diagonal {i j : Fin 3}
    (h : i ≠ j) :
    rightRegular (rootMinus j) * rightRegular (rootPlus i) +
        rightRegular (rootPlus i) * rightRegular (rootMinus j) = 0 := by
  simpa [h] using rightRegular_root_anticommutator i j

theorem rightRegular_rootPlus_anticommutator (i j : Fin 3) :
    rightRegular (rootPlus i) * rightRegular (rootPlus j) +
        rightRegular (rootPlus j) * rightRegular (rootPlus i) = 0 := by
  rw [rightRegular_anticommutator, rootPlus_mul_rootPlus_anticommutator]
  apply LinearMap.ext
  intro y
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul y 0 = 0
  exact InfoGeometry.Algebra.Zorn.SplitQuaternionCore.zMul_zero_right y

theorem rightRegular_rootMinus_anticommutator (i j : Fin 3) :
    rightRegular (rootMinus i) * rightRegular (rootMinus j) +
        rightRegular (rootMinus j) * rightRegular (rootMinus i) = 0 := by
  rw [rightRegular_anticommutator, rootMinus_mul_rootMinus_anticommutator]
  apply LinearMap.ext
  intro y
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul y 0 = 0
  exact InfoGeometry.Algebra.Zorn.SplitQuaternionCore.zMul_zero_right y

def rightRegularCARPair (i : Fin 3) :
    SplitClifford.CARPair EndCZ where
  ann := rightRegular (rootMinus i)
  cre := rightRegular (rootPlus i)
  ann_sq := rightRegular_rootMinus_sq i
  cre_sq := rightRegular_rootPlus_sq i
  anti := rightRegular_root_CAR i

theorem coordinateEquiv_rightRegular_on_frame (x : CZ) (i : Fin 8) :
    coordinateEquiv (rightRegular x (frame i)) =
      rightCoordinateOperator x (Pi.single i 1) := by
  rw [← coordinateEquiv_symm_single]
  exact
    (coordinateEquiv_rightRegular x (Pi.single i 1))

theorem rightRegular_rootMinus_rootPlus (i j : Fin 3) :
    rightRegular (rootMinus i) (rootPlus j) =
        if i = j then uPlus else 0 := by
  change rootPlus j * rootMinus i = _
  rw [rootPlus_mul_rootMinus_eq_ite]
  by_cases h : j = i
  · subst i
    simp
  · simp [h, Ne.symm h]

theorem rightRegular_rootPlus_rootMinus (i j : Fin 3) :
    rightRegular (rootPlus i) (rootMinus j) =
      if i = j then uMinus else 0 := by
  change rootMinus j * rootPlus i = _
  rw [rootMinus_mul_rootPlus_eq_ite]
  by_cases h : j = i
  · subst i
    simp
  · simp [h, Ne.symm h]

theorem rightRegular_rootPlus_zero_rootPlus_one :
    rightRegular (rootPlus 0) (rootPlus 1) = -rootMinus 2 := by
  change rootPlus 1 * rootPlus 0 = -rootMinus 2
  exact rootPlus_one_mul_rootPlus_zero

theorem rightRegular_rootPlus_one_rootPlus_two :
    rightRegular (rootPlus 1) (rootPlus 2) = -rootMinus 0 := by
  change rootPlus 2 * rootPlus 1 = -rootMinus 0
  exact rootPlus_two_mul_rootPlus_one

theorem rightRegular_rootPlus_two_rootPlus_zero :
    rightRegular (rootPlus 2) (rootPlus 0) = -rootMinus 1 := by
  change rootPlus 0 * rootPlus 2 = -rootMinus 1
  exact rootPlus_zero_mul_rootPlus_two

@[simp] theorem rightRegular_rootPlus_self (i : Fin 3) :
    rightRegular (rootPlus i) (rootPlus i) = 0 := by
  change rootPlus i * rootPlus i = 0
  exact rootPlus_sq i

@[simp] theorem rightRegular_rootMinus_self (i : Fin 3) :
    rightRegular (rootMinus i) (rootMinus i) = 0 := by
  change rootMinus i * rootMinus i = 0
  exact rootMinus_sq i

@[simp] theorem rightRegular_rootPlus_uPlus (i : Fin 3) :
    rightRegular (rootPlus i) uPlus = rootPlus i := by
  change uPlus * rootPlus i = rootPlus i
  exact uPlus_mul_rootPlus i

@[simp] theorem rightRegular_rootPlus_uMinus (i : Fin 3) :
    rightRegular (rootPlus i) uMinus = 0 := by
  change uMinus * rootPlus i = 0
  exact uMinus_mul_rootPlus i

@[simp] theorem rightRegular_rootMinus_uPlus (i : Fin 3) :
    rightRegular (rootMinus i) uPlus = 0 := by
  change uPlus * rootMinus i = 0
  exact uPlus_mul_rootMinus i

@[simp] theorem rightRegular_rootMinus_uMinus (i : Fin 3) :
    rightRegular (rootMinus i) uMinus = rootMinus i := by
  change uMinus * rootMinus i = rootMinus i
  exact uMinus_mul_rootMinus i

theorem rightRegular_creation_endpoint_packet (i : Fin 3) :
    rightRegular (rootPlus i) uPlus = rootPlus i ∧
      rightRegular (rootPlus i) uMinus = 0 :=
  ⟨rightRegular_rootPlus_uPlus i, rightRegular_rootPlus_uMinus i⟩

theorem rightRegular_annihilation_endpoint_packet (i : Fin 3) :
    rightRegular (rootMinus i) uPlus = 0 ∧
      rightRegular (rootMinus i) uMinus = rootMinus i :=
  ⟨rightRegular_rootMinus_uPlus i, rightRegular_rootMinus_uMinus i⟩

end InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
