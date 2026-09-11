import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.RegularActionAssociator
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport
import InfoGeometry.Lie.SplitOctonionEllFockCARComparison
import InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading

noncomputable section
set_option maxHeartbeats 1000000

namespace InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport
open InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ
abbrev SplitCarrier := SplitOctonionCoordinateCarrier
abbrev SplitEnd := Module.End ℝ SplitCarrier

private theorem zorn_left_alt (x y : CZ) :
    (x * x) * y = x * (x * y) := by
  rcases x with ⟨a, b, u, v⟩
  rcases y with ⟨c, d, r, s⟩
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
    ring
  · simp [InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
    ring
  · funext i
    fin_cases i <;> simp [InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross] <;> ring
  · funext i
    fin_cases i <;> simp [InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross] <;> ring

theorem leftRegular_anticommutator (a b : CZ) :
    leftRegular a * leftRegular b + leftRegular b * leftRegular a =
      leftRegular (a * b + b * a) := by
  apply LinearMap.ext
  intro y
  change a * (b * y) + b * (a * y) = (a * b + b * a) * y
  rcases a with ⟨a₁, a₂, a₃, a₄⟩
  rcases b with ⟨b₁, b₂, b₃, b₄⟩
  rcases y with ⟨y₁, y₂, y₃, y₄⟩
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
    ring
  · simp [InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
    ring
  · funext i
    fin_cases i <;> simp [InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross] <;> ring
  · funext i
    fin_cases i <;> simp [InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross] <;> ring

theorem leftRegular_sq_zero_of_sq_zero (x : CZ) (hx : x * x = 0) :
    leftRegular x * leftRegular x = 0 := by
  apply LinearMap.ext
  intro y
  change x * (x * y) = 0
  rw [← zorn_left_alt x y, hx]
  rcases y with ⟨a, b, u, v⟩
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  · simp [InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  · funext i
    fin_cases i <;> simp [InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  · funext i
    fin_cases i <;> simp [InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]

theorem leftRegular_rootPlus_sq (i : Fin 3) :
    leftRegular (rootPlus i) * leftRegular (rootPlus i) = 0 :=
  leftRegular_sq_zero_of_sq_zero (rootPlus i) (rootPlus_sq i)

theorem leftRegular_rootMinus_sq (i : Fin 3) :
    leftRegular (rootMinus i) * leftRegular (rootMinus i) = 0 :=
  leftRegular_sq_zero_of_sq_zero (rootMinus i) (rootMinus_sq i)

theorem leftRegular_root_CAR (i : Fin 3) :
    leftRegular (rootMinus i) * leftRegular (rootPlus i) +
        leftRegular (rootPlus i) * leftRegular (rootMinus i) = (1 : EndCZ) := by
  rw [leftRegular_anticommutator]
  have hanti : rootMinus i * rootPlus i + rootPlus i * rootMinus i = (1 : CZ) := by
    simpa [add_comm] using root_anticommutator i
  rw [hanti]
  apply LinearMap.ext
  intro y
  change (1 : CZ) * y = y
  exact one_zMul y

def leftRegularCARPair (i : Fin 3) : SplitClifford.CARPair EndCZ where
  ann := leftRegular (rootMinus i)
  cre := leftRegular (rootPlus i)
  ann_sq := leftRegular_rootMinus_sq i
  cre_sq := leftRegular_rootPlus_sq i
  anti := leftRegular_root_CAR i

def modeVector (i : Fin 3) : V3 := Pi.single i 1
def modeCovector (i : Fin 3) : Module.Dual ℝ V3 := (Pi.basisFun ℝ (Fin 3)).coord i

@[simp] theorem modeCovector_modeVector (i : Fin 3) :
    modeCovector i (modeVector i) = 1 := by simp [modeCovector, modeVector]

noncomputable def exteriorCoordinateEquiv : Exterior3 ≃ₗ[ℝ] SplitCarrier :=
  exterior3SplitOctonionCoordinateEquiv

def transportedCreation (i : Fin 3) : SplitEnd :=
  splitCoordinateWedge3 exteriorCoordinateEquiv (modeVector i)
def transportedAnnihilation (i : Fin 3) : SplitEnd :=
  splitCoordinateContract3 exteriorCoordinateEquiv (modeCovector i)

theorem transportedCreation_sq (i : Fin 3) :
    transportedCreation i * transportedCreation i = 0 :=
  splitCoordinateWedge3_sq exteriorCoordinateEquiv (modeVector i)

theorem transportedAnnihilation_sq (i : Fin 3) :
    transportedAnnihilation i * transportedAnnihilation i = 0 :=
  splitCoordinateContract3_sq exteriorCoordinateEquiv (modeCovector i)

theorem transportedExterior_CAR (i : Fin 3) :
    transportedAnnihilation i * transportedCreation i +
        transportedCreation i * transportedAnnihilation i = (1 : SplitEnd) := by
  simpa [transportedAnnihilation, transportedCreation, modeCovector_modeVector] using
    (splitCoordinateWedgeContract_CAR exteriorCoordinateEquiv (modeVector i) (modeCovector i))

def transportedExteriorCARPair (i : Fin 3) : SplitClifford.CARPair SplitEnd where
  ann := transportedAnnihilation i
  cre := transportedCreation i
  ann_sq := transportedAnnihilation_sq i
  cre_sq := transportedCreation_sq i
  anti := transportedExterior_CAR i

theorem creation_intertwines (i : Fin 3) :
    transportedCreation i ∘ₗ exteriorCoordinateEquiv.toLinearMap =
      exteriorCoordinateEquiv.toLinearMap ∘ₗ exteriorWedge3 (modeVector i) :=
  transportEnd_intertwines exteriorCoordinateEquiv (exteriorWedge3 (modeVector i))

theorem annihilation_intertwines (i : Fin 3) :
    transportedAnnihilation i ∘ₗ exteriorCoordinateEquiv.toLinearMap =
      exteriorCoordinateEquiv.toLinearMap ∘ₗ exteriorContract3 (modeCovector i) :=
  transportEnd_intertwines exteriorCoordinateEquiv (exteriorContract3 (modeCovector i))

end InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
