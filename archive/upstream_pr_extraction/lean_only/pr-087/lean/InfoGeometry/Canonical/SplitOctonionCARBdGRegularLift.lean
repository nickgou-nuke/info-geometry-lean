import Mathlib.Tactic
import InfoGeometry.Algebra.Zorn.RegularActionAssociator
import InfoGeometry.Algebra.KingdonSplitOctonion
import InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport
import InfoGeometry.Lie.SplitOctonionEllFockCARComparison
import InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading

/-!
# Native CAR/BdG regular-operator lift for split octonions

This owner closes the exact part of the exterior-CAR / split-octonion operator
comparison that follows from alternativity alone.

For an alternative algebra, the associator corrections in the symmetrized
composition of left regular actions cancel. Hence

`L_a L_b + L_b L_a = L_(ab + ba)`.

Therefore every element-level CAR pair in the split octonions lifts to an
operator-level CAR pair in `End`.  The literal Mathlib exterior CAR is also
transported to split coordinates by the already-owned endomorphism algebra
equivalence.

This file deliberately does not identify exterior creation with *left* regular
multiplication by a positive circular root.  Under the established exterior
ordering, creation raises degree and is structurally aligned with a right
regular root action; that stronger basis-level identification is a separate
intertwining theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonionExterior3OperatorTransport
open InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Physics

abbrev CZ := CanonicalZorn
abbrev EndCZ := Module.End ℝ CZ
abbrev SplitCarrier := SplitOctonionCoordinateCarrier
abbrev SplitEnd := Module.End ℝ SplitCarrier

private theorem zorn_left_alt (x y : CZ) :
    (x * x) * y = x * (x * y) :=
  InfoGeometry.Canonical.ZornVectorMatrixExplicit.KingdonSplitOctonion.zorn_left_alternative x y

/-- In an alternative algebra, the symmetrized composition of left regular
operators is exactly left multiplication by the element anticommutator.  The
two associator corrections cancel by skewness in the first two variables. -/
theorem leftRegular_anticommutator (a b : CZ) :
    leftRegular a * leftRegular b + leftRegular b * leftRegular a =
      leftRegular (a * b + b * a) := by
  apply LinearMap.ext
  intro y
  change a * (b * y) + b * (a * y) = (a * b + b * a) * y
  rw [add_mul]
  have hskew :=
    InfoGeometry.Algebra.alternative_associator_swap12 zorn_left_alt b a y
  change
    (b * a) * y - b * (a * y) =
      -((a * b) * y - a * (b * y)) at hskew
  abel

/-- Left regular action of a square-zero element is square-zero in an
alternative algebra. -/
theorem leftRegular_sq_zero_of_sq_zero
    (x : CZ) (hx : x * x = 0) :
    leftRegular x * leftRegular x = 0 := by
  apply LinearMap.ext
  intro y
  change x * (x * y) = 0
  rw [← zorn_left_alt x y, hx]
  simp

/-- Positive circular root channels lift to nilpotent left-regular operators. -/
theorem leftRegular_rootPlus_sq (i : Fin 3) :
    leftRegular (rootPlus i) * leftRegular (rootPlus i) = 0 :=
  leftRegular_sq_zero_of_sq_zero (rootPlus i) (rootPlus_sq i)

/-- Negative circular root channels lift to nilpotent left-regular operators. -/
theorem leftRegular_rootMinus_sq (i : Fin 3) :
    leftRegular (rootMinus i) * leftRegular (rootMinus i) = 0 :=
  leftRegular_sq_zero_of_sq_zero (rootMinus i) (rootMinus_sq i)

/-- The element-level split-octonion CAR lifts exactly to the left-regular
operator algebra. -/
theorem leftRegular_root_CAR (i : Fin 3) :
    leftRegular (rootMinus i) * leftRegular (rootPlus i) +
        leftRegular (rootPlus i) * leftRegular (rootMinus i) =
      (1 : EndCZ) := by
  rw [leftRegular_anticommutator]
  have hanti : rootMinus i * rootPlus i + rootPlus i * rootMinus i = (1 : CZ) := by
    simpa [add_comm] using root_anticommutator i
  rw [hanti]
  apply LinearMap.ext
  intro y
  change (1 : CZ) * y = y
  exact one_zMul y

/-- Native operator CAR pair obtained from the circular split-octonion roots. -/
def leftRegularCARPair (i : Fin 3) : SplitClifford.CARPair EndCZ where
  ann := leftRegular (rootMinus i)
  cre := leftRegular (rootPlus i)
  ann_sq := leftRegular_rootMinus_sq i
  cre_sq := leftRegular_rootPlus_sq i
  anti := leftRegular_root_CAR i

/-- Standard coordinate vector used for the literal exterior mode `i`. -/
def modeVector (i : Fin 3) : V3 := Pi.single i 1

/-- Standard coordinate covector dual to `modeVector i`. -/
def modeCovector (i : Fin 3) : Module.Dual ℝ V3 :=
  (Pi.basisFun ℝ (Fin 3)).coord i

@[simp] theorem modeCovector_modeVector (i : Fin 3) :
    modeCovector i (modeVector i) = 1 := by
  simp [modeCovector, modeVector]

/-- Existing exterior-to-coordinate equivalence, used as the BdG/Fock
operator transport. -/
noncomputable def exteriorCoordinateEquiv : Exterior3 ≃ₗ[ℝ] SplitCarrier :=
  exterior3SplitOctonionCoordinateEquiv

/-- Transported exterior creation operator on the split coordinate carrier. -/
def transportedCreation (i : Fin 3) : SplitEnd :=
  splitCoordinateWedge3 exteriorCoordinateEquiv (modeVector i)

/-- Transported exterior annihilation operator on the split coordinate carrier. -/
def transportedAnnihilation (i : Fin 3) : SplitEnd :=
  splitCoordinateContract3 exteriorCoordinateEquiv (modeCovector i)

/-- The transported literal exterior creation operator remains nilpotent. -/
theorem transportedCreation_sq (i : Fin 3) :
    transportedCreation i * transportedCreation i = 0 :=
  splitCoordinateWedge3_sq exteriorCoordinateEquiv (modeVector i)

/-- The transported literal exterior annihilation operator remains nilpotent. -/
theorem transportedAnnihilation_sq (i : Fin 3) :
    transportedAnnihilation i * transportedAnnihilation i = 0 :=
  splitCoordinateContract3_sq exteriorCoordinateEquiv (modeCovector i)

/-- The transported literal exterior mode satisfies the exact CAR identity. -/
theorem transportedExterior_CAR (i : Fin 3) :
    transportedAnnihilation i * transportedCreation i +
        transportedCreation i * transportedAnnihilation i =
      (1 : SplitEnd) := by
  simpa [transportedAnnihilation, transportedCreation,
    modeCovector_modeVector] using
    (splitCoordinateWedgeContract_CAR exteriorCoordinateEquiv
      (modeVector i) (modeCovector i))

/-- Transported Mathlib exterior CAR pair on split coordinates. -/
def transportedExteriorCARPair (i : Fin 3) : SplitClifford.CARPair SplitEnd where
  ann := transportedAnnihilation i
  cre := transportedCreation i
  ann_sq := transportedAnnihilation_sq i
  cre_sq := transportedCreation_sq i
  anti := transportedExterior_CAR i

/-- The existing transport really is an operator intertwiner, not only a
relation-preserving map. -/
theorem creation_intertwines (i : Fin 3) :
    transportedCreation i ∘ₗ exteriorCoordinateEquiv.toLinearMap =
      exteriorCoordinateEquiv.toLinearMap ∘ₗ exteriorWedge3 (modeVector i) := by
  exact transportEnd_intertwines exteriorCoordinateEquiv
    (exteriorWedge3 (modeVector i))

/-- Annihilation intertwines through the same carrier equivalence. -/
theorem annihilation_intertwines (i : Fin 3) :
    transportedAnnihilation i ∘ₗ exteriorCoordinateEquiv.toLinearMap =
      exteriorCoordinateEquiv.toLinearMap ∘ₗ exteriorContract3 (modeCovector i) := by
  exact transportEnd_intertwines exteriorCoordinateEquiv
    (exteriorContract3 (modeCovector i))

end InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
