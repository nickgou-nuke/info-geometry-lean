/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ThermodynamicSL2OperatorLift
import InfoGeometry.Clifford.Cl11StarAlgebraColimit

/-!
# Peirce operator powers in the `Cl(1,1)` algebraic tensor-tower limit

The Peirce-adapted even/odd power identities are first proved over an
arbitrary coefficient ring. This bridge applies the canonical finite-stage
inclusion into the existing algebraic direct limit, preserving the ordered
corner products. It does not identify the algebraic limit with an analytic
completion.
-/

noncomputable section

namespace InfoGeometry.Canonical.PeirceOperatorCl11TowerBridge

open InfoGeometry.OperatorAlgebra.ThermodynamicSL2OperatorLift
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11StarAlgebraColimit

/-- The Peirce-odd matrix with coefficients from finite tower stage `n`,
viewed in matrices over the algebraic tower limit. -/
def peirceGeneratorInLimit (n : ℕ) (a c : Stage n) : OperatorMatrix Limit :=
  (ofStage n).mapMatrix (peirceOffDiagonalGenerator a c)

/-- The finite-stage ordered diagonal corner powers viewed in the limit. -/
def peirceEvenPowerInLimit (n : ℕ) (a c : Stage n) (k : ℕ) :
    OperatorMatrix Limit :=
  (ofStage n).mapMatrix (peirceEvenPower a c k)

/-- The even-power decomposition survives the canonical finite-stage map into
the algebraic infinite tensor-tower carrier. -/
theorem peirceGeneratorInLimit_pow_even (n : ℕ) (a c : Stage n) (k : ℕ) :
    peirceGeneratorInLimit n a c ^ (2 * k) = peirceEvenPowerInLimit n a c k := by
  change ((ofStage n).mapMatrix (peirceOffDiagonalGenerator a c)) ^ (2 * k) = _
  calc
    _ = (ofStage n).mapMatrix
        (peirceOffDiagonalGenerator a c ^ (2 * k)) :=
          (map_pow ((ofStage n).mapMatrix) _ _).symm
    _ = (ofStage n).mapMatrix (peirceEvenPower a c k) :=
          congrArg ((ofStage n).mapMatrix)
            (peirceOffDiagonalGenerator_pow_even a c k)
    _ = peirceEvenPowerInLimit n a c k := rfl

/-- The odd-power decomposition also survives in the tower limit, with the
same right multiplication order as at the finite stage. -/
theorem peirceGeneratorInLimit_pow_odd (n : ℕ) (a c : Stage n) (k : ℕ) :
    peirceGeneratorInLimit n a c ^ (2 * k + 1) =
      peirceEvenPowerInLimit n a c k * peirceGeneratorInLimit n a c := by
  change ((ofStage n).mapMatrix (peirceOffDiagonalGenerator a c)) ^ (2 * k + 1) = _
  calc
    _ = (ofStage n).mapMatrix
        (peirceOffDiagonalGenerator a c ^ (2 * k + 1)) :=
          (map_pow ((ofStage n).mapMatrix) _ _).symm
    _ = (ofStage n).mapMatrix
        (peirceEvenPower a c k * peirceOffDiagonalGenerator a c) :=
          congrArg ((ofStage n).mapMatrix)
            (peirceOffDiagonalGenerator_pow_odd a c k)
    _ = peirceEvenPowerInLimit n a c k * peirceGeneratorInLimit n a c :=
          (ofStage n).mapMatrix.map_mul _ _

/-- A finite-stage element is faithfully retained by the tower colimit, so
these transported identities do not collapse distinct stage coefficients. -/
theorem ofStage_injective_at_finite_head (n : ℕ) :
    Function.Injective (ofStage n) :=
  ofStage_injective n

end InfoGeometry.Canonical.PeirceOperatorCl11TowerBridge
