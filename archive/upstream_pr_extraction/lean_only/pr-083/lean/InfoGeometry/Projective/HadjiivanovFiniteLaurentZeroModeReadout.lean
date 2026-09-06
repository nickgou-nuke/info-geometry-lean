import InfoGeometry.Projective.HadjiivanovFiniteLaurentModeTower
import InfoGeometry.Projective.HadjiivanovLogConnectionReadoutBridge

/-!
# Central Laurent-mode residue readout

The central coordinate of the symmetric stage `n` represents Laurent degree
zero.  Consequently the Euler summand vanishes there and the finite logarithmic
connection reads exactly as the fiber residue.  On the native rank-two fiber
this is the existing Virasoro `L₀` Jordan cell.

This is a finite coefficient identity, not a monodromy-as-holonomy theorem.
-/

namespace InfoGeometry.Projective.HadjiivanovFiniteLaurentZeroModeReadout

open HadjiivanovLogConnectionBridge
open HadjiivanovLogConnectionRankTwoBridge
open HadjiivanovLogConnectionReadoutBridge
open HadjiivanovFiniteLaurentModeTower
open InfoGeometry.Clifford.LogCftMonodromy

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Coordinate representing Laurent degree zero in the symmetric window
`[-n,n]`. -/
def centralModeIndex (n : ℕ) : Fin (2 * n + 1) :=
  ⟨n, by omega⟩

@[simp] theorem modeDegree_centralModeIndex (n : ℕ) :
    modeDegree n (centralModeIndex n) = 0 := by
  simp [modeDegree, centralModeIndex]

/-- Linear extraction of the central Laurent coefficient. -/
def centralModeReadout (n : ℕ) :
    FiniteModeSection n V →ₗ[ℂ] V where
  toFun x := x (centralModeIndex n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem centralModeReadout_apply
    (n : ℕ) (x : FiniteModeSection n V) :
    centralModeReadout n x = x (centralModeIndex n) := rfl

/-- At Laurent degree zero the finite connection is precisely its residue
operator. -/
theorem centralModeReadout_finiteModeConnection
    (R : LogResidue V) (n : ℕ) (x : FiniteModeSection n V) :
    centralModeReadout n (finiteModeConnection R n x) =
      residueOperator R (centralModeReadout n x) := by
  simp [centralModeReadout, finiteModeConnection_apply]

theorem centralModeReadout_finiteModeConnection_comp
    (R : LogResidue V) (n : ℕ) :
    (centralModeReadout n).comp (finiteModeConnection R n) =
      (residueOperator R).comp (centralModeReadout n) := by
  apply LinearMap.ext
  intro x
  exact centralModeReadout_finiteModeConnection R n x

/-- On the native rank-two LCFT fiber, the central finite-mode connection is
action by the existing Virasoro Jordan cell. -/
theorem rankTwo_centralModeReadout_finiteModeConnection
    (h : ℂ) (n : ℕ) (x : FiniteModeSection n RankTwoFiber) :
    centralModeReadout n (finiteModeConnection (rankTwoLogResidue h) n x) =
      (virasoroL0Cell h).mulVec (centralModeReadout n x) := by
  rw [centralModeReadout_finiteModeConnection]
  rw [rankTwo_residueOperator_eq_mulVecLin, Matrix.mulVecLin_apply]

/-- The one-wrap readout on the same central rank-two fiber is the native
Hadjiivanov monodromy matrix action. -/
theorem rankTwo_centralResidueMonodromyReadout
    (h : ℂ) (n : ℕ) (x : FiniteModeSection n RankTwoFiber) :
    residueMonodromyEnd (rankTwoLogResidue h) (centralModeReadout n x) =
      (hadjiivanovMonodromy h).mulVec (centralModeReadout n x) := by
  change residueMonodromyEnd (rankTwoLogResidue h) (centralModeReadout n x) =
    Matrix.mulVecLin (hadjiivanovMonodromy h) (centralModeReadout n x)
  rw [rankTwo_residueMonodromyEnd_eq_mulVecLin]

end

end InfoGeometry.Projective.HadjiivanovFiniteLaurentZeroModeReadout
