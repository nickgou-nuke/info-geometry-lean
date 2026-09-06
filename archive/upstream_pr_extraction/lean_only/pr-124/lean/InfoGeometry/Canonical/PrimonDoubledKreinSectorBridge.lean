import InfoGeometry.Algebra.PrimonColimitAlgebra
import InfoGeometry.Krein.DoubledSpaceMatrixClockBridge
import InfoGeometry.Krein.DoubledSpaceQutritMobiusBridge

/-!
# Primon colimit actions on the native doubled Krein carrier

This file is deliberately an interface theorem, not a second colimit.  A
stage-wise representation into the already existing doubled carrier is
packaged together with its bonding square; `DirectLimit.lift` then produces
the unique action of `PrimonUHFAlgebra`.  The four dynamical labels and the
two thermodynamic regimes are bookkeeping for readouts, not identifications
of their distinct algebraic laws.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimonDoubledKreinSectorBridge

open InfoGeometry.Algebra.PrimonColimitAlgebra
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Krein

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

abbrev DoubledEnd := DoubledSpace E →L[ℝ] DoubledSpace E

inductive FlowSector
  | parabolic
  | hyperbolic
  | elliptic
  | loxodromic
deriving DecidableEq, Repr

inductive ThermodynamicRegime
  | equilibrium
  | nonEquilibrium
deriving DecidableEq, Repr

/-- A genuine stage representation together with its colimit square. -/
structure CompatibleStageAction where
  map : ∀ n, MatrixStage n →+* DoubledEnd (E := E)
  bond : ∀ n (A : MatrixStage n),
    map (n + 1) (matrixBond n A) = map n A

namespace CompatibleStageAction

variable (A : CompatibleStageAction (E := E))

/-- The unique action induced on the existing Primon direct-limit carrier. -/
noncomputable def colimitMap (A : CompatibleStageAction (E := E)) :
    PrimonUHFAlgebra →+* DoubledEnd (E := E) :=
  directLimitLift matrixBond A.map (by
    intro n x
    exact A.bond n x)

@[simp] theorem colimitMap_stage (A : CompatibleStageAction (E := E))
    (n : ℕ) (x : MatrixStage n) :
    colimitMap A (toColimit n x) = A.map n x := by
  apply directLimitLift_of

theorem colimitMap_bond (A : CompatibleStageAction (E := E))
    (n : ℕ) (x : MatrixStage n) :
    colimitMap A (toColimit (n + 1) (matrixBond n x)) =
      colimitMap A (toColimit n x) := by
  rw [colimitMap_stage, colimitMap_stage, A.bond]

end CompatibleStageAction

/-! Sector and regime labels carried by a doubled-Krein readout. -/

structure SectorReadout where
  action : CompatibleStageAction (E := E)
  sector : FlowSector
  regime : ThermodynamicRegime

namespace SectorReadout

variable (R : SectorReadout (E := E))

noncomputable abbrev colimitAction (R : SectorReadout (E := E)) :
    PrimonUHFAlgebra →+* DoubledEnd (E := E) :=
  CompatibleStageAction.colimitMap R.action

@[simp] theorem colimitAction_stage (n : ℕ) (x : MatrixStage n) :
    colimitAction R (toColimit n x) = R.action.map n x :=
  CompatibleStageAction.colimitMap_stage R.action n x

theorem colimitAction_bond (n : ℕ) (x : MatrixStage n) :
    colimitAction R (toColimit (n + 1) (matrixBond n x)) =
      colimitAction R (toColimit n x) :=
  CompatibleStageAction.colimitMap_bond R.action n x

end SectorReadout

end InfoGeometry.Canonical.PrimonDoubledKreinSectorBridge
