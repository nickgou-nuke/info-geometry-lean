/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TracialGNSTomitaClosability
import InfoGeometry.Canonical.GrowingOnsiteTraceGNSFamily
import InfoGeometry.Canonical.FilteredGNSTomitaRealColimit
import InfoGeometry.Canonical.FilteredGNSTomitaModularHilbertCompletion

/-!
# The matrix trace family discharges the native Tomita colimit gate

The normalized trace on each actual Cuntz matrix stage is cyclic.  Its Tomita
core is therefore closable by the norm estimate, and the existing categorical
Tomita operator and modular-form Hilbert completion can be instantiated with no
remaining closability premise.  This does not identify a modular logarithm or
prove a new unbounded polar-decomposition theorem.
-/

noncomputable section
open scoped ComplexOrder

namespace InfoGeometry.Canonical.MatrixTraceTomitaColimit

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
open CStarStateColimit.Native.FilteredGNSTomitaRealColimit
open CStarStateColimit.Native.FilteredGNSTomitaModularHilbertCompletion
open CStarStateColimit.Native.TracialGNSTomitaClosability
open CuntzMatrixTowerInstantiation CantorBernoulliCStarMatrixTraceState
open GrowingOnsiteTraceGNSFamily

private abbrev matrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => (inferInstance : CStarAlgebra (CStarMatrixStage n))
private abbrev matrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => (inferInstance : PartialOrder (CStarMatrixStage n))
private abbrev matrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => (inferInstance : StarOrderedRing (CStarMatrixStage n))
attribute [local instance] matrixStageCStarFamily matrixStageOrderFamily matrixStageStarOrderFamily

/-- The actual finite normalized matrix trace has a closable Tomita core. -/
theorem cstarMatrixTraceState_closable (n : ℕ) :
    IsClosableTomitaCore (cstarMatrixTraceState n) :=
  isClosableTomitaCore_of_tracial (cstarMatrixTraceState n) (cstarTrace_cyclic n)

/-- Every member of the existing compatible matrix trace family satisfies
the gate required by the closed-domain colimit owners. -/
theorem cstarMatrixTraceStateFamily_closable :
    ∀ n, IsClosableTomitaCore (cstarMatrixTraceStateFamily.state n) :=
  cstarMatrixTraceState_closable

/-- The existing real categorical Tomita operator, now with all stage
closability obligations discharged by the normalized matrix trace. -/
def traceTomitaRealColimitOperator :
    ClosedTomitaDomainRealColimit CStarMatrixStage cstarMatrixInductiveSystem
        cstarMatrixTraceStateFamily →ₗ[ℝ]
      GNSRealColimit CStarMatrixStage cstarMatrixInductiveSystem
        cstarMatrixTraceStateFamily :=
  closedTomitaRealColimitOperator CStarMatrixStage cstarMatrixInductiveSystem
    cstarMatrixTraceStateFamily cstarMatrixTraceStateFamily_closable

/-- The concrete colimit operator has the established native stage readback. -/
theorem traceTomitaRealColimitOperator_inclusion (n : ℕ)
    (x : closedTomitaDomain (cstarMatrixTraceState n)) :
    traceTomitaRealColimitOperator
        (closedTomitaDomainRealInclusion CStarMatrixStage cstarMatrixInductiveSystem
          cstarMatrixTraceStateFamily n x) =
      gnsRealInclusion CStarMatrixStage cstarMatrixInductiveSystem
        cstarMatrixTraceStateFamily n
        (closedTomitaOperator (cstarMatrixTraceState n)
          (cstarMatrixTraceState_closable n) x) :=
  closedTomitaRealColimitOperator_inclusion CStarMatrixStage cstarMatrixInductiveSystem
    cstarMatrixTraceStateFamily cstarMatrixTraceStateFamily_closable n x

/-- The genuine modular-form quotient and its Hilbert completion for this
specific infinite matrix tower, without an assumed closability family. -/
abbrev TraceModularHilbertCompletion : Type :=
  ModularHilbertCompletion CStarMatrixStage cstarMatrixInductiveSystem
    cstarMatrixTraceStateFamily cstarMatrixTraceStateFamily_closable

end InfoGeometry.Canonical.MatrixTraceTomitaColimit
