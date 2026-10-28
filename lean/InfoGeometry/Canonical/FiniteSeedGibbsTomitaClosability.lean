/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteMatrixGibbsFaithfulness
import InfoGeometry.Canonical.FiniteFaithfulGNSTomitaClosability
import InfoGeometry.Canonical.FiniteSeedGibbsCStarStates
import InfoGeometry.Canonical.CStarMatrixTowerIsometry
import InfoGeometry.Canonical.FilteredGNSTomitaRealColimit
import InfoGeometry.Canonical.FilteredGNSTomitaModularHilbertCompletion

/-!
# Faithful finite-seed Gibbs states discharge the filtered Tomita gate

At a stage containing the seed, the existing state reads back as the Gibbs
functional of the transported matrix Hamiltonian.  At earlier stages,
compatibility and injectivity of the actual C⋆ matrix inclusions preserve
faithfulness.  Finite-dimensional continuity then proves stage Tomita
closability and instantiates the existing categorical operator and modular-form
completion.  No closability hypothesis is added to the state-family record.
-/

noncomputable section
open scoped ComplexOrder

namespace InfoGeometry.Canonical.FiniteSeedGibbsTomitaClosability

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
open CStarStateColimit.Native.FilteredGNSTomitaRealColimit
open CStarStateColimit.Native.FilteredGNSTomitaModularHilbertCompletion
open CStarStateColimit.Native.FiniteFaithfulGNSTomitaClosability
open CuntzMatrixTowerInstantiation CuntzMatrixAlgebraicStarColimit
open CantorBernoulliCStarMatrixTraceState CStarMatrixTowerIsometry
open FiniteMatrixGibbsFaithfulness AlgebraicKMSStateColimit

private abbrev matrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => (inferInstance : CStarAlgebra (CStarMatrixStage n))
private abbrev matrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => (inferInstance : PartialOrder (CStarMatrixStage n))
private abbrev matrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => (inferInstance : StarOrderedRing (CStarMatrixStage n))
attribute [local instance] matrixStageCStarFamily matrixStageOrderFamily matrixStageStarOrderFamily

variable {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ)

/-- Every stage containing the seed has the faithful transported Gibbs state. -/
theorem finiteSeedStageState_later_faithful {n : ℕ} (hkn : k ≤ n)
    (A : CStarMatrixStage n) :
    (finiteSeedStageState H hH β n).functional (star A * A) = 0 ↔ A = 0 := by
  constructor
  · intro hz
    let Hn : MatrixStage n := rawMap hkn H
    have hHn : Hn.IsHermitian := by
      change star (rawMap hkn H) = rawMap hkn H
      rw [← map_star]
      exact congrArg (rawMap hkn) hH
    rw [finiteSeedStageState_apply, map_mul, map_star,
      finiteSeedGibbs_later_stage hkn H Hn hH hHn rfl β] at hz
    have ha := (gibbsFunctional_star_mul_self_eq_zero_iff Hn hHn β
      ((CStarMatrix.ofMatrixStarAlgEquiv).symm A)).mp hz
    have hA := congrArg
      (CStarMatrix.ofMatrixStarAlgEquiv :
        MatrixStage n ≃⋆ₐ[ℂ] CStarMatrixStage n) ha
    simpa only [StarAlgEquiv.apply_symm_apply, map_zero] using hA
  · rintro rfl
    simp only [star_zero, zero_mul, map_zero]

/-- The actual finite-seed state is faithful at every stage, including n < k. -/
theorem finiteSeedStageState_faithful (n : ℕ) (A : CStarMatrixStage n) :
    (finiteSeedStageState H hH β n).functional (star A * A) = 0 ↔ A = 0 := by
  constructor
  · intro hz
    let m := max k n
    have hkm : k ≤ m := le_max_left k n
    have hnm : n ≤ m := le_max_right k n
    have hz' : (finiteSeedStageState H hH β m).functional
        (star (cstarConcreteMap hnm A) * cstarConcreteMap hnm A) = 0 := by
      rw [← map_star, ← map_mul, finiteSeedStageState_transition]
      exact hz
    have hA := (finiteSeedStageState_later_faithful H hH β hkm
      (cstarConcreteMap hnm A)).mp hz'
    apply cstarConcreteMap_injective hnm
    simpa only [map_zero] using hA
  · rintro rfl
    simp only [star_zero, zero_mul, map_zero]

/-- The finite-dimensional theorem applies to the native C⋆ type-copy, not a
new matrix norm or a scalar proxy. -/
theorem finiteSeedStageState_closable (n : ℕ) :
    IsClosableTomitaCore (finiteSeedStageState H hH β n) := by
  letI : FiniteDimensional ℂ (CStarMatrixStage n) :=
    (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage n ≃⋆ₐ[ℂ]
      CStarMatrixStage n).toAlgEquiv.toLinearEquiv.finiteDimensional
  exact isClosableTomitaCore_of_finiteDimensional_faithful
    (finiteSeedStageState H hH β n)
    (fun A hA => (finiteSeedStageState_faithful H hH β n A).mp hA)

/-- All closability gates of the already constructed compatible family are
discharged by its actual matrix Gibbs density. -/
theorem finiteSeedCompatibleStageStates_closable :
    ∀ n, IsClosableTomitaCore ((finiteSeedCompatibleStageStates H hH β).state n) :=
  finiteSeedStageState_closable H hH β

/-- The existing categorical Tomita operator for the proved Gibbs family. -/
def finiteSeedTomitaRealColimitOperator :
    ClosedTomitaDomainRealColimit CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β) →ₗ[ℝ]
      GNSRealColimit CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β) :=
  closedTomitaRealColimitOperator CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates H hH β)
    (finiteSeedCompatibleStageStates_closable H hH β)

/-- The concrete categorical operator agrees with its genuine closed stage
operators under the existing inclusions. -/
theorem finiteSeedTomitaRealColimitOperator_inclusion (n : ℕ)
    (x : closedTomitaDomain (finiteSeedStageState H hH β n)) :
    finiteSeedTomitaRealColimitOperator H hH β
        (closedTomitaDomainRealInclusion CStarMatrixStage cstarMatrixInductiveSystem
          (finiteSeedCompatibleStageStates H hH β) n x) =
      gnsRealInclusion CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β) n
        (closedTomitaOperator (finiteSeedStageState H hH β n)
          (finiteSeedStageState_closable H hH β n) x) :=
  closedTomitaRealColimitOperator_inclusion CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates H hH β)
    (finiteSeedCompatibleStageStates_closable H hH β) n x

/-- The native modular-form Hilbert completion for the finite-seed state on
the infinite matrix tower, with its actual proved stage closability. -/
abbrev FiniteSeedModularHilbertCompletion : Type :=
  ModularHilbertCompletion CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates H hH β)
    (finiteSeedCompatibleStageStates_closable H hH β)

end InfoGeometry.Canonical.FiniteSeedGibbsTomitaClosability
