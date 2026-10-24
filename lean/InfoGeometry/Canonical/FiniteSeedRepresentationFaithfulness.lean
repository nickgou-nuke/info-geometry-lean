/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredGNSMatrixFaithfulness
import InfoGeometry.Canonical.FiniteSeedRepresentedRealTime

/-! Faithfulness of the actual finite-seed representation.
The existing global GNS vacuum proves closure nontriviality; matrix simplicity
then proves injectivity of the native seed homomorphism. -/
noncomputable section
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

namespace InfoGeometry.Canonical.FiniteSeedRepresentationFaithfulness

open CStarStateColimit.Native
open FilteredGNSHilbertColimit FilteredGNSHilbertNontrivial
open FilteredGNSRepresentedCStarClosure
open CantorBernoulliCStarMatrixTraceState CuntzMatrixTowerInstantiation
open AlgebraicKMSStateColimit FiniteSeedRepresentedRealTime

universe u

/-- Identity and zero in the actual closure are separated by an existing global vacuum. -/
theorem representedClosure_nontrivial_at
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys) (i : I) :
    Nontrivial (representedCStarClosure Stage sys ω) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  apply globalGNSVacuum_ne_zero Stage sys ω i
  have hv := congrArg
    (fun T : representedCStarClosure Stage sys ω =>
      T.val (globalGNSVacuum Stage sys ω i)) h
  simpa using hv

private abbrev stageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun _n => inferInstance
private abbrev stageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun _n => inferInstance
private abbrev stageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun _n => inferInstance
attribute [local instance] stageCStarFamily stageOrderFamily stageStarOrderFamily

/-- Matrix simplicity proves injectivity of the actual seed homomorphism. -/
theorem seedStageHom_injective {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) :
    Function.Injective (seedStageHom H hH β) := by
  let : Nontrivial (representedCStarClosure CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates H hH β)) :=
    representedClosure_nontrivial_at CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates H hH β) k
  exact RingHom.injective (seedStageHom H hH β).toAlgHom.toRingHom

end InfoGeometry.Canonical.FiniteSeedRepresentationFaithfulness
