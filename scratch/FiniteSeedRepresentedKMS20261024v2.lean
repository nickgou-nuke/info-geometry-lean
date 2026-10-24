/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DenseTwistedCyclicity
import InfoGeometry.Canonical.FilteredGNSVacuumState
import InfoGeometry.Canonical.FiniteSeedGibbsCStarStates

/-!
# Finite-seed twisted cyclicity on the represented C⋆ closure

The finite-seed density is mapped as an actual unit. Algebraic Gibbs readback
and density of the represented algebraic colimit extend the twisted product
identity to the entire closure. This is not an analytic KMS strip theorem or
a claim that conjugation by a positive density preserves star.
-/
noncomputable section
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

namespace CStarStateColimit.Native.FilteredGNSRepresentedKMS

open FilteredStarAlgebraDirectLimit FilteredGNSRepresentedCStarClosure
open FilteredGNSVacuumReadback FilteredGNSVacuumState

universe u
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

attribute [local instance] FilteredGNSVacuumState.representedSpectralOrder
  FilteredGNSVacuumState.representedSpectralStarOrderedRing

/-- A property of the actual normalized state and mapped density unit.
No state, invariance certificate, or twisted identity is assumed as data. -/
def representedVacuumTwistedCyclic (v : I)
    (δraw : (AlgebraicStarDirectLimit Stage sys)ˣ) : Prop :=
  let ρ := representedVacuumState Stage sys ω v
  let δ := Units.map (algebraicColimitToRepresentedClosure Stage sys ω).toMonoidHom δraw
  ∀ X Y : representedCStarClosure Stage sys ω,
    ρ.functional (X * Y) = ρ.functional (Y * ((δ : _) * X * (↑δ⁻¹ : _)))

/-- Extend a dense algebraic identity using the existing continuous vacuum
functional. The concrete finite-seed consumer below proves the premise. -/
theorem representedVacuumTwistedCyclic_of_algebraic (v : I)
    (δraw : (AlgebraicStarDirectLimit Stage sys)ˣ)
    (h : ∀ x y : AlgebraicStarDirectLimit Stage sys,
      representedVacuumFunctional Stage sys ω v
        (algebraicColimitToRepresentedClosure Stage sys ω (x * y)) =
      representedVacuumFunctional Stage sys ω v
        (algebraicColimitToRepresentedClosure Stage sys ω
          (y * ((δraw : _) * x * (↑δraw⁻¹ : _))))) :
    representedVacuumTwistedCyclic Stage sys ω v δraw := by
  let J := algebraicColimitToRepresentedClosure Stage sys ω
  let φ := representedVacuumFunctional Stage sys ω v
  let δ := Units.map J.toMonoidHom δraw
  change ∀ X Y : representedCStarClosure Stage sys ω,
    φ (X * Y) = φ (Y * ((δ : _) * X * (↑δ⁻¹ : _)))
  exact InfoGeometry.OperatorAlgebra.DenseTwistedCyclicity.twisted_cyclicity_of_denseRange
    J.toAlgHom.toRingHom
    (algebraicColimitToRepresentedClosure_denseRange Stage sys ω)
    φ φ.continuous δraw h

end CStarStateColimit.Native.FilteredGNSRepresentedKMS

namespace InfoGeometry.Canonical.FiniteSeedRepresentedKMS

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open CStarStateColimit.Native.FilteredGNSVacuumReadback
open CStarStateColimit.Native.FilteredGNSRepresentedKMS
open CuntzMatrixTowerInstantiation CuntzMatrixAlgebraicStarColimit
open CantorBernoulliCStarMatrixTraceState FiniteMatrixGibbsFunctional
open AlgebraicKMSStateColimit

private abbrev matrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => (inferInstance : CStarAlgebra (CStarMatrixStage n))
private abbrev matrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => (inferInstance : PartialOrder (CStarMatrixStage n))
private abbrev matrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => (inferInstance : StarOrderedRing (CStarMatrixStage n))
attribute [local instance] matrixStageCStarFamily matrixStageOrderFamily matrixStageStarOrderFamily

/-- The native type-copy equivalence followed by the existing raw stage injection. -/
def matrixStageReadback (n : ℕ) :
    CStarMatrixStage n →⋆ₐ[ℂ] CuntzMatrixAlgebraicStarColimit.Carrier :=
  (stageInjection n).comp (CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)

/-- Reverse comparison of the two existing algebraic colimits. -/
def cstarColimitToMatrixColimit :
    AlgebraicStarDirectLimit CStarMatrixStage cstarMatrixInductiveSystem →⋆ₐ[ℂ]
      CuntzMatrixAlgebraicStarColimit.Carrier :=
  liftStarAlgHom CStarMatrixStage cstarMatrixInductiveSystem matrixStageReadback (by
    intro i j hij x
    change stageInjection j (CStarMatrix.ofMatrixStarAlgEquiv.symm (cstarConcreteMap hij x)) =
      stageInjection i (CStarMatrix.ofMatrixStarAlgEquiv.symm x)
    rw [cstarConcreteMap_toMatrixStage]
    exact stageInjection_transition hij (CStarMatrix.ofMatrixStarAlgEquiv.symm x))

@[simp] theorem cstarColimitToMatrixColimit_stage (n : ℕ) (x : CStarMatrixStage n) :
    cstarColimitToMatrixColimit
      (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem n x) =
        stageInjection n (CStarMatrix.ofMatrixStarAlgEquiv.symm x) := rfl

/-- The seed Gibbs unit in the C⋆-stage algebraic direct limit. -/
def seedDensityUnit {k : ℕ} (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) :
    (AlgebraicStarDirectLimit CStarMatrixStage cstarMatrixInductiveSystem)ˣ :=
  Units.map
    (((algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem k).comp
      CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom).toMonoidHom)
    (gibbsDensityUnit H hH β)

@[simp] theorem seedDensityUnit_readback {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) :
    Units.map cstarColimitToMatrixColimit.toMonoidHom (seedDensityUnit H hH β) =
      stageUnitToColimit k (gibbsDensityUnit H hH β) := by
  apply Units.ext
  change stageInjection k
    (CStarMatrix.ofMatrixStarAlgEquiv.symm
      (CStarMatrix.ofMatrixStarAlgEquiv (↑(gibbsDensityUnit H hH β) : MatrixStage k))) =
    stageInjection k (↑(gibbsDensityUnit H hH β) : MatrixStage k)
  rw [StarAlgEquiv.symm_apply_apply]

/-- Readback on the entire algebraic dense image, for every vacuum stage. -/
theorem finiteSeedVacuum_algebraic_readback {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) (v : ℕ)
    (x : AlgebraicStarDirectLimit CStarMatrixStage cstarMatrixInductiveSystem) :
    representedVacuumFunctional CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates H hH β) v
      (algebraicColimitToRepresentedClosure CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β) x) =
    normalizedDeltaWeightedFunctional (stageUnitToColimit k (gibbsDensityUnit H hH β))
      (cstarColimitToMatrixColimit x) := by
  induction x using DirectLimit.induction with
  | _ n a =>
    have hj : algebraicColimitToRepresentedClosure CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β)
        (algebraicStarDirectLimitOf CStarMatrixStage cstarMatrixInductiveSystem n a) =
        ⟨globalStageRepresentationStarAlgHom CStarMatrixStage cstarMatrixInductiveSystem
          (finiteSeedCompatibleStageStates H hH β) n a,
          globalStageRepresentation_mem_representedCStarClosure CStarMatrixStage
            cstarMatrixInductiveSystem (finiteSeedCompatibleStageStates H hH β) n a⟩ := by
      apply Subtype.ext
      exact algebraicColimitGNSRepresentation_of CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β) n a
    have hstage := representedVacuumFunctional_stage CStarMatrixStage
      cstarMatrixInductiveSystem (finiteSeedCompatibleStageStates H hH β) v n a
    have hread := finiteSeedStageState_apply H hH β n a
    exact (congrArg
      (representedVacuumFunctional CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β) v) hj).trans
      (hstage.trans hread)

/-- Actual completed-state twisted identity for every Hermitian finite seed.
No traciality, completed KMS identity, or state invariance is a hypothesis. -/
theorem finiteSeed_representedVacuumTwistedCyclic {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) (v : ℕ) :
    representedVacuumTwistedCyclic CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates H hH β) v (seedDensityUnit H hH β) := by
  refine representedVacuumTwistedCyclic_of_algebraic CStarMatrixStage
    cstarMatrixInductiveSystem (finiteSeedCompatibleStageStates H hH β)
    v (seedDensityUnit H hH β) ?_
  intro x y
  rw [finiteSeedVacuum_algebraic_readback H hH β v (x * y),
    finiteSeedVacuum_algebraic_readback H hH β v
      (y * ((↑(seedDensityUnit H hH β)) * x * (↑((seedDensityUnit H hH β)⁻¹))))]
  have hd := congrArg Units.val (seedDensityUnit_readback H hH β)
  have hi := congrArg (fun u => ((u⁻¹ : CuntzMatrixAlgebraicStarColimit.Carrierˣ) :
    CuntzMatrixAlgebraicStarColimit.Carrier)) (seedDensityUnit_readback H hH β)
  change cstarColimitToMatrixColimit (↑(seedDensityUnit H hH β)) = _ at hd
  change cstarColimitToMatrixColimit (↑((seedDensityUnit H hH β)⁻¹)) = _ at hi
  simp only [map_mul, hd, hi]
  exact normalizedDeltaWeightedFunctional_kms
    (stageUnitToColimit k (gibbsDensityUnit H hH β))
    (cstarColimitToMatrixColimit x) (cstarColimitToMatrixColimit y)

end InfoGeometry.Canonical.FiniteSeedRepresentedKMS
