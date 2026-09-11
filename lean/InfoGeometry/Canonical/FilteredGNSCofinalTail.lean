import InfoGeometry.Canonical.FilteredGNSTailStarRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Cofinal GNS tails inside the global filtered Hilbert colimit

Every stage vector in a filtered GNS system transports to a stage above any
fixed base index.  Consequently, restricting the canonical stage images to an
upper tail does not change their dense span in the global completed colimit.
This is the first step toward the canonical unitary equivalence between a
cofinal-tail Hilbert colimit and the global filtered GNS Hilbert colimit.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSCofinalTail

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSTomitaModularForm
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSTailRepresentation
open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
open InfoGeometry.Canonical.FilteredIsometricInnerProductDirectLimit
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      Stage sys)

local notation "G" =>
  GNSStage Stage sys ω
local notation "GS" =>
  filteredGNSIsometricDirectSystem Stage sys ω
local notation "E" =>
  TailGNSStage Stage sys ω
local notation "S" =>
  tailGNSIsometricDirectSystem Stage sys ω

/-- The images of stages above any fixed base index remain dense in the
global filtered GNS Hilbert colimit. -/
theorem dense_iUnion_range_upper_gnsStageToHilbertColimit
    (i₀ : I) :
    Dense
      (⋃ j : UpperIndex i₀,
        Set.range
          (gnsStageToHilbertColimit Stage sys ω j.1)) := by
  apply (dense_iUnion_range_gnsStageToHilbertColimit
    Stage sys ω).mono
  intro z hz
  rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
  rcases hi with ⟨x, rfl⟩
  obtain ⟨j, hi_j, hi₀_j⟩ := exists_ge_ge i i₀
  apply Set.mem_iUnion.mpr
  refine ⟨⟨j, hi₀_j⟩, ?_⟩
  refine ⟨filteredGNSMap Stage sys ω hi_j x, ?_⟩
  exact
    gnsStageToHilbertColimit_transition
      Stage sys ω hi_j x

/-- A tail stage followed by its canonical inclusion into the global
algebraic GNS colimit, viewed over the real scalar ring used by
`Module.DirectLimit`. -/
def tailStageToGlobalRealMap
    (i₀ : I) (j : UpperIndex i₀) :
    E i₀ j →ₗ[ℝ]
      AlgebraicGNSHilbertColimit Stage sys ω where
  toFun :=
    stageToDirectLimitLinearMap G GS j.1
  map_add' := by
    intro x y
    exact map_add _ x y
  map_smul' := by
    intro r x
    exact
      (stageToDirectLimitLinearMap G GS j.1).map_smul_of_tower r x

/-- The tail-stage maps form a cocone into the global algebraic colimit. -/
theorem tailStageToGlobalRealMap_compatible
    (i₀ : I)
    (j k : UpperIndex i₀) (hjk : j ≤ k)
    (x : E i₀ j) :
    tailStageToGlobalRealMap Stage sys ω i₀ k
        (realTransition (E i₀) (S i₀) hjk x) =
      tailStageToGlobalRealMap Stage sys ω i₀ j x := by
  change
    stageToDirectLimitLinearMap G GS k.1
        (filteredGNSLinearIsometry Stage sys ω hjk x) =
      stageToDirectLimitLinearMap G GS j.1 x
  exact stageToDirectLimitLinearMap_transition G GS hjk x

/-- Canonical real-linear descent from the algebraic upper-tail colimit to
the global algebraic GNS colimit. -/
def tailAlgebraicToGlobalReal
    (i₀ : I) :
    RealDirectLimit (E i₀) (S i₀) →ₗ[ℝ]
      AlgebraicGNSHilbertColimit Stage sys ω :=
  Module.DirectLimit.lift
    ℝ (UpperIndex i₀) (E i₀)
    (fun _ _ hjk => realTransition (E i₀) (S i₀) hjk)
    (tailStageToGlobalRealMap Stage sys ω i₀)
    (tailStageToGlobalRealMap_compatible Stage sys ω i₀)

@[simp] theorem tailAlgebraicToGlobalReal_of
    (i₀ : I) (j : UpperIndex i₀) (x : E i₀ j) :
    tailAlgebraicToGlobalReal Stage sys ω i₀
        (Module.DirectLimit.of
          ℝ (UpperIndex i₀) (E i₀)
          (fun _ _ hjk => realTransition (E i₀) (S i₀) hjk)
          j x) =
      stageToDirectLimitLinearMap G GS j.1 x := by
  simpa only [tailStageToGlobalRealMap] using
    (Module.DirectLimit.lift_of
      (g := tailStageToGlobalRealMap Stage sys ω i₀)
      (tailStageToGlobalRealMap_compatible
        Stage sys ω i₀)
      (i := j) x)

/-- The cofinal-tail descent is complex linear because both colimits inherit
their complex actions from the same stage system. -/
def tailAlgebraicToGlobal
    (i₀ : I) :
    RealDirectLimit (E i₀) (S i₀) →ₗ[ℂ]
      AlgebraicGNSHilbertColimit Stage sys ω where
  toFun := tailAlgebraicToGlobalReal Stage sys ω i₀
  map_add' := (tailAlgebraicToGlobalReal Stage sys ω i₀).map_add
  map_smul' := by
    intro c z
    induction z using Module.DirectLimit.induction_on with
    | ih j x =>
        simp only [complex_smul_of,
          tailAlgebraicToGlobalReal_of, map_smul]
        rfl

@[simp] theorem tailAlgebraicToGlobal_of
    (i₀ : I) (j : UpperIndex i₀) (x : E i₀ j) :
    tailAlgebraicToGlobal Stage sys ω i₀
        (stageToDirectLimitLinearMap (E i₀) (S i₀) j x) =
      stageToDirectLimitLinearMap G GS j.1 x :=
  tailAlgebraicToGlobalReal_of Stage sys ω i₀ j x

/-- The algebraic cofinal-tail descent preserves the norm exactly. -/
theorem tailAlgebraicToGlobal_norm
    (i₀ : I)
    (z : RealDirectLimit (E i₀) (S i₀)) :
    ‖tailAlgebraicToGlobal Stage sys ω i₀ z‖ = ‖z‖ := by
  induction z using Module.DirectLimit.induction_on with
  | ih j x =>
      change
        ‖tailAlgebraicToGlobal Stage sys ω i₀
            (stageToDirectLimitLinearMap (E i₀) (S i₀) j x)‖ =
          ‖stageToDirectLimitLinearMap (E i₀) (S i₀) j x‖
      rw [tailAlgebraicToGlobal_of]
      change
        ‖stageToDirectLimitLinearIsometry G GS j.1 x‖ =
          ‖stageToDirectLimitLinearIsometry (E i₀) (S i₀) j x‖
      rw [(stageToDirectLimitLinearIsometry G GS j.1).norm_map,
        (stageToDirectLimitLinearIsometry
          (E i₀) (S i₀) j).norm_map]

/-- Canonical algebraic linear isometry from a cofinal GNS tail to the global
algebraic GNS colimit. -/
def tailAlgebraicToGlobalLinearIsometry
    (i₀ : I) :
    RealDirectLimit (E i₀) (S i₀) →ₗᵢ[ℂ]
      AlgebraicGNSHilbertColimit Stage sys ω :=
  LinearIsometry.mk
    (tailAlgebraicToGlobal Stage sys ω i₀)
    (tailAlgebraicToGlobal_norm Stage sys ω i₀)

/-- Continuous extension of the algebraic cofinal-tail isometry to the two
Hilbert completions. -/
def tailHilbertToGlobalCLM
    (i₀ : I) :
    HilbertDirectLimit (E i₀) (S i₀) →L[ℂ]
      GNSHilbertColimit Stage sys ω :=
  (tailAlgebraicToGlobalLinearIsometry
    Stage sys ω i₀).toContinuousLinearMap.completion

theorem tailHilbertToGlobal_isometry
    (i₀ : I) :
    Isometry (tailHilbertToGlobalCLM Stage sys ω i₀) := by
  change
    Isometry
      ((tailAlgebraicToGlobalLinearIsometry
        Stage sys ω i₀).toContinuousLinearMap.completion :
        HilbertDirectLimit (E i₀) (S i₀) →
          GNSHilbertColimit Stage sys ω)
  rw [ContinuousLinearMap.coe_completion]
  exact
    (tailAlgebraicToGlobalLinearIsometry
      Stage sys ω i₀).isometry.completion_map

/-- The completed cofinal map bundled as a complex linear isometry. -/
def tailHilbertToGlobalLinearIsometry
    (i₀ : I) :
    HilbertDirectLimit (E i₀) (S i₀) →ₗᵢ[ℂ]
      GNSHilbertColimit Stage sys ω :=
  LinearIsometry.mk
    (tailHilbertToGlobalCLM Stage sys ω i₀)
    (fun x => by
      have h :=
        (tailHilbertToGlobal_isometry
          Stage sys ω i₀).dist_eq x 0
      simpa [dist_zero] using h)

/-- The completed cofinal map sends every tail-stage vector to the identical
global stage image. -/
@[simp] theorem tailHilbertToGlobal_stage
    (i₀ : I) (j : UpperIndex i₀) (x : E i₀ j) :
    tailHilbertToGlobalCLM Stage sys ω i₀
        (stageToHilbertDirectLimit (E i₀) (S i₀) j x) =
      gnsStageToHilbertColimit Stage sys ω j.1 x := by
  rw [stageToHilbertDirectLimit_apply]
  unfold tailHilbertToGlobalCLM
  unfold directLimitToCompletion
  rw [ContinuousLinearMap.completion_apply_coe]
  change
    UniformSpace.Completion.coe'
        (tailAlgebraicToGlobal Stage sys ω i₀
          (stageToDirectLimitLinearMap (E i₀) (S i₀) j x)) =
      UniformSpace.Completion.coe'
        (stageToDirectLimitLinearMap G GS j.1 x)
  rw [tailAlgebraicToGlobal_of]

/-- The completed cofinal isometry has dense range in the global filtered
GNS Hilbert colimit. -/
theorem tailHilbertToGlobal_denseRange
    (i₀ : I) :
    DenseRange
      (tailHilbertToGlobalLinearIsometry
        Stage sys ω i₀) := by
  apply
    (dense_iUnion_range_upper_gnsStageToHilbertColimit
      Stage sys ω i₀).mono
  intro z hz
  rcases Set.mem_iUnion.mp hz with ⟨j, hj⟩
  rcases hj with ⟨x, rfl⟩
  refine
    ⟨stageToHilbertDirectLimit (E i₀) (S i₀) j x, ?_⟩
  exact tailHilbertToGlobal_stage Stage sys ω i₀ j x

/-- The completed cofinal isometry is onto: its range is closed because its
domain is complete and dense by cofinality. -/
theorem tailHilbertToGlobal_surjective
    (i₀ : I) :
    Function.Surjective
      (tailHilbertToGlobalLinearIsometry
        Stage sys ω i₀) := by
  have hclosed :
      IsClosed
        (Set.range
          (tailHilbertToGlobalLinearIsometry
            Stage sys ω i₀)) :=
    (tailHilbertToGlobal_isometry
      Stage sys ω i₀).isClosedEmbedding.isClosed_range
  have hdense :
      Dense
        (Set.range
          (tailHilbertToGlobalLinearIsometry
            Stage sys ω i₀)) :=
    tailHilbertToGlobal_denseRange Stage sys ω i₀
  intro z
  exact hdense.induction (fun x hx => hx) hclosed z

/-- Canonical unitary equivalence between the Hilbert colimit of a cofinal
GNS tail and the global filtered GNS Hilbert colimit. -/
def tailHilbertGlobalEquiv
    (i₀ : I) :
    HilbertDirectLimit (E i₀) (S i₀) ≃ₗᵢ[ℂ]
      GNSHilbertColimit Stage sys ω :=
  LinearIsometryEquiv.ofSurjective
    (tailHilbertToGlobalLinearIsometry
      Stage sys ω i₀)
    (tailHilbertToGlobal_surjective
      Stage sys ω i₀)

@[simp] theorem tailHilbertGlobalEquiv_stage
    (i₀ : I) (j : UpperIndex i₀) (x : E i₀ j) :
    tailHilbertGlobalEquiv Stage sys ω i₀
        (stageToHilbertDirectLimit (E i₀) (S i₀) j x) =
      gnsStageToHilbertColimit Stage sys ω j.1 x := by
  change
    tailHilbertToGlobalLinearIsometry Stage sys ω i₀
        (stageToHilbertDirectLimit (E i₀) (S i₀) j x) =
      gnsStageToHilbertColimit Stage sys ω j.1 x
  exact tailHilbertToGlobal_stage Stage sys ω i₀ j x

end CStarStateColimit.Native.FilteredGNSCofinalTail
