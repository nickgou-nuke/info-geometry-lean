import InfoGeometry.Canonical.FilteredCompatibleOperatorColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredGNSHilbertColimit

/-!
# Stage observables acting on cofinal filtered GNS tails

An observable `a : Aᵢ` does not canonically act on earlier GNS stages.  It
does act on every later stage by transport along the star-algebra system.
Accordingly, its honest operator colimit is formed over the upper tail
`{j // i ≤ j}`.  This is the direct-colimit formulation of the represented
observable; no global coordinate realization is assumed.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTailRepresentation

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSTomitaModularForm
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion
open InfoGeometry.Canonical.FilteredCompatibleOperatorColimit

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

/-- Cofinal upper tail beginning at one stage. -/
abbrev UpperIndex (i₀ : I) :=
  {j : I // i₀ ≤ j}

noncomputable instance upperIndexNonempty
    (i₀ : I) :
    Nonempty (UpperIndex i₀) :=
  ⟨⟨i₀, le_refl i₀⟩⟩

noncomputable instance upperIndexIsDirectedOrder
    (i₀ : I) :
    IsDirectedOrder (UpperIndex i₀) := by
  constructor
  intro j k
  obtain ⟨m, hjm, hkm⟩ := exists_ge_ge j.1 k.1
  exact
    ⟨⟨m, le_trans j.2 hjm⟩, hjm, hkm⟩

/-- Completed GNS stage family restricted to an upper tail. -/
abbrev TailGNSStage (i₀ : I) (j : UpperIndex i₀) :
    Type u :=
  (ω.state j.1).functional.GNS

/-- Restriction of the filtered GNS isometric system to an upper tail. -/
def tailGNSIsometricDirectSystem
    (i₀ : I) :
    IsometricDirectSystem (TailGNSStage Stage sys ω i₀) where
  map := fun hjk =>
    filteredGNSLinearIsometry Stage sys ω hjk
  map_id := by
    intro j
    exact congrArg
      (fun T =>
        T)
      ((filteredGNSIsometricDirectSystem
        Stage sys ω).map_id j.1)
  map_comp := by
    intro i j k hij hjk
    exact
      (filteredGNSIsometricDirectSystem
        Stage sys ω).map_comp hij hjk

/-- Transport a stage observable to one stage of its upper tail. -/
def tailObservable
    {i₀ : I} (a : Stage i₀)
    (j : UpperIndex i₀) :
    Stage j.1 :=
  sys.map j.2 a

/-- Tail observables are compatible with every further transition. -/
theorem tailObservable_transition
    {i₀ : I} (a : Stage i₀)
    {j k : UpperIndex i₀} (hjk : j ≤ k) :
    sys.map hjk (tailObservable Stage sys a j) =
      tailObservable Stage sys a k := by
  unfold tailObservable
  exact congrArg
    (fun f : Stage i₀ →⋆ₐ[ℂ] Stage k.1 => f a)
    (sys.map_comp j.2 hjk)

/-- The represented tail observable at one GNS stage. -/
def tailGNSOperator
    {i₀ : I} (a : Stage i₀)
    (j : UpperIndex i₀) :
    TailGNSStage Stage sys ω i₀ j →L[ℂ]
      TailGNSStage Stage sys ω i₀ j :=
  (ω.state j.1).functional.gnsStarAlgHom
    (tailObservable Stage sys a j)

/-- The represented observable intertwines the filtered GNS transitions on
its entire upper tail. -/
theorem tailGNSOperator_intertwines
    {i₀ : I} (a : Stage i₀)
    {j k : UpperIndex i₀} (hjk : j ≤ k)
    (x : TailGNSStage Stage sys ω i₀ j) :
    (tailGNSIsometricDirectSystem
        Stage sys ω i₀).map hjk
        (tailGNSOperator Stage sys ω a j x) =
      tailGNSOperator Stage sys ω a k
        ((tailGNSIsometricDirectSystem
          Stage sys ω i₀).map hjk x) := by
  simp only [tailGNSIsometricDirectSystem, tailGNSOperator,
    filteredGNSLinearIsometry_apply]
  have h :=
    congrFun
      (filteredGNSMap_intertwines
        Stage sys ω hjk
        (tailObservable Stage sys a j)) x
  rw [tailObservable_transition Stage sys a hjk] at h
  exact h

/-- The represented tail operator has the uniform bound inherited from the
original stage observable. -/
theorem tailGNSOperator_norm_le
    {i₀ : I} (a : Stage i₀)
    (j : UpperIndex i₀)
    (x : TailGNSStage Stage sys ω i₀ j) :
    ‖tailGNSOperator Stage sys ω a j x‖ ≤
      ‖a‖ * ‖x‖ := by
  have h_stage :
      ‖tailGNSOperator Stage sys ω a j x‖ ≤
        ‖tailObservable Stage sys a j‖ * ‖x‖ := by
    refine UniformSpace.Completion.induction_on x ?_ ?_
    · exact isClosed_le
        (continuous_norm.comp
          (tailGNSOperator Stage sys ω a j).continuous)
        (continuous_const.mul continuous_norm)
    · intro y
      rw [tailGNSOperator]
      change
        ‖(ω.state j.1).functional.gnsNonUnitalStarAlgHom
            (tailObservable Stage sys a j)
            (y : (ω.state j.1).functional.GNS)‖ ≤
          ‖tailObservable Stage sys a j‖ *
            ‖(y : (ω.state j.1).functional.GNS)‖
      rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
      rw [UniformSpace.Completion.norm_coe,
        UniformSpace.Completion.norm_coe]
      calc
        ‖(ω.state j.1).functional.leftMulMapPreGNS
              (tailObservable Stage sys a j) y‖ ≤
            ‖(ω.state j.1).functional.leftMulMapPreGNS
                (tailObservable Stage sys a j)‖ * ‖y‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖tailObservable Stage sys a j‖ * ‖y‖ := by
          exact mul_le_mul_of_nonneg_right
            (by
              unfold PositiveLinearMap.leftMulMapPreGNS
              apply LinearMap.mkContinuous_norm_le
              exact norm_nonneg _)
            (norm_nonneg y)
  calc
    ‖tailGNSOperator Stage sys ω a j x‖ ≤
        ‖tailObservable Stage sys a j‖ * ‖x‖ :=
      h_stage
    _ ≤ ‖a‖ * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right
        (NonUnitalStarAlgHom.norm_apply_le
          (sys.map j.2) a)
        (norm_nonneg x)

/-- A stage observable produces a compatible uniformly bounded family of
full GNS operators on its upper tail. -/
def tailGNSCompatibleOperatorFamily
    {i₀ : I} (a : Stage i₀) :
    CompatibleOperatorFamily
      (TailGNSStage Stage sys ω i₀)
      (tailGNSIsometricDirectSystem
        Stage sys ω i₀) where
  op := tailGNSOperator Stage sys ω a
  intertwines := by
    intro j k hjk x
    exact tailGNSOperator_intertwines
      Stage sys ω a hjk x
  bound := ‖a‖
  norm_le := tailGNSOperator_norm_le
    Stage sys ω a

/-- The bounded operator induced by a stage observable on the Hilbert
completion of its cofinal GNS tail. -/
def tailCompletedRepresentation
    {i₀ : I} (a : Stage i₀) :
    HilbertDirectLimit
        (TailGNSStage Stage sys ω i₀)
        (tailGNSIsometricDirectSystem
          Stage sys ω i₀) →L[ℂ]
      HilbertDirectLimit
        (TailGNSStage Stage sys ω i₀)
        (tailGNSIsometricDirectSystem
          Stage sys ω i₀) :=
  completedOperator
    (TailGNSStage Stage sys ω i₀)
    (tailGNSIsometricDirectSystem Stage sys ω i₀)
    (tailGNSCompatibleOperatorFamily
      Stage sys ω a)

/-- On every stage image, the completed representation acts by the native
GNS left representation of the transported observable. -/
@[simp] theorem tailCompletedRepresentation_stage
    {i₀ : I} (a : Stage i₀)
    (j : UpperIndex i₀)
    (x : TailGNSStage Stage sys ω i₀ j) :
    tailCompletedRepresentation Stage sys ω a
        (stageToHilbertDirectLimit
          (TailGNSStage Stage sys ω i₀)
          (tailGNSIsometricDirectSystem
            Stage sys ω i₀) j x) =
      stageToHilbertDirectLimit
        (TailGNSStage Stage sys ω i₀)
        (tailGNSIsometricDirectSystem
          Stage sys ω i₀) j
        (tailGNSOperator Stage sys ω a j x) := by
  exact completedOperator_stage
    (TailGNSStage Stage sys ω i₀)
    (tailGNSIsometricDirectSystem Stage sys ω i₀)
    (tailGNSCompatibleOperatorFamily Stage sys ω a)
    j x

end CStarStateColimit.Native.FilteredGNSTailRepresentation
