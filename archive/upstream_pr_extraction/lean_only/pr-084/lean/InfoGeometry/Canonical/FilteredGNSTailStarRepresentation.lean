import InfoGeometry.Canonical.FilteredGNSTailRepresentation

/-!
# Algebra representations on filtered GNS tails

The cofinal-tail operators attached to one stage algebra preserve addition,
multiplication, and the unit after passage to the completed filtered GNS
Hilbert space.  The proofs use the dense union of stage GNS images and the
native stage GNS representation; no ambient coordinate representation is
chosen.

The involution is transported by proving the Hilbert-adjoint pairing first on
two arbitrary stage images at a common upper stage and then extending it in
both variables across their dense union.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTailStarRepresentation

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSTomitaModularForm
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSTailRepresentation
open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
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

local notation "E" =>
  TailGNSStage Stage sys ω
local notation "S" =>
  tailGNSIsometricDirectSystem Stage sys ω

/-- Two bounded operators on a filtered GNS-tail completion are equal when
they agree on every canonical stage image. -/
theorem continuousLinearMap_eq_of_stage_eq
    {i₀ : I}
    {T U :
      HilbertDirectLimit (E i₀) (S i₀) →L[ℂ]
        HilbertDirectLimit (E i₀) (S i₀)}
    (h :
      ∀ (j : UpperIndex i₀) (x : E i₀ j),
        T (stageToHilbertDirectLimit (E i₀) (S i₀) j x) =
          U (stageToHilbertDirectLimit (E i₀) (S i₀) j x)) :
    T = U := by
  apply ContinuousLinearMap.ext
  have hfun : (T : HilbertDirectLimit (E i₀) (S i₀) →
      HilbertDirectLimit (E i₀) (S i₀)) = U := by
    apply UniformSpace.Completion.denseRange_coe.equalizer
      T.continuous U.continuous
    funext y
    induction y using Module.DirectLimit.induction_on with
    | ih j x =>
        exact h j x
  exact fun x => congrFun hfun x

/-- Addition of observables is represented by addition of the completed
tail operators. -/
theorem tailCompletedRepresentation_add
    {i₀ : I} (a b : Stage i₀) :
    tailCompletedRepresentation Stage sys ω (a + b) =
      tailCompletedRepresentation Stage sys ω a +
        tailCompletedRepresentation Stage sys ω b := by
  apply continuousLinearMap_eq_of_stage_eq Stage sys ω
  intro j x
  simp only [ContinuousLinearMap.add_apply,
    tailCompletedRepresentation_stage]
  simp [tailGNSOperator, tailObservable]
  exact UniformSpace.Completion.coe_add _ _

/-- Multiplication of observables is represented by composition of the
completed tail operators. -/
theorem tailCompletedRepresentation_mul
    {i₀ : I} (a b : Stage i₀) :
    tailCompletedRepresentation Stage sys ω (a * b) =
      tailCompletedRepresentation Stage sys ω a *
        tailCompletedRepresentation Stage sys ω b := by
  apply continuousLinearMap_eq_of_stage_eq Stage sys ω
  intro j x
  simp only [ContinuousLinearMap.mul_apply,
    tailCompletedRepresentation_stage]
  simp [tailGNSOperator, tailObservable]

/-- The stage unit acts as the identity on the completed cofinal-tail GNS
space. -/
theorem tailCompletedRepresentation_one
    (i₀ : I) :
    tailCompletedRepresentation Stage sys ω (1 : Stage i₀) = 1 := by
  apply continuousLinearMap_eq_of_stage_eq Stage sys ω
  intro j x
  simp only [ContinuousLinearMap.one_apply,
    tailCompletedRepresentation_stage]
  simp [tailGNSOperator, tailObservable]

/-- The completed cofinal-tail action bundled as a genuine algebra
homomorphism. -/
def tailCompletedRepresentationAlgHom
    (i₀ : I) :
    Stage i₀ →ₐ[ℂ]
      (HilbertDirectLimit (E i₀) (S i₀) →L[ℂ]
        HilbertDirectLimit (E i₀) (S i₀)) where
  toFun := tailCompletedRepresentation Stage sys ω
  map_one' := tailCompletedRepresentation_one Stage sys ω i₀
  map_mul' := tailCompletedRepresentation_mul Stage sys ω
  map_zero' := by
    simpa using
      tailCompletedRepresentation_add Stage sys ω
        (0 : Stage i₀) 0
  map_add' := tailCompletedRepresentation_add Stage sys ω
  commutes' := by
    intro c
    apply continuousLinearMap_eq_of_stage_eq Stage sys ω
    intro j x
    rw [tailCompletedRepresentation_stage]
    have hstage :
        tailGNSOperator Stage sys ω
            ((algebraMap ℂ (Stage i₀)) c) j x =
          c • x := by
      change
        (ω.state j.1).functional.gnsStarAlgHom
            ((sys.map j.2)
              ((algebraMap ℂ (Stage i₀)) c)) x =
          c • x
      have hmap :
          (sys.map j.2) ((algebraMap ℂ (Stage i₀)) c) =
            (algebraMap ℂ (Stage j.1)) c :=
        AlgHomClass.commutes (sys.map j.2) c
      rw [hmap]
      have hrep :
          (ω.state j.1).functional.gnsStarAlgHom
              ((algebraMap ℂ (Stage j.1)) c) =
            (algebraMap ℂ
              ((ω.state j.1).functional.GNS →L[ℂ]
                (ω.state j.1).functional.GNS)) c :=
        AlgHomClass.commutes
          (ω.state j.1).functional.gnsStarAlgHom c
      rw [hrep]
      rfl
    rw [hstage]
    exact
      (stageToHilbertDirectLimit (E i₀) (S i₀) j).map_smul c x

@[simp] theorem tailCompletedRepresentationAlgHom_apply
    {i₀ : I} (a : Stage i₀) :
    tailCompletedRepresentationAlgHom Stage sys ω i₀ a =
      tailCompletedRepresentation Stage sys ω a :=
  rfl

/-- At each tail stage, the transported involution acts by the Hilbert
adjoint of the transported observable. -/
theorem tailGNSOperator_star_inner
    {i₀ : I} (a : Stage i₀)
    (j : UpperIndex i₀)
    (x y : E i₀ j) :
    inner ℂ
        (tailGNSOperator Stage sys ω (star a) j y) x =
      inner ℂ y
        (tailGNSOperator Stage sys ω a j x) := by
  change
    inner ℂ
        ((ω.state j.1).functional.gnsStarAlgHom
          ((sys.map j.2) (star a)) y) x =
      inner ℂ y
        ((ω.state j.1).functional.gnsStarAlgHom
          ((sys.map j.2) a) x)
  rw [map_star]
  rw [map_star]
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- The completed operators satisfy the adjoint pairing on any two canonical
stage images.  Different stages are compared only after transport to a common
upper stage of the filtered system. -/
theorem tailCompletedRepresentation_star_inner_stage
    {i₀ : I} (a : Stage i₀)
    (j k : UpperIndex i₀)
    (x : E i₀ j) (y : E i₀ k) :
    inner ℂ
        (tailCompletedRepresentation Stage sys ω (star a)
          (stageToHilbertDirectLimit (E i₀) (S i₀) k y))
        (stageToHilbertDirectLimit (E i₀) (S i₀) j x) =
      inner ℂ
        (stageToHilbertDirectLimit (E i₀) (S i₀) k y)
        (tailCompletedRepresentation Stage sys ω a
          (stageToHilbertDirectLimit (E i₀) (S i₀) j x)) := by
  obtain ⟨m, hjm, hkm⟩ := exists_ge_ge j k
  rw [tailCompletedRepresentation_stage,
    tailCompletedRepresentation_stage]
  calc
    inner ℂ
        (stageToHilbertDirectLimit (E i₀) (S i₀) k
          (tailGNSOperator Stage sys ω (star a) k y))
        (stageToHilbertDirectLimit (E i₀) (S i₀) j x) =
      inner ℂ
        (stageToHilbertDirectLimit (E i₀) (S i₀) m
          ((S i₀).map hkm
            (tailGNSOperator Stage sys ω (star a) k y)))
        (stageToHilbertDirectLimit (E i₀) (S i₀) m
          ((S i₀).map hjm x)) := by
        rw [stageToHilbertDirectLimit_transition,
          stageToHilbertDirectLimit_transition]
    _ = inner ℂ
        ((S i₀).map hkm
          (tailGNSOperator Stage sys ω (star a) k y))
        ((S i₀).map hjm x) :=
      (stageToHilbertDirectLimit (E i₀) (S i₀) m).inner_map_map _ _
    _ = inner ℂ
        (tailGNSOperator Stage sys ω (star a) m
          ((S i₀).map hkm y))
        ((S i₀).map hjm x) := by
      rw [tailGNSOperator_intertwines Stage sys ω (star a) hkm y]
    _ = inner ℂ
        ((S i₀).map hkm y)
        (tailGNSOperator Stage sys ω a m
          ((S i₀).map hjm x)) :=
      tailGNSOperator_star_inner Stage sys ω a m _ _
    _ = inner ℂ
        ((S i₀).map hkm y)
        ((S i₀).map hjm
          (tailGNSOperator Stage sys ω a j x)) := by
      rw [tailGNSOperator_intertwines Stage sys ω a hjm x]
    _ = inner ℂ
        (stageToHilbertDirectLimit (E i₀) (S i₀) m
          ((S i₀).map hkm y))
        (stageToHilbertDirectLimit (E i₀) (S i₀) m
          ((S i₀).map hjm
            (tailGNSOperator Stage sys ω a j x))) := by
      rw [(stageToHilbertDirectLimit
        (E i₀) (S i₀) m).inner_map_map]
    _ = inner ℂ
        (stageToHilbertDirectLimit (E i₀) (S i₀) k y)
        (stageToHilbertDirectLimit (E i₀) (S i₀) j
          (tailGNSOperator Stage sys ω a j x)) := by
      rw [stageToHilbertDirectLimit_transition,
        stageToHilbertDirectLimit_transition]

/-- The completed tail representation preserves the adjoint pairing on the
whole Hilbert colimit.  The extension uses the dense union of stage images in
each argument. -/
theorem tailCompletedRepresentation_star_inner
    {i₀ : I} (a : Stage i₀)
    (z w : HilbertDirectLimit (E i₀) (S i₀)) :
    inner ℂ
        (tailCompletedRepresentation Stage sys ω (star a) w) z =
      inner ℂ w
        (tailCompletedRepresentation Stage sys ω a z) := by
  let D : Set (HilbertDirectLimit (E i₀) (S i₀)) :=
    ⋃ j : UpperIndex i₀,
      Set.range (stageToHilbertDirectLimit (E i₀) (S i₀) j)
  have hD : Dense D :=
    dense_iUnion_range_stageToHilbertDirectLimit (E i₀) (S i₀)
  have h_stage_left :
      ∀ (j : UpperIndex i₀) (x : E i₀ j)
        (w : HilbertDirectLimit (E i₀) (S i₀)),
        inner ℂ
            (tailCompletedRepresentation Stage sys ω (star a) w)
            (stageToHilbertDirectLimit (E i₀) (S i₀) j x) =
          inner ℂ w
            (tailCompletedRepresentation Stage sys ω a
              (stageToHilbertDirectLimit (E i₀) (S i₀) j x)) := by
    intro j x
    have heq :
        (fun w =>
          inner ℂ
            (tailCompletedRepresentation Stage sys ω (star a) w)
            (stageToHilbertDirectLimit (E i₀) (S i₀) j x)) =
        (fun w =>
          inner ℂ w
            (tailCompletedRepresentation Stage sys ω a
              (stageToHilbertDirectLimit (E i₀) (S i₀) j x))) := by
      apply Continuous.ext_on hD
      · exact
          (tailCompletedRepresentation
            Stage sys ω (star a)).continuous.inner continuous_const
      · exact continuous_id.inner continuous_const
      · intro w hw
        rcases Set.mem_iUnion.mp hw with ⟨k, hk⟩
        rcases hk with ⟨y, rfl⟩
        exact tailCompletedRepresentation_star_inner_stage
          Stage sys ω a j k x y
    exact fun w => congrFun heq w
  have heq :
      (fun z =>
        inner ℂ
          (tailCompletedRepresentation Stage sys ω (star a) w) z) =
      (fun z =>
        inner ℂ w
          (tailCompletedRepresentation Stage sys ω a z)) := by
    apply Continuous.ext_on hD
    · exact continuous_const.inner continuous_id
    · exact continuous_const.inner
        (tailCompletedRepresentation Stage sys ω a).continuous
    · intro z hz
      rcases Set.mem_iUnion.mp hz with ⟨j, hj⟩
      rcases hj with ⟨x, rfl⟩
      exact h_stage_left j x w
  exact congrFun heq z

/-- The completed representation sends the algebra involution to the Hilbert
adjoint involution on bounded operators. -/
theorem tailCompletedRepresentation_star
    {i₀ : I} (a : Stage i₀) :
    tailCompletedRepresentation Stage sys ω (star a) =
      star (tailCompletedRepresentation Stage sys ω a) := by
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_right ℂ
  intro z
  rw [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact tailCompletedRepresentation_star_inner
    Stage sys ω a z w

/-- The cofinal-tail action of a stage algebra on the completed filtered GNS
space, bundled as a genuine star-algebra representation. -/
def tailCompletedRepresentationStarAlgHom
    (i₀ : I) :
    Stage i₀ →⋆ₐ[ℂ]
      (HilbertDirectLimit (E i₀) (S i₀) →L[ℂ]
        HilbertDirectLimit (E i₀) (S i₀)) :=
  { tailCompletedRepresentationAlgHom Stage sys ω i₀ with
    map_star' := tailCompletedRepresentation_star Stage sys ω }

@[simp] theorem tailCompletedRepresentationStarAlgHom_apply
    {i₀ : I} (a : Stage i₀) :
    tailCompletedRepresentationStarAlgHom Stage sys ω i₀ a =
      tailCompletedRepresentation Stage sys ω a :=
  rfl

end CStarStateColimit.Native.FilteredGNSTailStarRepresentation
