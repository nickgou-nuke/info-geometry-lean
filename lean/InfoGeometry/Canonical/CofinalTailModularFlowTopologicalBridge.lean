import InfoGeometry.Canonical.FilteredGNSCofinalTailTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Cofinal-tail transport of a topological flow

This owner records the exact descent statement needed for a modular-flow
interface.  The flow maps are parameters: no analytic Tomita construction is
asserted here.  If the global and tail maps agree after every finite-stage
injection, continuity and the density of the tail stages force the global
intertwining square.
-/

noncomputable section

namespace CStarStateColimit.Native.CofinalTailModularFlowTopologicalBridge

open CategoryTheory CategoryTheory.Limits
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSCofinalTail
open CStarStateColimit.Native.FilteredGNSCofinalTailTopology
open CStarStateColimit.Native.FilteredGNSCofinalTailTopCatEquivalence
open CStarStateColimit.Native.FilteredGNSCofinalTailTopological
open CStarStateColimit.Native.FilteredGNSTailRepresentation
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
  (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

local notation "E" => TailGNSStage Stage sys ω
local notation "S" => tailGNSIsometricDirectSystem Stage sys ω

def tailStageTopCatHom (i₀ : I) (j : UpperIndex i₀) :
    TopCat.of (E i₀ j) ⟶
      TopCat.of (HilbertDirectLimit (E i₀) (S i₀)) :=
  TopCat.ofHom
    { toFun := stageToHilbertDirectLimit (E i₀) (S i₀) j
      continuous_toFun :=
        (stageToHilbertDirectLimit (E i₀) (S i₀) j).continuous }

/-- A pair of continuous maps on the global and cofinal-tail Hilbert
colimits, together with the finite-stage compatibility that determines their
intertwining. -/
structure CofinalTailFlowData (i₀ : I) where
  globalFlow : ℝ →
    (TopCat.of (GNSHilbertColimit Stage sys ω) ⟶
      TopCat.of (GNSHilbertColimit Stage sys ω))
  tailFlow : ℝ →
    (TopCat.of
      (HilbertDirectLimit (E i₀) (S i₀)) ⟶
      TopCat.of
        (HilbertDirectLimit (E i₀) (S i₀)))
  stage_intertwines : ∀ (t : ℝ) (j : UpperIndex i₀),
    (tailStageTopCatHom Stage sys ω i₀ j ≫
      tailFlow t ≫ tailToGlobalTopCatMap Stage sys ω i₀) =
    (tailStageTopCatHom Stage sys ω i₀ j ≫
      tailToGlobalTopCatMap Stage sys ω i₀ ≫ globalFlow t)

/-- A cofinal-tail flow whose global leg already satisfies the one-parameter
group laws.  The tail laws are intentionally omitted: they are consequences
of the cofinal topological equivalence below. -/
structure CofinalTailFlowGroupData (i₀ : I)
    extends CofinalTailFlowData Stage sys ω i₀ where
  global_zero : globalFlow 0 = 𝟙 _
  global_add : ∀ t s, globalFlow (t + s) = globalFlow s ≫ globalFlow t

@[reassoc]
theorem cofinalTailFlow_intertwines
    (i₀ : I) (D : CofinalTailFlowData Stage sys ω i₀) (t : ℝ) :
    tailToGlobalTopCatMap Stage sys ω i₀ ≫ D.globalFlow t =
      D.tailFlow t ≫ tailToGlobalTopCatMap Stage sys ω i₀ := by
  apply TopCat.hom_ext
  have hdense : DenseRange
      (fun p : Σ j : UpperIndex i₀, E i₀ j =>
        stageToHilbertDirectLimit (E i₀) (S i₀) p.1 p.2) := by
    change Dense (Set.range
      (fun p : Σ j : UpperIndex i₀, E i₀ j =>
        stageToHilbertDirectLimit (E i₀) (S i₀) p.1 p.2))
    have hrange :
        Set.range
            (fun p : Σ j : UpperIndex i₀, E i₀ j =>
              stageToHilbertDirectLimit (E i₀) (S i₀) p.1 p.2) =
          ⋃ j : UpperIndex i₀,
            Set.range (stageToHilbertDirectLimit (E i₀) (S i₀) j) := by
      ext y
      constructor
      · rintro ⟨⟨j, x⟩, rfl⟩
        exact Set.mem_iUnion.mpr ⟨j, ⟨x, rfl⟩⟩
      · intro hy
        rcases Set.mem_iUnion.mp hy with ⟨j, ⟨x, rfl⟩⟩
        exact ⟨⟨j, x⟩, rfl⟩
    rw [hrange]
    exact dense_iUnion_range_stageToHilbertDirectLimit (E i₀) (S i₀)
  have hfun :
      (fun x => (tailToGlobalTopCatMap Stage sys ω i₀ ≫ D.globalFlow t).hom x) =
        (fun x => (D.tailFlow t ≫ tailToGlobalTopCatMap Stage sys ω i₀).hom x) := by
    apply hdense.equalizer
    · exact (D.globalFlow t).hom.continuous.comp
        (tailToGlobalTopCatMap Stage sys ω i₀).hom.continuous
    · exact (tailToGlobalTopCatMap Stage sys ω i₀).hom.continuous.comp
        (D.tailFlow t).hom.continuous
    · funext x
      simp only [Function.comp_apply]
      simpa only [Category.assoc] using
        (congrArg (fun m => m.hom x.2)
          (D.stage_intertwines t x.1)).symm
  apply ContinuousMap.ext
  intro x
  exact congrFun hfun x

theorem cofinalTailFlow_zero
    (i₀ : I) (D : CofinalTailFlowGroupData Stage sys ω i₀) :
    D.toCofinalTailFlowData.tailFlow 0 = 𝟙 _ := by
  apply (Iso.cancel_iso_hom_right _ _
    (tailGlobalTopCatIso Stage sys ω i₀)).mp
  calc
    D.toCofinalTailFlowData.tailFlow 0 ≫
        tailToGlobalTopCatMap Stage sys ω i₀ =
      tailToGlobalTopCatMap Stage sys ω i₀ ≫
        D.toCofinalTailFlowData.globalFlow 0 :=
      (cofinalTailFlow_intertwines Stage sys ω i₀
        D.toCofinalTailFlowData 0).symm
    _ = tailToGlobalTopCatMap Stage sys ω i₀ ≫ 𝟙 _ := by
      rw [D.global_zero]
    _ = 𝟙 _ ≫ tailToGlobalTopCatMap Stage sys ω i₀ := by simp

theorem cofinalTailFlow_add
    (i₀ : I) (D : CofinalTailFlowGroupData Stage sys ω i₀)
    (t s : ℝ) :
    D.toCofinalTailFlowData.tailFlow (t + s) =
      D.toCofinalTailFlowData.tailFlow s ≫
        D.toCofinalTailFlowData.tailFlow t := by
  apply (Iso.cancel_iso_hom_right _ _
    (tailGlobalTopCatIso Stage sys ω i₀)).mp
  calc
    D.toCofinalTailFlowData.tailFlow (t + s) ≫
        tailToGlobalTopCatMap Stage sys ω i₀ =
      tailToGlobalTopCatMap Stage sys ω i₀ ≫
        D.toCofinalTailFlowData.globalFlow (t + s) :=
      (cofinalTailFlow_intertwines Stage sys ω i₀
        D.toCofinalTailFlowData (t + s)).symm
    _ = tailToGlobalTopCatMap Stage sys ω i₀ ≫
        (D.toCofinalTailFlowData.globalFlow s ≫
          D.toCofinalTailFlowData.globalFlow t) := by
      rw [D.global_add]
    _ = (tailToGlobalTopCatMap Stage sys ω i₀ ≫
          D.toCofinalTailFlowData.globalFlow s) ≫
        D.toCofinalTailFlowData.globalFlow t := by
      simp only [Category.assoc]
    _ = (D.toCofinalTailFlowData.tailFlow s ≫
          tailToGlobalTopCatMap Stage sys ω i₀) ≫
        D.toCofinalTailFlowData.globalFlow t := by
      rw [cofinalTailFlow_intertwines Stage sys ω i₀
        D.toCofinalTailFlowData s]
    _ = D.toCofinalTailFlowData.tailFlow s ≫
        (tailToGlobalTopCatMap Stage sys ω i₀ ≫
          D.toCofinalTailFlowData.globalFlow t) := by
      simp only [Category.assoc]
    _ = D.toCofinalTailFlowData.tailFlow s ≫
        (D.toCofinalTailFlowData.tailFlow t ≫
          tailToGlobalTopCatMap Stage sys ω i₀) := by
      rw [cofinalTailFlow_intertwines Stage sys ω i₀
        D.toCofinalTailFlowData t]
    _ = (D.toCofinalTailFlowData.tailFlow s ≫
          D.toCofinalTailFlowData.tailFlow t) ≫
        tailToGlobalTopCatMap Stage sys ω i₀ := by
      simp only [Category.assoc]

end CStarStateColimit.Native.CofinalTailModularFlowTopologicalBridge
