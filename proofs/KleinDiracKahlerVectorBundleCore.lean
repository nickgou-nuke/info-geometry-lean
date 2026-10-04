import proofs.KleinSixStateVectorBundleCore
import InfoGeometry.Topology.DiracKahlerMultiplication
import InfoGeometry.Canonical.DiracKahlerSplitCurvature

noncomputable section

open Topology
open KleinBrillouinBase KleinBottleOrbitQuotient KleinGlideCovering
open KleinGlideCoveringAtlas
open InfoGeometry.Topology.DiracKahlerMultiplication
open InfoGeometry.Canonical.DiracKahlerSplitCurvature

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

local instance : TopologicalSpace (V →ₗ[ℝ] V) := ⊥
local instance : DiscreteTopology (V →ₗ[ℝ] V) := ⟨rfl⟩

def operatorTwist (J : V →ₗ[ℝ] V) (T : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  J.comp (T.comp J)

theorem operatorTwist_involutive (J : V →ₗ[ℝ] V) (hJ : J.comp J = LinearMap.id) (T : V →ₗ[ℝ] V) :
    operatorTwist J (operatorTwist J T) = T := by
  ext x
  have h (y) : J (J y) = y := by
    have h' : (J.comp J) y = y := by rw [hJ]; rfl
    exact h'
  simp [operatorTwist, h]

def deckOperatorMap (J : V →ₗ[ℝ] V) (g : Deck2) (T : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  if g = 0 then T else operatorTwist J T

theorem deckOperatorMap_add (J : V →ₗ[ℝ] V) (hJ : J.comp J = LinearMap.id) (g h : Deck2) (T : V →ₗ[ℝ] V) :
    deckOperatorMap J (g + h) T = deckOperatorMap J h (deckOperatorMap J g T) := by
  have h11 : (1 + 1 : Deck2) = 0 := by decide
  fin_cases g <;> fin_cases h
  · simp [deckOperatorMap]
  · simp [deckOperatorMap]
  · simp [deckOperatorMap]
  · simp [deckOperatorMap, h11, operatorTwist_involutive J hJ T]

theorem continuous_deckOperatorMap (J : V →ₗ[ℝ] V) :
    Continuous (fun p : Deck2 × (V →ₗ[ℝ] V) ↦ deckOperatorMap J p.1 p.2) := by
  rw [continuous_prod_of_discrete_left]
  intro g
  exact continuous_of_discreteTopology

def operatorCoordChange (J : V →ₗ[ℝ] V) (i j x : KleinBrillouinQuotient)
    (T : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  deckOperatorMap J (KleinSixStateVectorBundleCore.deckTransition i j x) T

theorem continuousOn_operatorCoordChange (J : V →ₗ[ℝ] V)
    (i j : KleinBrillouinQuotient) :
    ContinuousOn (fun p : KleinBrillouinQuotient × (V →ₗ[ℝ] V) ↦
      operatorCoordChange J i j p.1 p.2)
      (((coverTriv i).baseSet ∩ (coverTriv j).baseSet) ×ˢ Set.univ) := by
  have ht : ContinuousOn
      (fun p : KleinBrillouinQuotient × (V →ₗ[ℝ] V) ↦
        KleinSixStateVectorBundleCore.deckTransition i j p.1)
      (((coverTriv i).baseSet ∩ (coverTriv j).baseSet) ×ˢ Set.univ) :=
    (KleinSixStateVectorBundleCore.continuousOn_deckTransition i j).comp continuousOn_fst (fun _ hp ↦ hp.1)
  exact (continuous_deckOperatorMap J).comp_continuousOn (ht.prodMk continuousOn_snd)

/-- Native Mathlib FiberBundleCore mapping the topological Klein quotient to the Dirac-Kähler data. -/
def kleinDiracKahlerBundleCore (J : V →ₗ[ℝ] V) (hJ : J.comp J = LinearMap.id) :
    FiberBundleCore KleinBrillouinQuotient KleinBrillouinQuotient (V →ₗ[ℝ] V) where
  baseSet i := (coverTriv i).baseSet
  isOpen_baseSet i := (coverTriv i).open_baseSet
  indexAt x := x
  mem_baseSet_at x := mem_coverTriv_baseSet x
  coordChange := operatorCoordChange J
  coordChange_self i x hx T := by
    rw [operatorCoordChange, KleinSixStateVectorBundleCore.deckTransition_self i x hx]
    rfl
  continuousOn_coordChange := continuousOn_operatorCoordChange J
  coordChange_comp i j k x hx T := by
    rw [operatorCoordChange, operatorCoordChange, operatorCoordChange,
      KleinSixStateVectorBundleCore.deckTransition_comp i j k x hx.1.1 hx.1.2 hx.2]
    exact (deckOperatorMap_add J hJ _ _ T).symm

/-- Physical formalization: the orientation-reversing twist swaps the negative Dirac-Kähler operator. -/
theorem klein_holonomy_swaps_negative_dirac (D : Data V) (hJ : D.chirality.comp D.chirality = LinearMap.id) :
    operatorTwist D.chirality (negativeDirac D) = -(negativeDirac D) := by
  dsimp [operatorTwist, negativeDirac]
  have h1 : D.chirality.comp (D.d.comp D.chirality) = -D.d := by
    rw [D.d_anticommutes]
    rw [LinearMap.comp_neg, ← LinearMap.comp_assoc, hJ, LinearMap.id_comp]
  have h2 : D.chirality.comp (D.codifferential.comp D.chirality) = -D.codifferential := by
    rw [D.codifferential_anticommutes]
    rw [LinearMap.comp_neg, ← LinearMap.comp_assoc, hJ, LinearMap.id_comp]
  rw [LinearMap.sub_comp, LinearMap.comp_sub]
  rw [h1, h2]
  abel
