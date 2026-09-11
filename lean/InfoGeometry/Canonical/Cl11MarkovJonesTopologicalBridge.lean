import InfoGeometry.Clifford.Cl11MarkovJonesEngine
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Topological readout for the finite `Cl(1,1)` Markov trace net

`Cl11MarkovJonesEngine` owns the algebraic finite Markov trace and its
one-step stability.  This owner exposes the same maps in `TopCat`.  It stops
at the finite compatible readout: no trace on a completed or infinite factor
is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11MarkovJonesTopologicalBridge

open CategoryTheory
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11MarkovJonesEngine

/-- The one-step matrix embedding as a continuous `TopCat` morphism. -/
def stageEmbedTopCatHom (n : ℕ) :
    TopCat.of (MatStage n) ⟶ TopCat.of (MatStage (n + 1)) :=
  TopCat.ofHom
    { toFun := stageEmbed n
      continuous_toFun :=
        (stageEmbed n).toLinearMap.continuous_of_finiteDimensional }

/-- The normalized finite Markov trace as a continuous `TopCat` morphism. -/
def normalizedTraceTopCatHom (n : ℕ) :
    TopCat.of (MatStage n) ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := normalizedTraceLinear n
      continuous_toFun :=
        (normalizedTraceLinear n).continuous_of_finiteDimensional }

@[simp] theorem stageEmbedTopCatHom_apply (n : ℕ) (A : MatStage n) :
    stageEmbedTopCatHom n A = stageEmbed n A :=
  rfl

@[simp] theorem normalizedTraceTopCatHom_apply (n : ℕ) (A : MatStage n) :
    normalizedTraceTopCatHom n A = normalizedTraceLinear n A :=
  rfl

/-- The finite Markov stability law is a naturality square in `TopCat`. -/
theorem normalizedTraceTopCat_naturality (n : ℕ) :
    stageEmbedTopCatHom n ≫ normalizedTraceTopCatHom (n + 1) =
      normalizedTraceTopCatHom n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro A
  change normalizedTraceLinear (n + 1) (stageEmbed n A) =
    normalizedTraceLinear n A
  exact cl11_normalizedTrace_one_step n A

/-- The normalization readout is the unit at every finite stage. -/
theorem normalizedTraceTopCat_one (n : ℕ) :
    normalizedTraceTopCatHom n (1 : MatStage n) = 1 := by
  change normalizedTraceLinear n (1 : MatStage n) = 1
  exact cl11MarkovTraceNet.map_one n

/-- The algebraic and topological readouts agree pointwise on a one-step
transition. -/
theorem normalizedTraceTopCat_naturality_apply (n : ℕ) (A : MatStage n) :
    normalizedTraceTopCatHom (n + 1) (stageEmbedTopCatHom n A) =
      normalizedTraceTopCatHom n A := by
  exact congrArg (fun f => f A) (normalizedTraceTopCat_naturality n)

end InfoGeometry.Canonical.Cl11MarkovJonesTopologicalBridge
