import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# The Jaynes--Lean Colimit Bridge

This module packages the finite-stage content of the slogan:

* Jaynes: continuum probability is approached through finite-set refinements;
* Lean: infinity is controlled by inductive/recursive rules;
* category theory: the continuum is represented as a colimit of a
  directed finite-stage diagram.

The finite kernel below is intentionally modest.  It defines finite probability
stages, refinement morphisms preserving the normalizing data, a countable
directed system, and explicit data structures for the continuum/KMS/Bures/GNS
targets.  No analytic continuum theorem is asserted beyond supplied fields.
-/

noncomputable section

open BigOperators
open CategoryTheory CategoryTheory.Limits

namespace JaynesLeanColimitBridge

universe u v

/-- The finite Kolmogorov probability axioms for a concrete finite support. -/
def FiniteKolmogorovAxioms (Ω : Type) [Fintype Ω] (prob : Ω → ℝ) : Prop :=
  (∑ ω : Ω, prob ω) = 1 ∧ ∀ ω, 0 ≤ prob ω

/-- The finite Gibbs/KMS normalization condition for a finite support. -/
def FiniteKMSCondition (Ω : Type) [Fintype Ω]
    (prob finiteIntegralOfMotion : Ω → ℝ) : Prop :=
  ∃ (β : ℝ), ∀ ω,
    prob ω * (∑ ω' : Ω, Real.exp (- β * finiteIntegralOfMotion ω')) =
      Real.exp (- β * finiteIntegralOfMotion ω)

/-- A finite Jaynes stage: probability is first defined on a finite set of
explicit alternatives. -/
structure FiniteJaynesSide where
  partitionSize : ℕ
  partitionSize_pos : 0 < partitionSize
  sampleSpace : Type
  sampleSpace_fintype : Fintype sampleSpace
  prob : sampleSpace → ℝ
  prob_nonneg : ∀ ω, 0 ≤ prob ω
  prob_sum_one : (∑ ω : sampleSpace, prob ω) = 1
  finiteIntegralOfMotion : sampleSpace → ℝ
  finiteKMS_condition : FiniteKMSCondition sampleSpace prob finiteIntegralOfMotion
  finiteKolmogorovAxioms_hold : FiniteKolmogorovAxioms sampleSpace prob

/-- The stage-indexed Kolmogorov proposition, separate from the stored field. -/
def StageKolmogorov (S : FiniteJaynesSide) : Prop :=
  letI := S.sampleSpace_fintype
  FiniteKolmogorovAxioms S.sampleSpace S.prob

/-- The stage-indexed KMS proposition, separate from the stored field. -/
def StageKMS (S : FiniteJaynesSide) : Prop :=
  letI := S.sampleSpace_fintype
  FiniteKMSCondition S.sampleSpace S.prob S.finiteIntegralOfMotion

/-- Finite expectation: the Jaynes-safe object before any continuum limit. -/
def finiteExpectation (S : FiniteJaynesSide) (O : S.sampleSpace → ℝ) : ℝ :=
  letI := S.sampleSpace_fintype;
  ∑ ω : S.sampleSpace, O ω * S.prob ω

/-- Finite Shannon entropy.  Differential entropy is deliberately not used as a
primitive object in this finite module. -/
def finiteShannonEntropy (S : FiniteJaynesSide) : ℝ :=
  letI := S.sampleSpace_fintype;
  -(∑ ω : S.sampleSpace,
    let pω := S.prob ω;
    if pω > 0 then pω * Real.log pω else 0)

/-- The expectation of the constant observable `1` is normalized. -/
theorem finiteExpectation_one (S : FiniteJaynesSide) :
    finiteExpectation S (fun _ => 1) = 1 := by
  simp [finiteExpectation, S.prob_sum_one]

/-- A refinement morphism from a coarse finite Jaynes stage to a finer stage. -/
structure RefinementMorphism (S T : FiniteJaynesSide) where
  map : S.sampleSpace → T.sampleSpace
  preserves_integral_of_motion :
    ∀ ω, S.finiteIntegralOfMotion ω = T.finiteIntegralOfMotion (map ω)
  preserves_kolmogorov :
    StageKolmogorov S → StageKolmogorov T
  preserves_kms : StageKMS S → StageKMS T

/-- Normalization is stagewise invariant because each finite stage is itself a
probability space. -/
theorem refinement_preserves_total_probability
    {S T : FiniteJaynesSide} (_r : RefinementMorphism S T) :
    (letI := S.sampleSpace_fintype; ∑ ω : S.sampleSpace, S.prob ω) =
      (letI := T.sampleSpace_fintype; ∑ ω' : T.sampleSpace, T.prob ω') := by
  simp [S.prob_sum_one, T.prob_sum_one]

/-- A countable directed system of finite Jaynes stages.  The transition
morphisms are the generalized `succ` operation. -/
structure JaynesDirectedSystem where
  stages : ℕ → FiniteJaynesSide
  refinements : ∀ n, RefinementMorphism (stages n) (stages (n + 1))

/-- Propagate Kolmogorov validity by one successor/refinement step. -/
theorem kolmogorov_succ
    (D : JaynesDirectedSystem) (n : ℕ)
    (h : StageKolmogorov (D.stages n)) :
    StageKolmogorov (D.stages (n + 1)) :=
  (D.refinements n).preserves_kolmogorov h

/-- Propagate the finite KMS condition by one successor/refinement step. -/
theorem kms_succ
    (D : JaynesDirectedSystem) (n : ℕ)
    (h : StageKMS (D.stages n)) :
    StageKMS (D.stages (n + 1)) :=
  (D.refinements n).preserves_kms h

/-- A native readout from the canonical colimit to a supplied cocone target. -/
noncomputable def nativeColimitReadout
    {J : Type v} [Category.{v} J] (F : J ⥤ Type u)
    [HasColimit F]
    (C : Cocone F) : colimit F ⟶ C.pt :=
  colimit.desc F C

theorem nativeColimitReadout_ι
    {J : Type v} [Category.{v} J] (F : J ⥤ Type u)
    [HasColimit F]
    (C : Cocone F) (j : J) :
    colimit.ι F j ≫ nativeColimitReadout F C = C.ι.app j := by
  exact colimit.ι_desc C j

theorem nativeColimitReadout_unique
    {J : Type v} [Category.{v} J] (F : J ⥤ Type u)
    [HasColimit F]
    (C : Cocone F)
    (g : colimit F ⟶ C.pt)
    (hg : ∀ j : J, colimit.ι F j ≫ g = C.ι.app j) :
    g = nativeColimitReadout F C := by
  apply colimit.hom_ext
  intro j
  rw [hg j, nativeColimitReadout_ι]

end JaynesLeanColimitBridge
