import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic

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

namespace JaynesLeanColimitBridge

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

/-- A bare colimit object for a directed Jaynes system.  The universal property
is stored as a field of the chosen colimit object. -/
structure InductionColimit (D : JaynesDirectedSystem) where
  colimitCarrier : Type
  inclusions : ∀ n, (D.stages n).sampleSpace → colimitCarrier
  universalProperty : ∀ (C : Type) (f : ∀ n, (D.stages n).sampleSpace → C),
    (∀ n x, f (n + 1) ((D.refinements n).map x) = f n x) →
    ∃! g : colimitCarrier → C, ∀ n x, g (inclusions n x) = f n x

/-- Continuum data over the directed finite system.  These are the
analytic/geometric targets carried by the chosen colimit object, not new
kernel-proved continuum theorems. -/
structure ColimitContinuumData (D : JaynesDirectedSystem) (IC : InductionColimit D) where
  kmsState : IC.colimitCarrier → ℝ
  kmsState_is_colimit : ∀ n x, kmsState (IC.inclusions n x) = (D.stages n).prob x
  buresMetric : IC.colimitCarrier → IC.colimitCarrier → ℝ
  buresMetric_is_colimit : ∀ n x y, buresMetric (IC.inclusions n x) (IC.inclusions n y) = Real.sqrt ((D.stages n).prob x * (D.stages n).prob y)
  gnsHilbertSpace : Type
  [gnsHilbertSpace_normed : NormedAddCommGroup gnsHilbertSpace]
  [gnsHilbertSpace_inner : InnerProductSpace ℝ gnsHilbertSpace]
  gnsVacuum : gnsHilbertSpace
  gns_is_colimit : ∀ n x, ∃ (v : gnsHilbertSpace), ‖v‖^2 = (D.stages n).prob x

/-- The complete theorem-object: finite Jaynes stages, colimit mechanism, and
continuum data targets. -/
structure ColimitBridge where
  finiteSide : JaynesDirectedSystem
  colimitMechanism : InductionColimit finiteSide
  continuum : ColimitContinuumData finiteSide colimitMechanism
  finitePropertiesLift_proof : ∀ n, StageKMS (finiteSide.stages n) →
    letI := (finiteSide.stages n).sampleSpace_fintype
    ∃ β, ∀ x,
      continuum.kmsState (colimitMechanism.inclusions n x) *
          (∑ ω' : (finiteSide.stages n).sampleSpace,
            Real.exp (- β * (finiteSide.stages n).finiteIntegralOfMotion ω')) =
        Real.exp (- β * (finiteSide.stages n).finiteIntegralOfMotion x)
  bridgeSlogan : String
  mechanismSlogan : String

/-- The finite-to-colimit lifting law exposed as a proposition from its owner. -/
def ColimitBridge.finitePropertiesLift (B : ColimitBridge) : Prop :=
  ∀ n, StageKMS (B.finiteSide.stages n) →
    letI := (B.finiteSide.stages n).sampleSpace_fintype
    ∃ β, ∀ x,
      B.continuum.kmsState (B.colimitMechanism.inclusions n x) *
          (∑ ω' : (B.finiteSide.stages n).sampleSpace,
            Real.exp (- β * (B.finiteSide.stages n).finiteIntegralOfMotion ω')) =
        Real.exp (- β * (B.finiteSide.stages n).finiteIntegralOfMotion x)

/-- If the bridge includes a proof that finite compatible properties lift, then
the recorded lifting statement is available. -/
theorem bridge_lifting (B : ColimitBridge) : B.finitePropertiesLift := B.finitePropertiesLift_proof

/-- The three-lineage slogan as explicit data. -/
structure ThreeLineagesConverge where
  leanKernelLine : String
  categoryLine : String
  jaynesLine : String
  commonPrinciple : String

/-- A canonical inhabitant of the slogan package. -/
def threeLineagesConverge : ThreeLineagesConverge :=
  { leanKernelLine := "infinity is controlled by inductive closure / successor"
    categoryLine := "infinity is represented by directed colimit bookkeeping"
    jaynesLine := "continuum probability is the stable limit of finite-set calculations"
    commonPrinciple := "finite generation + compatible refinement + universal colimit completion" }

/-- Synthesis: the file closes the finite packaging and exposes the continuum as
explicit colimit data. -/
theorem jaynes_lean_colimit_bridge_synthesis :
    (∀ S : FiniteJaynesSide, finiteExpectation S (fun _ => 1) = 1) ∧
    (∀ (D : JaynesDirectedSystem) (n : ℕ),
      StageKolmogorov (D.stages n) →
      StageKolmogorov (D.stages (n + 1))) ∧
    (∀ (D : JaynesDirectedSystem) (n : ℕ),
      StageKMS (D.stages n) →
      StageKMS (D.stages (n + 1))) := by
  constructor
  · intro S
    exact finiteExpectation_one S
  · constructor
    · intro D n h
      exact kolmogorov_succ D n h
    · intro D n h
      exact kms_succ D n h

end JaynesLeanColimitBridge
