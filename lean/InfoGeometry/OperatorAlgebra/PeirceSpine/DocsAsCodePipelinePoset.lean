/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.EpistemicCompilerPeirceBridge
import Mathlib.Tactic.NoncommRing

/-!
# D₄₈: a Peirce-ring model of a documentation pipeline

The constructions here model corner support, finite graph paths, branch
conjugation, and triangular operator composition. They do not formalize a
MkDocs/Jinja/AWS implementation or assert deployment idempotence for an
external software system.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.OperatorAlgebra.ThreeCornerColumnAlgebra (third)

variable {B : Type*} [Ring B]

def docsCodeSector (P X : B) : B := peirce11 P X
def docsOutputSector (P X : B) : B := (1 - P) * X * (1 - P)

/-- A context value is carried from the `P` corner through the lower cone and
lands in the complementary diagonal corner. -/
def jinjaContextRender (P A C X : B) : B :=
  coneMinus P C * docsCodeSector P X * conePlus P A

def mermaidPipeline (P₁ P₂ A C : B) : B :=
  twoStepUpper P₁ P₂ A C

/-- Unipotent conjugates of the source idempotent model the two branch states. -/
def docsFeatureBranch (P A : B) : B :=
  (1 + conePlus P A) * P * (1 - conePlus P A)

def docsReviewBranch (P C : B) : B :=
  (1 + coneMinus P C) * P * (1 - coneMinus P C)

def docsMergeToMain (P A Pbranch : B) : B :=
  (1 - conePlus P A) * Pbranch * (1 + conePlus P A)

/-- Lower-triangular operator with source diagonal, transition, and target
diagonal blocks. -/
def docsPipelineOp (P F Bbuild D : B) : B :=
  blockLower P F Bbuild D

def docsDeployProjection (P Bbuild : B) : B := P + coneMinus P Bbuild

theorem docs_as_code_jinja_context_corner {P : B} (hP : P * P = P)
    (A C X : B) :
    docsOutputSector P (jinjaContextRender P A C X) =
      jinjaContextRender P A C X ∧
    P * jinjaContextRender P A C X = 0 ∧
    jinjaContextRender P A C 1 = qgtMinus P A C := by
  refine ⟨?_, ?_, ?_⟩
  · unfold docsOutputSector jinjaContextRender docsCodeSector
    peirce_nf hP
  · unfold jinjaContextRender docsCodeSector
    peirce_nf hP
  · unfold jinjaContextRender docsCodeSector qgtMinus
    peirce_nf hP

theorem mermaid_pipeline_resolvent
    {P₁ P₂ : B} (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0) (A C : B) :
    mermaidPipeline P₁ P₂ A C * mermaidPipeline P₁ P₂ A C =
      P₁ * A * P₂ * C * third P₁ P₂ ∧
    mermaidPipeline P₁ P₂ A C * mermaidPipeline P₁ P₂ A C *
      mermaidPipeline P₁ P₂ A C = 0 ∧
    (1 - mermaidPipeline P₁ P₂ A C) *
      twoStepResolvent P₁ P₂ A C = 1 ∧
    twoStepResolvent P₁ P₂ A C *
      (1 - mermaidPipeline P₁ P₂ A C) = 1 := by
  simpa [mermaidPipeline] using
    three_layer_poset_resolvent h1 h2 h12 h21 A C

theorem docs_gitflow_branch_and_merge {P : B} (hP : P * P = P) (A C : B) :
    docsFeatureBranch P A * docsFeatureBranch P A = docsFeatureBranch P A ∧
    docsReviewBranch P C * docsReviewBranch P C = docsReviewBranch P C ∧
    docsReviewBranch P C - docsFeatureBranch P A = genPhi P A C ∧
    (docsReviewBranch P C - docsFeatureBranch P A) *
      (docsReviewBranch P C - docsFeatureBranch P A) = genV P A C ∧
    docsMergeToMain P A (docsFeatureBranch P A) = P := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [docsFeatureBranch]
    peirce_nf hP
  · simp only [docsReviewBranch]
    peirce_nf hP
  · simp only [docsReviewBranch, docsFeatureBranch, genPhi]
    peirce_nf hP
  · simp only [docsReviewBranch, docsFeatureBranch, genPhi, genV, anticomm]
    peirce_nf hP
  · simp only [docsMergeToMain, docsFeatureBranch]
    peirce_nf hP

theorem docs_pipeline_idempotency_and_composition {P : B}
    (hP : P * P = P) (Bbuild F₁ B₁ D₁ F₂ B₂ D₂ : B) :
    docsDeployProjection P Bbuild * docsDeployProjection P Bbuild =
      docsDeployProjection P Bbuild ∧
    P * docsPipelineOp P F₁ B₁ D₁ * (1 - P) = 0 ∧
    docsCodeSector P (docsPipelineOp P F₁ B₁ D₁) = docsCodeSector P F₁ ∧
    docsPipelineOp P F₁ B₁ D₁ * docsPipelineOp P F₂ B₂ D₂ =
      docsPipelineOp P (F₁ * P * F₂)
        (B₁ * P * F₂ + D₁ * (1 - P) * B₂)
        (D₁ * (1 - P) * D₂) := by
  have hPc : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  have hcP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have hcIdem : (1 - P) * (1 - P) = 1 - P := by
    noncomm_ring [hP]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold docsDeployProjection
    have hN0 : coneMinus P Bbuild * coneMinus P Bbuild = 0 :=
      coneMinus_mul_coneMinus hP Bbuild Bbuild
    have hPN : P * coneMinus P Bbuild = 0 := P_mul_coneMinus hP Bbuild
    have hNP : coneMinus P Bbuild * P = coneMinus P Bbuild :=
      coneMinus_mul_P hP Bbuild
    noncomm_ring [hP, hN0, hPN, hNP]
  · change P * blockLower P F₁ B₁ D₁ * (1 - P) = 0
    exact blockLower_upper_right hP F₁ B₁ D₁
  · change peirce11 P (blockLower P F₁ B₁ D₁) = peirce11 P F₁
    exact blockLower_peirce11 hP F₁ B₁ D₁
  · exact blockLower_mul hP F₁ B₁ D₁ F₂ B₂ D₂

/-- Synthesis of the five finite algebraic stages. The names of external
software components motivate the stages; the theorem's scope is the ring
identities in its type. -/
theorem stage_D48_docs_as_code_pipeline_master
    {P P₁ P₂ : B} (hP : P * P = P)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (A C X Bbuild F₁ B₁ D₁ F₂ B₂ D₂ : B) :
    docsOutputSector P (jinjaContextRender P A C X) =
      jinjaContextRender P A C X ∧
    jinjaContextRender P A C 1 = qgtMinus P A C ∧
    mermaidPipeline P₁ P₂ A C * mermaidPipeline P₁ P₂ A C *
      mermaidPipeline P₁ P₂ A C = 0 ∧
    (1 - mermaidPipeline P₁ P₂ A C) * twoStepResolvent P₁ P₂ A C = 1 ∧
    docsReviewBranch P C - docsFeatureBranch P A = genPhi P A C ∧
    (docsReviewBranch P C - docsFeatureBranch P A) *
      (docsReviewBranch P C - docsFeatureBranch P A) = genV P A C ∧
    docsMergeToMain P A (docsFeatureBranch P A) = P ∧
    docsDeployProjection P Bbuild * docsDeployProjection P Bbuild =
      docsDeployProjection P Bbuild ∧
    docsCodeSector P (docsPipelineOp P F₁ B₁ D₁) = docsCodeSector P F₁ ∧
    docsPipelineOp P F₁ B₁ D₁ * docsPipelineOp P F₂ B₂ D₂ =
      docsPipelineOp P (F₁ * P * F₂)
        (B₁ * P * F₂ + D₁ * (1 - P) * B₂)
        (D₁ * (1 - P) * D₂) := by
  rcases docs_as_code_jinja_context_corner hP A C X with ⟨hJ1, _, hJ3⟩
  rcases mermaid_pipeline_resolvent h1 h2 h12 h21 A C with
    ⟨_, hM2, hM3, _⟩
  rcases docs_gitflow_branch_and_merge hP A C with
    ⟨_, _, hG3, hG4, hG5⟩
  rcases docs_pipeline_idempotency_and_composition hP Bbuild F₁ B₁ D₁ F₂ B₂ D₂ with
    ⟨hC1, _, hC3, hC4⟩
  exact ⟨hJ1, hJ3, hM2, hM3, hG3, hG4, hG5, hC1, hC3, hC4⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine
