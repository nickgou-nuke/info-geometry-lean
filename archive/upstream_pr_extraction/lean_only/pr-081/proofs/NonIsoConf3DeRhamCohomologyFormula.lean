import Mathlib
import proofs.NonIsoConf3DeRhamCooperad
import proofs.QuadraticConfiguration3

noncomputable section

namespace NonIsoConf3DeRhamCohomologyFormula

open Polynomial
open QuadraticConfiguration3
open NonIsoConf3DeRhamCooperad

/-- Formal Poincaré-polynomial for the rank-32 finite candidate.

For the three-point non-isotropic configuration space, this is

`(1+t)^3 (1+t^{D-1})^2`
-/
def lightConePoincareProduct (D : ℕ) : Polynomial ℤ :=
  (Polynomial.X + 1) ^ 3 * (Polynomial.X ^ (D - 1) + 1) ^ 2

/-- Formal Poincaré-polynomial for the OS-`α` finite alternative.

`(1+3t+2t^2)(1+t^{D-1})^2`.
-/
def lightConePoincareOS (D : ℕ) : Polynomial ℤ :=
  (1 + 3 * Polynomial.X + 2 * Polynomial.X ^ 2) * (Polynomial.X ^ (D - 1) + 1) ^ 2

/-- Pick the finite candidate by branch relation choice. -/
def lightConePoincareFromChoice (c : ModelChoice) (D : ℕ) : Polynomial ℤ :=
  match c with
  | ModelChoice.productLeray => lightConePoincareProduct D
  | ModelChoice.osAlpha => lightConePoincareOS D

/-- Poincaré polynomial chosen by the relation. -/
def deRhamBranchPoincare (D : ℕ) (S : ConcreteDeRhamCooperadData D) : Polynomial ℤ :=
  lightConePoincareFromChoice S.relationChoice D

/-- Arity-3 cooperad internal edge set for a chosen two-point/internal split. -/
def arityThreeInternalEdges (b : BlockDecomp3) : Finset Edge3 :=
  (Finset.univ : Finset Edge3).filter (fun e => cooperadEdge b e = TargetFactor.internal)

/-- Arity-3 cooperad outer edge set for a chosen two-point/internal split. -/
def arityThreeOuterEdges (b : BlockDecomp3) : Finset Edge3 :=
  (Finset.univ : Finset Edge3).filter (fun e => cooperadEdge b e = TargetFactor.outer)

/-- If the finite relation choice is the product/Leray candidate, the selected
polynomial is exactly the product/Leray Poincaré polynomial. -/
theorem deRhamBranchPoincare_product_formula {D : ℕ}
    (S : ConcreteDeRhamCooperadData D)
    (hchoice : S.relationChoice = ModelChoice.productLeray) :
    deRhamBranchPoincare D S = lightConePoincareProduct D := by
  simp [deRhamBranchPoincare, lightConePoincareFromChoice, hchoice]

/-- If the finite relation choice is OS-α, the selected polynomial is the OS-α
finite alternative. -/
theorem deRhamBranchPoincare_os_formula {D : ℕ}
    (S : ConcreteDeRhamCooperadData D)
    (hchoice : S.relationChoice = ModelChoice.osAlpha) :
    deRhamBranchPoincare D S = lightConePoincareOS D := by
  simp [deRhamBranchPoincare, lightConePoincareFromChoice, hchoice]

/-- `t=1` gives total rank 32 on the product/Leray branch. -/
theorem lightConeProduct_rank_at_one (D : ℕ) :
    Polynomial.eval 1 (lightConePoincareProduct D) = 32 := by
  simp [lightConePoincareProduct]

/-- `t=1` gives total rank 24 on the OS-α branch. -/
theorem lightConeOS_rank_at_one (D : ℕ) :
    Polynomial.eval 1 (lightConePoincareOS D) = 24 := by
  simp [lightConePoincareOS]

/-- Combined selection-and-rank statement for the product/Leray choice. -/
theorem deRhamBranch_product_and_rank {D : ℕ}
    (S : ConcreteDeRhamCooperadData D)
    (hchoice : S.relationChoice = ModelChoice.productLeray) :
    deRhamBranchPoincare D S = lightConePoincareProduct D ∧
      Polynomial.eval 1 (deRhamBranchPoincare D S) = 32 := by
  constructor
  · exact deRhamBranchPoincare_product_formula (D := D) S hchoice
  · rw [deRhamBranchPoincare_product_formula (D := D) S hchoice]
    exact lightConeProduct_rank_at_one D

/-- The two finite alternatives differ by rank 8. -/
theorem lightConeRankGap_at_one (D : ℕ) :
    Polynomial.eval 1 (lightConePoincareProduct D - lightConePoincareOS D) = 8 := by
  simp [lightConePoincareProduct, lightConePoincareOS]

/-- Under explicit branch choice, this transports the rank statement. -/
theorem deRhamBranch_rank_product (D : ℕ)
    (S : ConcreteDeRhamCooperadData D)
    (hchoice : S.relationChoice = ModelChoice.productLeray) :
    Polynomial.eval 1 (deRhamBranchPoincare D S) = 32 := by
  rw [deRhamBranchPoincare_product_formula (D := D) S hchoice]
  exact lightConeProduct_rank_at_one D

/-- Under explicit OS-α choice, this transports the rank statement. -/
theorem deRhamBranch_rank_os (D : ℕ)
    (S : ConcreteDeRhamCooperadData D)
    (hchoice : S.relationChoice = ModelChoice.osAlpha) :
    Polynomial.eval 1 (deRhamBranchPoincare D S) = 24 := by
  rw [deRhamBranchPoincare_os_formula (D := D) S hchoice]
  exact lightConeOS_rank_at_one D

/-- Each arity-3 split has exactly one internal edge and two outer edges. -/
theorem arityThree_cooperad_partition_counts (b : BlockDecomp3) :
    (arityThreeInternalEdges b).card = 1 ∧ (arityThreeOuterEdges b).card = 2 := by
  cases b
  · constructor
    · have h : arityThreeInternalEdges BlockDecomp3.pair12_3 = {Edge3.e12} := by
        ext e
        cases e <;> simp [arityThreeInternalEdges, cooperadEdge]
      simp [h]
    · have h :
          arityThreeOuterEdges BlockDecomp3.pair12_3 = {Edge3.e13, Edge3.e23} := by
        ext e
        cases e <;> simp [arityThreeOuterEdges, cooperadEdge]
      simp [h]
  · constructor
    · have h : arityThreeInternalEdges BlockDecomp3.pair13_2 = {Edge3.e13} := by
        ext e
        cases e <;> simp [arityThreeInternalEdges, cooperadEdge]
      simp [h]
    · have h :
          arityThreeOuterEdges BlockDecomp3.pair13_2 = {Edge3.e12, Edge3.e23} := by
        ext e
        cases e <;> simp [arityThreeOuterEdges, cooperadEdge]
      simp [h]
  · constructor
    · have h : arityThreeInternalEdges BlockDecomp3.pair23_1 = {Edge3.e23} := by
        ext e
        cases e <;> simp [arityThreeInternalEdges, cooperadEdge]
      simp [h]
    · have h :
          arityThreeOuterEdges BlockDecomp3.pair23_1 = {Edge3.e12, Edge3.e13} := by
        ext e
        cases e <;> simp [arityThreeOuterEdges, cooperadEdge]
      simp [h]

/-- Combined finite conclusion for the pairwise non-isotropic three-point space under
an explicit choice of the finite branch: Poincaré polynomial and cooperad edge
partitioning.

This is a formal consequence of the branch choice field in
`ConcreteDeRhamCooperadData`; identification with actual
`Conf_Q(ℂ^D,3)` is intentionally not asserted here.
-/
theorem deRham_cohomology_and_cooperad_if_product
    {D : ℕ}
    (S : ConcreteDeRhamCooperadData D)
    (hchoice : S.relationChoice = ModelChoice.productLeray) :
    deRhamBranchPoincare D S = lightConePoincareProduct D ∧
      Polynomial.eval 1 (deRhamBranchPoincare D S) = 32 ∧
      (∀ b : BlockDecomp3, (arityThreeInternalEdges b).card = 1) ∧
      (∀ b : BlockDecomp3, (arityThreeOuterEdges b).card = 2) := by
  constructor
  · exact deRhamBranchPoincare_product_formula (D := D) S hchoice
  constructor
  · rw [deRhamBranchPoincare_product_formula (D := D) S hchoice]
    exact lightConeProduct_rank_at_one D
  constructor
  · intro b
    exact (arityThree_cooperad_partition_counts b).1
  · intro b
    exact (arityThree_cooperad_partition_counts b).2

end NonIsoConf3DeRhamCohomologyFormula
