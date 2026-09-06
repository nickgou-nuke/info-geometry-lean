import proofs.QuadraticConfiguration3
import proofs.LightConeConf3DeRhamCooperad
import proofs.NonIsoConf3DeRhamCohomologyFormula

/-!
# Light-cone quadric formalization for `Conf_Q(ℂ^D,3)`

This file collects the finite Lean consequences in one place under a
single naming convention:

* the light-cone quadric configuration is the same finite presentation used by
  `QuadraticConfiguration3` (standard quadratic form `q(x)=Σ_i x_i^2`),
* arity-3 cooperad splitting for `{1,2}|{3}` has one internal and two outer
  edges,
* under explicit `ModelChoice.productLeray`, the finite Poincaré candidate is
  `(1+t)^3(1+t^(D-1))^2` with total rank `32`.

This module only states the finite branch consequences proved by the imported
de Rham/cooperad model.
-/

namespace NonIsoConf3LightConeQuadricSummary

open QuadraticConfiguration3
open LightConeConf3DeRhamCooperad
open NonIsoConf3DeRhamCooperad
open NonIsoConf3DeRhamCohomologyFormula

/-- `Config3` is the light-cone non-isotropic configuration model in this project. -/
abbrev LightConeConfig3 (D : ℕ) := Config3 D

/-- The light-cone model is definitionally the same as `Config3`. -/
@[simp] theorem lightConeConfig3_eq_Config3 (D : ℕ) :
    LightConeConfig3 D = Config3 D := by
  rfl

/-- The chosen quadratic form is the standard light-cone form `q(x)=∑ x_i^2`. -/
theorem lightConeQuadraticForm (D : ℕ) (x : V D) :
    QuadraticConfiguration3.q D x = ∑ i : Fin D, x i * x i := by
  rfl

/-- For the standard presentation, this is just the configuration structure field
bundle itself: nonisotropic pairwise separations are exactly the three explicit
hypotheses. -/
theorem lightConeConfig3_pairwise_nonisotropic (D : ℕ) (C : LightConeConfig3 D) :
    q D (diff C.x1 C.x2) ≠ 0 ∧
      q D (diff C.x1 C.x3) ≠ 0 ∧
      q D (diff C.x2 C.x3) ≠ 0 := by
  constructor
  · exact C.h12
  constructor
  · exact C.h13
  · exact C.h23

/-- Cooperad split for the arity-3 light-cone configuration.

`12|3` sends edge `12` internally, while `13` and `23` are outer.
-/
theorem lightCone_arity3_cooperad_split :
    (collapse12 Edge3.e12 = ClusterSlot.inner) ∧
    (collapse12 Edge3.e13 = ClusterSlot.outer) ∧
    (collapse12 Edge3.e23 = ClusterSlot.outer) := by
  constructor
  · exact collapse12_e12
  constructor
  · exact collapse12_e13
  · exact collapse12_e23

/-- Finite ranks of the two candidates at the light-cone arity-three level.
-/
theorem lightCone_candidate_ranks :
    Fintype.card LightConeProductBasis = 32 ∧ Fintype.card OSFluxBasis = 24 := by
  constructor
  · exact lightConeProductBasis_card
  · exact lightConeOSAlternative_card

/-- Rank-gap signature.
-/
theorem lightCone_rank_gap :
    Fintype.card LightConeProductBasis - Fintype.card OSFluxBasis = 8 := by
  rw [product_vs_os_rank_gap]

/-- Cooperad-independent count: for each arity-three block decomposition,
there is exactly one internal and two outer edges.
-/
theorem lightCone_three_block_partition_counts (b : BlockDecomp3) :
    (arityThreeInternalEdges b).card = 1 ∧ (arityThreeOuterEdges b).card = 2 := by
  constructor
  · exact (arityThree_cooperad_partition_counts b).1
  · exact (arityThree_cooperad_partition_counts b).2

/-- Environmentally decomposed Cooperad split `{1,2}|{3}` preserves rank 32 in the
pairwise non-isotropic light-cone model.
-/
theorem lightCone_pair12_environmental_decomposition_preserves_quadric_rank32
    (D : ℕ)
    (S : ConcreteDeRhamCooperadData D)
    (hchoice : S.relationChoice = ModelChoice.productLeray) :
    deRhamBranchPoincare D S = lightConePoincareProduct D ∧
    Polynomial.eval 1 (deRhamBranchPoincare D S) = 32 ∧
    (arityThreeInternalEdges BlockDecomp3.pair12_3).card = 1 ∧
    (arityThreeOuterEdges BlockDecomp3.pair12_3).card = 2 := by
  constructor
  · simpa using (deRhamBranch_product_and_rank (D := D) S hchoice).1
  constructor
  · simpa using (deRhamBranch_product_and_rank (D := D) S hchoice).2
  constructor
  · simpa using (arityThree_cooperad_partition_counts BlockDecomp3.pair12_3).1
  · simpa using (arityThree_cooperad_partition_counts BlockDecomp3.pair12_3).2

end NonIsoConf3LightConeQuadricSummary
