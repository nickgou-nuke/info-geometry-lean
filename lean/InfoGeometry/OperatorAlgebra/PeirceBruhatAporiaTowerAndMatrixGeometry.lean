/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.Core.NewtonIdempotentCorrection
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Meta.EpistemicCompilerChain
import InfoGeometry.Meta.MetaEpistemicCompiler
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic.FinCases

/-!
# Peirce–Bruhat–Aporia Poset and Noncommutative Matrix Geometry

Epistemic compilation (`solve et coagula`) translating non-abelian dichotomy,
fourfold Peirce decomposition, Bruhat perspective conjugation, iterated
idempotency-defect towers, and quadratic Newton–Peirce convergence into
native Mathlib + Lean 4 noncommutative ring and block-matrix theorems.

Upstream philosophical or symbolic labels in design provenance carry no
semantic content beyond the kernel-checked noncommutative `[Ring B]`,
`[StarRing B]`, and `Matrix (Fin 2) (Fin 2)` propositions declared below.

## Causal Poset (`CoagulationArchetype`)

`S1_binaryCut ≤ S2_fourfoldPeirce ≤ {S3_transcendentBruhat, S4_aporiaDefectTower} ≤ S5_covariantMetaTower ≤ S6_noncommMatrixCoagulation`

* **S1 (`S1_binaryCut`)**: Noncommutative idempotent cut `P * P = P`, complementary
  involution `invS P`, grading derivation `peirceGradingDeriv P`, and exact
  characteristic-free commutant characterization (`binaryCut_commutant_characterization`).
* **S2 (`S2_fourfoldPeirce`)**: Complete orthogonal partition into the four Peirce
  corners `(peirce11, conePlus, coneMinus, peirce00)` and exact noncommutative
  quiver multiplication rules (`fourfold_peirce_noncomm_mul_blocks`).
* **S3 (`S3_transcendentBruhat`)**: Opposite-corner generators `(Φ, J, V, Σ)`,
  unipotent Bruhat unit `chartBruhatUnit`, ring automorphism
  `chartBruhatRingEquiv : B ≃+* B`, rotated-cut invariance (`bruhatPerspective_rotatedCut_and_metric_invariance`),
  and `[StarRing B]` self/skew-adjoint Gram factorization (`star_transcendent_adjoint_and_gram_factorization`).
* **S4 (`S4_aporiaDefectTower`)**: Iterated idempotency defect `idempotencyDefect^[n]`,
  Newton–Peirce flow `newtonPeirceStep^[k]`, one-sided annihilation/intertwining/transport,
  and all-`k` noncommutative `2^k`-power factorization (`idempotencyDefect_newtonPeirceStep_iterate_factor`).
* **S5 (`S5_covariantMetaTower`)**: Coagulated join of `S3` and `S4`:
  pinched rotated-cut defect law (`pinched_bruhatPerspective_defect_eq_genV_defect`),
  Sylvester cone intertwining at all Newton–Peirce depths, Maurer–Cartan covariant
  constancy (`peirceCovariantDeriv = 0`), and Bruhat invariance across both meta-towers.
* **S6 (`S6_noncommMatrixCoagulation`)**: Block-matrix `M₂(B)` realization over
  arbitrary noncommutative `[Ring B]`, three explicit noncommutative matrix witnesses
  refuting commutative/one-step simplifications, universal synthesis theorem, and
  certified `MetaEpistemicCompiler` schedule + `#register_archetype` closure.

## Three-Bucket Audit Map

* **BUCKET 1 (Reused upstream owners)**:
  - `InfoGeometry.Core.IdempotentGraphGrassmannian`: `idempotencyDefect`,
    `idempotencyDefect_eq_zero_iff`, `idempotencyDefect_add_of_orthogonal`,
    `idempotencyDefect_iterates_add_of_orthogonal`, `map_idempotencyDefect_iterates`,
    `idempotencyDefect_iterates_intertwines`, `idempotencyDefect_iterates_left_support`,
    `idempotencyDefect_iterates_right_support`, `newtonPeirceStep`,
    `idempotencyDefect_newtonPeirceStep`.
  - `InfoGeometry.OperatorAlgebra.PeirceSpine`: `conePlus`, `coneMinus`,
    `peirce11`, `peirce00`, `evenGrade`, `oddGrade`, `genPhi`, `genJ`, `genV`, `genSig`,
    `qgtPlus`, `qgtMinus`, `parityConj`, `invS`, `chartBruhatConj`, `chartBruhatConjInv`,
    `chart_bruhat_factor_mul_inv`, `chartBruhatConj_mul`, `chartBruhatConj_genV`,
    `chartBruhatConj_one_sub_genV`, `chart_bruhat_conjugate_peirce_blocks`,
    `chart_bruhat_conjugation_transition`, `grade_projection_laws`,
    `archetype_A2_peirce_cartan_grading_and_tangent_closure`,
    `archetype_A3_nilpotent_cones_and_tetraktys_table`, `qgt_cycles_orthogonal`,
    `genV_defect_cycle_split`, `genV_defect_iterates_cycle_split`,
    `qgtPlus_defect_iterates_left`, `qgtPlus_defect_iterates_right`,
    `qgtMinus_defect_iterates_left`, `qgtMinus_defect_iterates_right`,
    `genV_defect_iterates_left_projection`, `genV_defect_iterates_right_projection`,
    `qgt_cycles_cone_relations`, `qgt_defect_iterate_sum_commutes_with_generators`.
  - `InfoGeometry.OperatorAlgebra.PeirceDefectBridge`: `peirceGradingDeriv`,
    `peirceCovariantDeriv`, `peirceMaurerCartanCurvature`.
  - `InfoGeometry.MetaCompiler`: `TypedArchetype`, `Status`, `Phase`,
    `executable_certified_compilation`, `#register_archetype`, `#audit_archetype`.
* **BUCKET 2 (New theorems proved here)**:
  - Diamond poset `CoagulationArchetype` with certified parallel schedules.
  - Complete characteristic-free four-way commutant equivalence `binaryCut_commutant_characterization`.
  - All-16 corner composition and noncommutative quiver multiplication laws
    `fourfold_peirce_orthogonality_and_completeness`, `fourfold_peirce_noncomm_mul_blocks`.
  - Genuine `Bˣ` (`chartBruhatUnit`) and `B ≃+* B` (`chartBruhatRingEquiv`) promotions,
    plus `star_transcendent_adjoint_and_gram_factorization`.
  - Full `newtonPeirceStep^[k]` orbit theorems (one-sided annihilation, orthogonal
    splitting, intertwining, support preservation, `RingHom` transport) and
    `idempotencyDefect_newtonPeirceStep_iterate_factor` (`(idempotencyDefect x) ^ (2 ^ k)` factor).
  - Pinched Bruhat-cut defect theorem and all-depth covariant constancy across both towers.
  - Noncommutative fiber block-matrix `diag2RingHom`, three concrete `M₂(M₂(ℤ))` / `M₂(ℤ)`
    counterexample/witness theorems, master synthesis theorem, and `TypedArchetype` closure.
* **BUCKET 3 (Out-of-scope / excluded)**:
  - Infinite-dimensional operator-norm convergence, spectral radius bounds, smooth
    manifold differential geometry, and continuum physical/Kubo transport claims.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry

open Matrix
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.ProofCarryingSchedule
open InfoGeometry.MetaCompiler

/-! ## Section 1: Bounded Acyclic Diamond Causal Poset (`CoagulationArchetype`) -/

/-- Six-stage noncommutative epistemic coagulation poset forming a diamond DAG:
`S1` → `S2` → `{S3 ∥ S4}` → `S5` → `S6`. -/
inductive CoagulationArchetype
  | S1_binaryCut
  | S2_fourfoldPeirce
  | S3_transcendentBruhat
  | S4_aporiaDefectTower
  | S5_covariantMetaTower
  | S6_noncommMatrixCoagulation
  deriving DecidableEq, Repr, Inhabited

namespace CoagulationArchetype

private def equivFin : CoagulationArchetype ≃ Fin 6 where
  toFun
    | .S1_binaryCut => 0
    | .S2_fourfoldPeirce => 1
    | .S3_transcendentBruhat => 2
    | .S4_aporiaDefectTower => 3
    | .S5_covariantMetaTower => 4
    | .S6_noncommMatrixCoagulation => 5
  invFun
    | 0 => .S1_binaryCut
    | 1 => .S2_fourfoldPeirce
    | 2 => .S3_transcendentBruhat
    | 3 => .S4_aporiaDefectTower
    | 4 => .S5_covariantMetaTower
    | _ => .S6_noncommMatrixCoagulation
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance instFintype : Fintype CoagulationArchetype :=
  Fintype.ofEquiv (Fin 6) equivFin.symm

/-- Downward-closed causal prerequisites defining the diamond poset. -/
def prerequisites : CoagulationArchetype → Finset CoagulationArchetype
  | .S1_binaryCut => {.S1_binaryCut}
  | .S2_fourfoldPeirce => {.S1_binaryCut, .S2_fourfoldPeirce}
  | .S3_transcendentBruhat =>
      {.S1_binaryCut, .S2_fourfoldPeirce, .S3_transcendentBruhat}
  | .S4_aporiaDefectTower =>
      {.S1_binaryCut, .S2_fourfoldPeirce, .S4_aporiaDefectTower}
  | .S5_covariantMetaTower =>
      {.S1_binaryCut, .S2_fourfoldPeirce, .S3_transcendentBruhat,
       .S4_aporiaDefectTower, .S5_covariantMetaTower}
  | .S6_noncommMatrixCoagulation =>
      {.S1_binaryCut, .S2_fourfoldPeirce, .S3_transcendentBruhat,
       .S4_aporiaDefectTower, .S5_covariantMetaTower, .S6_noncommMatrixCoagulation}

instance instPartialOrder : PartialOrder CoagulationArchetype where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro a b
    cases a <;> cases b <;> decide

instance instDecidableLE : DecidableLE CoagulationArchetype := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

instance instDecidableLT : DecidableLT CoagulationArchetype := fun a b =>
  decidable_of_iff (a ≤ b ∧ ¬ b ≤ a) lt_iff_le_not_ge.symm

/-- The causal poset has unique bottom `S1_binaryCut`, unique top `S6_noncommMatrixCoagulation`,
strict cover edges of a diamond DAG, and genuinely incomparable parallel branches
`S3_transcendentBruhat` and `S4_aporiaDefectTower`. -/
theorem coagulationPoset_diamond_structure :
    (∀ x : CoagulationArchetype,
      CoagulationArchetype.S1_binaryCut ≤ x ∧ x ≤ CoagulationArchetype.S6_noncommMatrixCoagulation) ∧
    (CoagulationArchetype.S1_binaryCut < CoagulationArchetype.S2_fourfoldPeirce ∧
      CoagulationArchetype.S2_fourfoldPeirce < CoagulationArchetype.S3_transcendentBruhat ∧
      CoagulationArchetype.S2_fourfoldPeirce < CoagulationArchetype.S4_aporiaDefectTower ∧
      CoagulationArchetype.S3_transcendentBruhat < CoagulationArchetype.S5_covariantMetaTower ∧
      CoagulationArchetype.S4_aporiaDefectTower < CoagulationArchetype.S5_covariantMetaTower ∧
      CoagulationArchetype.S5_covariantMetaTower < CoagulationArchetype.S6_noncommMatrixCoagulation) ∧
    (¬ (CoagulationArchetype.S3_transcendentBruhat ≤ CoagulationArchetype.S4_aporiaDefectTower) ∧
      ¬ (CoagulationArchetype.S4_aporiaDefectTower ≤ CoagulationArchetype.S3_transcendentBruhat)) := by
  decide

/-- Deliberately reversed input worklist forcing the deterministic dependency compiler
to recover a valid topological schedule from the partial order. -/
def canonicalPending : List CoagulationArchetype :=
  [.S6_noncommMatrixCoagulation, .S5_covariantMetaTower, .S4_aporiaDefectTower,
   .S3_transcendentBruhat, .S2_fourfoldPeirce, .S1_binaryCut]

/-- Linearization ordering the Bruhat branch (`S3`) before the defect-tower branch (`S4`). -/
def scheduleBruhatFirst : List CoagulationArchetype :=
  [.S1_binaryCut, .S2_fourfoldPeirce, .S3_transcendentBruhat,
   .S4_aporiaDefectTower, .S5_covariantMetaTower, .S6_noncommMatrixCoagulation]

/-- Linearization ordering the defect-tower branch (`S4`) before the Bruhat branch (`S3`). -/
def scheduleAporiaFirst : List CoagulationArchetype :=
  [.S1_binaryCut, .S2_fourfoldPeirce, .S4_aporiaDefectTower,
   .S3_transcendentBruhat, .S5_covariantMetaTower, .S6_noncommMatrixCoagulation]

theorem canonicalPending_nodup : canonicalPending.Nodup := by decide

theorem canonicalPending_univ : canonicalPending.toFinset = Finset.univ := by decide

/-- Both parallel linearizations are valid causal schedules, and they are distinct,
witnessing nontrivial concurrency between `S3_transcendentBruhat` and `S4_aporiaDefectTower`. -/
theorem two_distinct_valid_topological_schedules :
    ValidSchedule ∅ scheduleBruhatFirst ∧
    ValidSchedule ∅ scheduleAporiaFirst ∧
    scheduleBruhatFirst ≠ scheduleAporiaFirst ∧
    compile (∅ : Finset CoagulationArchetype) canonicalPending = some scheduleAporiaFirst := by
  decide

end CoagulationArchetype

/-! ## Section 2 (`S1_binaryCut`): Noncommutative Binary Cut & Commutant Characterization -/

section Stage1_BinaryCut

variable {B : Type*} [Ring B]

/-- Complementary idempotent laws, involutive grading operator `invS P`, and vanishing
of the grading derivation on the cut itself. -/
theorem binaryCut_split_and_grading_involution {P : B} (hP : P * P = P) :
    (1 - P) * (1 - P) = 1 - P ∧
    P * (1 - P) = 0 ∧
    (1 - P) * P = 0 ∧
    invS P * invS P = 1 ∧
    peirceGradingDeriv P P = 0 ∧
    peirceGradingDeriv P (1 - P) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · noncomm_ring [hP]
  · noncomm_ring [hP]
  · noncomm_ring [hP]
  · unfold invS; noncomm_ring [hP]
  · unfold peirceGradingDeriv PeirceSpine.comm; noncomm_ring
  · unfold peirceGradingDeriv PeirceSpine.comm; noncomm_ring

/-- Characteristic-free characterization of commuting with an idempotent cut `P`
in an arbitrary associative ring `B` (without requiring `Invertible (2 : B)`). -/
theorem binaryCut_commutant_characterization
    {P : B} (hP : P * P = P) (X : B) :
    (P * X = X * P ↔ peirceGradingDeriv P X = 0) ∧
    (peirceGradingDeriv P X = 0 ↔ oddGrade P X = 0) ∧
    (oddGrade P X = 0 ↔ evenGrade P X = X) ∧
    (P * X = X * P → parityConj P X = X) := by
  have h1 : P * X = X * P ↔ peirceGradingDeriv P X = 0 := by
    unfold peirceGradingDeriv PeirceSpine.comm
    exact sub_eq_zero.symm
  have hA2 := archetype_A2_peirce_cartan_grading_and_tangent_closure hP X X
  have hOddComm : PeirceSpine.comm P (PeirceSpine.comm P X) = oddGrade P X := hA2.2.1
  have hTripleComm :
      PeirceSpine.comm P (PeirceSpine.comm P (PeirceSpine.comm P X)) =
        PeirceSpine.comm P X := hA2.2.2.2.1
  have h2 : peirceGradingDeriv P X = 0 ↔ oddGrade P X = 0 := by
    constructor
    · intro hDeriv
      unfold peirceGradingDeriv at hDeriv
      rw [← hOddComm, hDeriv]
      simp [PeirceSpine.comm]
    · intro hOdd
      unfold peirceGradingDeriv
      rw [← hTripleComm, hOddComm, hOdd]
      simp [PeirceSpine.comm]
  have hDecomp : evenGrade P X + oddGrade P X = X := (grade_projection_laws hP X).2.2.2.2
  have h3 : oddGrade P X = 0 ↔ evenGrade P X = X := by
    constructor
    · intro hOdd
      rw [hOdd, add_zero] at hDecomp
      exact hDecomp
    · intro hEven
      rw [hEven] at hDecomp
      calc
        oddGrade P X = (X + oddGrade P X) - X := by abel
        _ = X - X := by rw [hDecomp]
        _ = 0 := sub_self X
  refine ⟨h1, h2, h3, ?_⟩
  intro hCom
  have hEven : evenGrade P X = X := h3.mp (h2.mp (h1.mp hCom))
  rw [← hEven]
  unfold parityConj
  peirce_nf hP

end Stage1_BinaryCut

/-! ## Section 3 (`S2_fourfoldPeirce`): Fourfold Peirce Anatomy & Quiver Multiplication -/

section Stage2_FourfoldPeirce

variable {B : Type*} [Ring B]

/-- The four Peirce maps `(peirce11, conePlus, coneMinus, peirce00)` form a complete
system of mutually orthogonal linear projections decomposing every operator `X : B`. -/
theorem fourfold_peirce_orthogonality_and_completeness
    {P : B} (hP : P * P = P) (X : B) :
    peirce11 P X + conePlus P X + coneMinus P X + peirce00 P X = X ∧
    peirce11 P X + peirce00 P X = evenGrade P X ∧
    conePlus P X + coneMinus P X = oddGrade P X ∧
    peirce11 P (peirce11 P X) = peirce11 P X ∧
    conePlus P (conePlus P X) = conePlus P X ∧
    coneMinus P (coneMinus P X) = coneMinus P X ∧
    peirce00 P (peirce00 P X) = peirce00 P X ∧
    (peirce11 P (conePlus P X) = 0 ∧ peirce11 P (coneMinus P X) = 0 ∧
      peirce11 P (peirce00 P X) = 0) ∧
    (conePlus P (peirce11 P X) = 0 ∧ conePlus P (coneMinus P X) = 0 ∧
      conePlus P (peirce00 P X) = 0) ∧
    (coneMinus P (peirce11 P X) = 0 ∧ coneMinus P (conePlus P X) = 0 ∧
      coneMinus P (peirce00 P X) = 0) ∧
    (peirce00 P (peirce11 P X) = 0 ∧ peirce00 P (conePlus P X) = 0 ∧
      peirce00 P (coneMinus P X) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    (simp only [peirce11, peirce00, conePlus, coneMinus, evenGrade, oddGrade] <;> peirce_nf hP)

/-- Exact noncommutative `2 × 2` quiver multiplication rules for the four Peirce blocks
of a product `X * Y`, preserving noncommutative factor order. -/
theorem fourfold_peirce_noncomm_mul_blocks
    {P : B} (hP : P * P = P) (X Y : B) :
    peirce11 P (X * Y) = peirce11 P X * peirce11 P Y + conePlus P X * coneMinus P Y ∧
    conePlus P (X * Y) = peirce11 P X * conePlus P Y + conePlus P X * peirce00 P Y ∧
    coneMinus P (X * Y) = coneMinus P X * peirce11 P Y + peirce00 P X * coneMinus P Y ∧
    peirce00 P (X * Y) = coneMinus P X * conePlus P Y + peirce00 P X * peirce00 P Y := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [peirce11, peirce00, conePlus, coneMinus]; peirce_nf hP)

end Stage2_FourfoldPeirce

/-! ## Section 4 (`S3_transcendentBruhat`): Bruhat Perspective Automorphism & `StarRing` Duality -/

section Stage3_TranscendentBruhat

variable {B : Type*} [Ring B]

/-- The unipotent two-factor Bruhat transition element `(1 + N₊)(1 - N₋)` bundled as a
genuine group unit `Bˣ` with inverse `(1 + N₋)(1 - N₊)`. -/
def chartBruhatUnit {P : B} (hP : P * P = P) (A C : B) : Bˣ where
  val := (1 + conePlus P A) * (1 - coneMinus P C)
  inv := (1 + coneMinus P C) * (1 - conePlus P A)
  val_inv := (chart_bruhat_factor_mul_inv hP A C).1
  inv_val := (chart_bruhat_factor_mul_inv hP A C).2

/-- Perspectival Bruhat conjugation promoted to a genuine ring automorphism `B ≃+* B`. -/
def chartBruhatRingEquiv {P : B} (hP : P * P = P) (A C : B) : B ≃+* B where
  toFun := chartBruhatConj P A C
  invFun := chartBruhatConjInv P A C
  left_inv X := by
    have h1 := (chart_bruhat_factor_mul_inv hP A C).1
    have h2 := (chart_bruhat_factor_mul_inv hP A C).2
    unfold chartBruhatConj chartBruhatConjInv
    calc
      (1 + coneMinus P C) * (1 - conePlus P A) *
          ((1 + conePlus P A) * (1 - coneMinus P C) * X *
            (1 + coneMinus P C) * (1 - conePlus P A)) *
          (1 + conePlus P A) * (1 - coneMinus P C)
          = (((1 + coneMinus P C) * (1 - conePlus P A)) *
              ((1 + conePlus P A) * (1 - coneMinus P C))) * X *
            (((1 + coneMinus P C) * (1 - conePlus P A)) *
              ((1 + conePlus P A) * (1 - coneMinus P C))) := by
            simp only [mul_assoc]
      _ = 1 * X * 1 := by rw [h2]
      _ = X := by rw [one_mul, mul_one]
  right_inv X := by
    have h1 := (chart_bruhat_factor_mul_inv hP A C).1
    unfold chartBruhatConj chartBruhatConjInv
    calc
      (1 + conePlus P A) * (1 - coneMinus P C) *
          ((1 + coneMinus P C) * (1 - conePlus P A) * X *
            (1 + conePlus P A) * (1 - coneMinus P C)) *
          (1 + coneMinus P C) * (1 - conePlus P A)
          = (((1 + conePlus P A) * (1 - coneMinus P C)) *
              ((1 + coneMinus P C) * (1 - conePlus P A))) * X *
            (((1 + conePlus P A) * (1 - coneMinus P C)) *
              ((1 + coneMinus P C) * (1 - conePlus P A))) := by
            simp only [mul_assoc]
      _ = 1 * X * 1 := by rw [h1]
      _ = X := by rw [one_mul, mul_one]
  map_mul' X Y := chartBruhatConj_mul hP A C X Y
  map_add' X Y := by unfold chartBruhatConj; noncomm_ring

/-- Under the Bruhat perspective automorphism `chartBruhatRingEquiv`, the cut `P`
transforms to a rotated idempotent `P_rot` whose pinched diagonal corners extract
`(P - Q₊) + Q₋`, while `genV P A C` and `1 - genV P A C` remain fixed. -/
theorem bruhatPerspective_rotatedCut_and_metric_invariance
    {P : B} (hP : P * P = P) (A C : B) :
    let e := chartBruhatRingEquiv hP A C
    let P_rot := e P
    P_rot * P_rot = P_rot ∧
    e (P + coneMinus P C) = P - conePlus P A ∧
    e.symm (P - conePlus P A) = P + coneMinus P C ∧
    e (genV P A C) = genV P A C ∧
    e (1 - genV P A C) = 1 - genV P A C ∧
    peirce11 P P_rot = P - qgtPlus P A C ∧
    peirce00 P P_rot = qgtMinus P A C ∧
    evenGrade P P_rot = (P - qgtPlus P A C) + qgtMinus P A C := by
  intro e P_rot
  have hRotIdem : P_rot * P_rot = P_rot := by
    calc
      P_rot * P_rot = e (P * P) := (e.map_mul P P).symm
      _ = e P := by rw [hP]
  have hTrans := chart_bruhat_conjugation_transition hP A C
  have hBlocks := chart_bruhat_conjugate_peirce_blocks hP A C
  have h11 : peirce11 P P_rot = P - qgtPlus P A C := by
    change P * chartBruhatConj P A C P * P = P - qgtPlus P A C
    exact hBlocks.1
  have h00 : peirce00 P P_rot = qgtMinus P A C := by
    change (1 - P) * chartBruhatConj P A C P * (1 - P) = qgtMinus P A C
    exact hBlocks.2.2.2
  have hEven : evenGrade P P_rot = (P - qgtPlus P A C) + qgtMinus P A C := by
    change peirce11 P P_rot + peirce00 P P_rot = _
    rw [h11, h00]
  exact ⟨hRotIdem, hTrans.1, hTrans.2, chartBruhatConj_genV hP A C,
    chartBruhatConj_one_sub_genV hP A C, h11, h00, hEven⟩

/-- In a noncommutative `[StarRing B]` with self-adjoint cut `star P = P`, pairing `A`
with `C := star A` makes `conePlus P A` and `coneMinus P (star A)` mutual adjoints,
makes `genPhi P A (star A)` self-adjoint, makes `genJ P A (star A)` skew-adjoint,
and realizes `(qgtPlus, qgtMinus, genV)` as star-Gram products. -/
theorem star_transcendent_adjoint_and_gram_factorization
    [StarRing B] {P : B} (hP : P * P = P) (hPs : star P = P) (A : B) :
    star (conePlus P A) = coneMinus P (star A) ∧
    star (coneMinus P (star A)) = conePlus P A ∧
    star (genPhi P A (star A)) = genPhi P A (star A) ∧
    star (genJ P A (star A)) = -genJ P A (star A) ∧
    qgtPlus P A (star A) = conePlus P A * star (conePlus P A) ∧
    qgtMinus P A (star A) = star (conePlus P A) * conePlus P A ∧
    genV P A (star A) = star (genPhi P A (star A)) * genPhi P A (star A) := by
  have h1mP : star (1 - P) = 1 - P := by
    simp only [star_sub, star_one, hPs]
  have hPlus : star (conePlus P A) = coneMinus P (star A) := by
    unfold conePlus coneMinus
    rw [star_mul, star_mul, h1mP, hPs, mul_assoc]
  have hMinus : star (coneMinus P (star A)) = conePlus P A := by
    rw [← hPlus, star_star]
  have hPhi : star (genPhi P A (star A)) = genPhi P A (star A) := by
    unfold genPhi
    rw [star_add, hPlus, hMinus, add_comm]
  have hJ : star (genJ P A (star A)) = -genJ P A (star A) := by
    unfold genJ
    rw [star_sub, hPlus, hMinus, neg_sub]
  have hQPlus : qgtPlus P A (star A) = conePlus P A * star (conePlus P A) := by
    rw [hPlus]
    rfl
  have hQMinus : qgtMinus P A (star A) = star (conePlus P A) * conePlus P A := by
    rw [hPlus]
    rfl
  have hV : genV P A (star A) = star (genPhi P A (star A)) * genPhi P A (star A) := by
    have hPhiSq := (archetype_A3_nilpotent_cones_and_tetraktys_table hP A (star A)).2.2.1
    rw [hPhi, hPhiSq]
  exact ⟨hPlus, hMinus, hPhi, hJ, hQPlus, hQMinus, hV⟩

end Stage3_TranscendentBruhat

/-! ## Section 5 (`S4_aporiaDefectTower`): Newton–Peirce Orbits & All-`k` `2^k`-Super-Convergence -/

section Stage4_AporiaDefectTower

/- The ring-level proofs live in the focused core owner. These aliases preserve
all public theorem names and their exact types for existing consumers. -/

alias newtonPeirceStep_mul_eq_zero :=
  InfoGeometry.Core.IdempotentGraphGrassmannian.newtonPeirceStep_mul_eq_zero

alias newtonPeirceStep_iterates_mul_eq_zero :=
  InfoGeometry.Core.IdempotentGraphGrassmannian.newtonPeirceStep_iterates_mul_eq_zero

alias newtonPeirceStep_iterates_add_of_orthogonal :=
  InfoGeometry.Core.IdempotentGraphGrassmannian.newtonPeirceStep_iterates_add_of_orthogonal

alias newtonPeirceStep_intertwines :=
  InfoGeometry.Core.IdempotentGraphGrassmannian.newtonPeirceStep_intertwines

alias newtonPeirceStep_iterates_intertwines :=
  InfoGeometry.Core.IdempotentGraphGrassmannian.newtonPeirceStep_iterates_intertwines

alias newtonPeirceStep_iterates_left_support :=
  InfoGeometry.Core.IdempotentGraphGrassmannian.newtonPeirceStep_iterates_left_support

alias newtonPeirceStep_iterates_right_support :=
  InfoGeometry.Core.IdempotentGraphGrassmannian.newtonPeirceStep_iterates_right_support

alias newtonPeirceStep_iterates_left_annihilated :=
  InfoGeometry.Core.IdempotentGraphGrassmannian.newtonPeirceStep_iterates_left_annihilated

alias newtonPeirceStep_iterates_right_annihilated :=
  InfoGeometry.Core.IdempotentGraphGrassmannian.newtonPeirceStep_iterates_right_annihilated

alias map_newtonPeirceStep :=
  InfoGeometry.Core.IdempotentGraphGrassmannian.map_newtonPeirceStep

alias map_newtonPeirceStep_iterates :=
  InfoGeometry.Core.IdempotentGraphGrassmannian.map_newtonPeirceStep_iterates

alias idempotencyDefect_newtonPeirceStep_iterate_factor :=
  InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect_newtonPeirceStep_iterate_factor

alias newtonPeirceStep_iterate_idempotent_of_defect_pow_two_pow_zero :=
  InfoGeometry.Core.IdempotentGraphGrassmannian.newtonPeirceStep_iterate_idempotent_of_defect_pow_two_pow_zero

end Stage4_AporiaDefectTower

/-! ## Section 6 (`S5_covariantMetaTower`): Bruhat Pinching, Covariant Constancy & Meta-Towers -/

section Stage5_CovariantMetaTower

variable {B : Type*} [Ring B]

/-- **Pinched Bruhat-Perspective Aporia**: Pinching the rotated cut
`P_rot = chartBruhatRingEquiv hP A C P` along `P` produces upper/lower diagonal corners
whose idempotency defects agree identically with those of the orthogonal cycles `Q₊`, `Q₋`,
so the pinched even cut has defect equal to `idempotencyDefect (genV P A C)`. -/
theorem pinched_bruhatPerspective_defect_eq_genV_defect
    {P : B} (hP : P * P = P) (A C : B) :
    let P_rot := chartBruhatRingEquiv hP A C P
    idempotencyDefect (peirce11 P P_rot) = idempotencyDefect (qgtPlus P A C) ∧
    idempotencyDefect (peirce00 P P_rot) = idempotencyDefect (qgtMinus P A C) ∧
    idempotencyDefect (evenGrade P P_rot) = idempotencyDefect (genV P A C) := by
  intro P_rot
  have hBlocks := bruhatPerspective_rotatedCut_and_metric_invariance hP A C
  have h11 : peirce11 P P_rot = P - qgtPlus P A C := hBlocks.2.2.2.2.2.1
  have h00 : peirce00 P P_rot = qgtMinus P A C := hBlocks.2.2.2.2.2.2.1
  have hQPL : P * qgtPlus P A C = qgtPlus P A C := by
    simpa only [Function.iterate_zero_apply] using qgtPlus_defect_iterates_left hP A C 0
  have hQPR : qgtPlus P A C * P = qgtPlus P A C := by
    simpa only [Function.iterate_zero_apply] using qgtPlus_defect_iterates_right hP A C 0
  have hDef11 : idempotencyDefect (peirce11 P P_rot) = idempotencyDefect (qgtPlus P A C) := by
    rw [h11]
    unfold idempotencyDefect
    calc
      (P - qgtPlus P A C) * (P - qgtPlus P A C) - (P - qgtPlus P A C)
          = P * P - P * qgtPlus P A C - qgtPlus P A C * P +
              qgtPlus P A C * qgtPlus P A C - P + qgtPlus P A C := by noncomm_ring
      _ = P - qgtPlus P A C - qgtPlus P A C +
              qgtPlus P A C * qgtPlus P A C - P + qgtPlus P A C := by
            rw [hP, hQPL, hQPR]
      _ = qgtPlus P A C * qgtPlus P A C - qgtPlus P A C := by abel
  have hDef00 : idempotencyDefect (peirce00 P P_rot) = idempotencyDefect (qgtMinus P A C) := by
    rw [h00]
  have hOrtho10 : peirce11 P P_rot * peirce00 P P_rot = 0 := by
    simp only [peirce11, peirce00]; peirce_nf hP
  have hOrtho01 : peirce00 P P_rot * peirce11 P P_rot = 0 := by
    simp only [peirce11, peirce00]; peirce_nf hP
  have hDefEven : idempotencyDefect (evenGrade P P_rot) = idempotencyDefect (genV P A C) := by
    change idempotencyDefect (peirce11 P P_rot + peirce00 P P_rot) = _
    rw [idempotencyDefect_add_of_orthogonal hOrtho10 hOrtho01, hDef11, hDef00,
      ← genV_defect_cycle_split hP A C]
  exact ⟨hDef11, hDef00, hDefEven⟩

/-- All Newton–Peirce iterates of `genV P A C` split orthogonally across `qgtPlus` and
`qgtMinus`, intertwine both Peirce cones, and commute with `genPhi` and `genJ`. -/
theorem qgt_newtonPeirce_iterates_cone_relations_and_split
    {P : B} (hP : P * P = P) (A C : B) (k : ℕ) :
    newtonPeirceStep^[k] (genV P A C) =
      newtonPeirceStep^[k] (qgtPlus P A C) + newtonPeirceStep^[k] (qgtMinus P A C) ∧
    conePlus P A * newtonPeirceStep^[k] (qgtMinus P A C) =
      newtonPeirceStep^[k] (qgtPlus P A C) * conePlus P A ∧
    coneMinus P C * newtonPeirceStep^[k] (qgtPlus P A C) =
      newtonPeirceStep^[k] (qgtMinus P A C) * coneMinus P C ∧
    PeirceSpine.comm (genPhi P A C) (newtonPeirceStep^[k] (genV P A C)) = 0 ∧
    PeirceSpine.comm (genJ P A C) (newtonPeirceStep^[k] (genV P A C)) = 0 := by
  have hOrtho := qgt_cycles_orthogonal hP A C
  have hCone := qgt_cycles_cone_relations hP A C
  have hSplit :
      newtonPeirceStep^[k] (genV P A C) =
        newtonPeirceStep^[k] (qgtPlus P A C) + newtonPeirceStep^[k] (qgtMinus P A C) := by
    change newtonPeirceStep^[k] (qgtPlus P A C + qgtMinus P A C) = _
    exact newtonPeirceStep_iterates_add_of_orthogonal hOrtho.1 hOrtho.2 k
  have hInterPlus :
      conePlus P A * newtonPeirceStep^[k] (qgtMinus P A C) =
        newtonPeirceStep^[k] (qgtPlus P A C) * conePlus P A :=
    (newtonPeirceStep_iterates_intertwines hCone.2.2.1.symm k).symm
  have hInterMinus :
      coneMinus P C * newtonPeirceStep^[k] (qgtPlus P A C) =
        newtonPeirceStep^[k] (qgtMinus P A C) * coneMinus P C :=
    (newtonPeirceStep_iterates_intertwines hCone.2.2.2.2.2.symm k).symm
  have hZero1 := newtonPeirceStep_iterates_left_annihilated hCone.1 k
  have hZero2 := newtonPeirceStep_iterates_right_annihilated hCone.2.1 k
  have hZero3 := newtonPeirceStep_iterates_left_annihilated hCone.2.2.2.1 k
  have hZero4 := newtonPeirceStep_iterates_right_annihilated hCone.2.2.2.2.1 k
  have hCommPlus :
      conePlus P A * newtonPeirceStep^[k] (genV P A C) =
        newtonPeirceStep^[k] (genV P A C) * conePlus P A := by
    rw [hSplit, mul_add, add_mul, hZero1, hInterPlus, hZero2, zero_add, add_zero]
  have hCommMinus :
      coneMinus P C * newtonPeirceStep^[k] (genV P A C) =
        newtonPeirceStep^[k] (genV P A C) * coneMinus P C := by
    rw [hSplit, mul_add, add_mul, hInterMinus, hZero3, hZero4, add_zero, zero_add]
  have hCommPhi : PeirceSpine.comm (genPhi P A C) (newtonPeirceStep^[k] (genV P A C)) = 0 := by
    unfold PeirceSpine.comm genPhi
    rw [add_mul, mul_add, hCommPlus, hCommMinus, sub_self]
  have hCommJ : PeirceSpine.comm (genJ P A C) (newtonPeirceStep^[k] (genV P A C)) = 0 := by
    unfold PeirceSpine.comm genJ
    rw [sub_mul, mul_sub, hCommPlus, hCommMinus, sub_self]
  exact ⟨hSplit, hInterPlus, hInterMinus, hCommPhi, hCommJ⟩

/-- **Coagulated Covariant Constancy & Bruhat Invariance Across Both Meta-Towers**:
At every defect-tower depth `n` and every Newton–Peirce depth `k`, both
`idempotencyDefect^[n] (genV P A C)` and `newtonPeirceStep^[k] (genV P A C)` are
simultaneously:
1. covariantly constant under `peirceCovariantDeriv P A C`,
2. parity-even (`parityConj P · = ·`), and
3. invariant under the full Bruhat perspective automorphism `chartBruhatRingEquiv hP A C`. -/
theorem all_depth_meta_tower_covariant_constancy_and_bruhat_invariance
    {P : B} (hP : P * P = P) (A C : B) (n k : ℕ) :
    peirceCovariantDeriv P A C (idempotencyDefect^[n] (genV P A C)) = 0 ∧
    parityConj P (idempotencyDefect^[n] (genV P A C)) = idempotencyDefect^[n] (genV P A C) ∧
    chartBruhatRingEquiv hP A C (idempotencyDefect^[n] (genV P A C)) =
      idempotencyDefect^[n] (genV P A C) ∧
    peirceCovariantDeriv P A C (newtonPeirceStep^[k] (genV P A C)) = 0 ∧
    parityConj P (newtonPeirceStep^[k] (genV P A C)) = newtonPeirceStep^[k] (genV P A C) ∧
    chartBruhatRingEquiv hP A C (newtonPeirceStep^[k] (genV P A C)) =
      newtonPeirceStep^[k] (genV P A C) := by
  have hPDef : P * idempotencyDefect^[n] (genV P A C) =
      idempotencyDefect^[n] (genV P A C) * P := by
    rw [genV_defect_iterates_left_projection hP A C n,
      genV_defect_iterates_right_projection hP A C n]
  have hDefChar := binaryCut_commutant_characterization hP (idempotencyDefect^[n] (genV P A C))
  have hDefDeriv : peirceGradingDeriv P (idempotencyDefect^[n] (genV P A C)) = 0 :=
    hDefChar.1.mp hPDef
  have hDefParity :
      parityConj P (idempotencyDefect^[n] (genV P A C)) =
        idempotencyDefect^[n] (genV P A C) :=
    hDefChar.2.2.2 hPDef
  have hPhiDef :
      PeirceSpine.comm (genPhi P A C) (idempotencyDefect^[n] (genV P A C)) = 0 := by
    rw [genV_defect_iterates_cycle_split hP A C n]
    exact (qgt_defect_iterate_sum_commutes_with_generators hP A C n).1
  have hDefCov :
      peirceCovariantDeriv P A C (idempotencyDefect^[n] (genV P A C)) = 0 := by
    unfold peirceCovariantDeriv
    rw [hDefDeriv, hPhiDef, add_zero]
  have hVFix : (chartBruhatRingEquiv hP A C).toRingHom (genV P A C) = genV P A C :=
    chartBruhatConj_genV hP A C
  have hDefBruhat :
      chartBruhatRingEquiv hP A C (idempotencyDefect^[n] (genV P A C)) =
        idempotencyDefect^[n] (genV P A C) := by
    change (chartBruhatRingEquiv hP A C).toRingHom (idempotencyDefect^[n] (genV P A C)) = _
    rw [map_idempotencyDefect_iterates (chartBruhatRingEquiv hP A C).toRingHom, hVFix]
  have hNewtRel := qgt_newtonPeirce_iterates_cone_relations_and_split hP A C k
  have hNP_left :
      P * newtonPeirceStep^[k] (qgtPlus P A C) = newtonPeirceStep^[k] (qgtPlus P A C) :=
    newtonPeirceStep_iterates_left_support
      (by simpa only [Function.iterate_zero_apply] using qgtPlus_defect_iterates_left hP A C 0) k
  have hNP_right :
      newtonPeirceStep^[k] (qgtPlus P A C) * P = newtonPeirceStep^[k] (qgtPlus P A C) :=
    newtonPeirceStep_iterates_right_support
      (by simpa only [Function.iterate_zero_apply] using qgtPlus_defect_iterates_right hP A C 0) k
  have hNM_left : P * newtonPeirceStep^[k] (qgtMinus P A C) = 0 :=
    newtonPeirceStep_iterates_left_annihilated
      (by simp only [qgtMinus]; peirce_nf hP) k
  have hNM_right : newtonPeirceStep^[k] (qgtMinus P A C) * P = 0 :=
    newtonPeirceStep_iterates_right_annihilated
      (by simp only [qgtMinus]; peirce_nf hP) k
  have hPNewt : P * newtonPeirceStep^[k] (genV P A C) =
      newtonPeirceStep^[k] (genV P A C) * P := by
    rw [hNewtRel.1, mul_add, add_mul, hNP_left, hNP_right, hNM_left, hNM_right]
  have hNewtChar := binaryCut_commutant_characterization hP (newtonPeirceStep^[k] (genV P A C))
  have hNewtDeriv : peirceGradingDeriv P (newtonPeirceStep^[k] (genV P A C)) = 0 :=
    hNewtChar.1.mp hPNewt
  have hNewtParity :
      parityConj P (newtonPeirceStep^[k] (genV P A C)) = newtonPeirceStep^[k] (genV P A C) :=
    hNewtChar.2.2.2 hPNewt
  have hNewtCov :
      peirceCovariantDeriv P A C (newtonPeirceStep^[k] (genV P A C)) = 0 := by
    unfold peirceCovariantDeriv
    rw [hNewtDeriv, hNewtRel.2.2.2.1, add_zero]
  have hNewtBruhat :
      chartBruhatRingEquiv hP A C (newtonPeirceStep^[k] (genV P A C)) =
        newtonPeirceStep^[k] (genV P A C) := by
    change (chartBruhatRingEquiv hP A C).toRingHom (newtonPeirceStep^[k] (genV P A C)) = _
    rw [map_newtonPeirceStep_iterates (chartBruhatRingEquiv hP A C).toRingHom, hVFix]
  exact ⟨hDefCov, hDefParity, hDefBruhat, hNewtCov, hNewtParity, hNewtBruhat⟩

end Stage5_CovariantMetaTower

/-! ## Section 7 (`S6_noncommMatrixCoagulation`): Block-Matrix Geometry, Witnesses & Master Synthesis -/

section Stage6_NoncommMatrixCoagulation

/-- Canonical block-matrix idempotent cut `diag(1, 0)` inside `M₂(B)` for an arbitrary
noncommutative ring `B`. -/
def peirceCut2 {B : Type*} [Ring B] : Matrix (Fin 2) (Fin 2) B :=
  Matrix.of ![![1, 0], ![0, 0]]

/-- Block-diagonal embedding `B × B →+* M₂(B)` over an arbitrary noncommutative ring `B`. -/
def diag2RingHom (B : Type*) [Ring B] : B × B →+* Matrix (Fin 2) (Fin 2) B where
  toFun uv := Matrix.of ![![uv.1, 0], ![0, uv.2]]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' uv₁ uv₂ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' uv₁ uv₂ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- `peirceCut2` is idempotent over every associative ring `B`. -/
theorem peirceCut2_idempotent {B : Type*} [Ring B] :
    (peirceCut2 : Matrix (Fin 2) (Fin 2) B) * peirceCut2 = peirceCut2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [peirceCut2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Over an arbitrary noncommutative fiber ring `B`, `qgtPlus`, `qgtMinus`, and `genV` of
two `2 × 2` block matrices `(A, C)` under `peirceCut2` compute the ordered noncommutative
round-trip fiber products `(A 0 1 * C 1 0)` and `(C 1 0 * A 0 1)`. -/
theorem peirceCut2_tetraktys_fiber_products {B : Type*} [Ring B]
    (A C : Matrix (Fin 2) (Fin 2) B) :
    qgtPlus peirceCut2 A C = diag2RingHom B (A 0 1 * C 1 0, 0) ∧
    qgtMinus peirceCut2 A C = diag2RingHom B (0, C 1 0 * A 0 1) ∧
    genV peirceCut2 A C = diag2RingHom B (A 0 1 * C 1 0, C 1 0 * A 0 1) := by
  have hCut : ∀ i j : Fin 2,
      (peirceCut2 : Matrix (Fin 2) (Fin 2) B) i j = if i = 0 ∧ j = 0 then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [peirceCut2]
  have hPlus : conePlus peirceCut2 A = Matrix.of ![![0, A 0 1], ![0, 0]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conePlus, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, hCut]
  have hMinus : coneMinus peirceCut2 C = Matrix.of ![![0, 0], ![C 1 0, 0]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coneMinus, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, hCut, Fin.sum_univ_two]
  have hQP : qgtPlus peirceCut2 A C = diag2RingHom B (A 0 1 * C 1 0, 0) := by
    unfold qgtPlus
    rw [hPlus, hMinus]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diag2RingHom, Matrix.mul_apply, Fin.sum_univ_two]
  have hQM : qgtMinus peirceCut2 A C = diag2RingHom B (0, C 1 0 * A 0 1) := by
    unfold qgtMinus
    rw [hPlus, hMinus]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diag2RingHom, Matrix.mul_apply, Fin.sum_univ_two]
  have hV : genV peirceCut2 A C = diag2RingHom B (A 0 1 * C 1 0, C 1 0 * A 0 1) := by
    change qgtPlus peirceCut2 A C + qgtMinus peirceCut2 A C = _
    rw [hQP, hQM, ← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  exact ⟨hQP, hQM, hV⟩

/-- Both the defect tower and the Newton–Peirce tower of `genV peirceCut2 A C` transport
exact-fiberwise through `diag2RingHom B`, preserving the noncommutative order between
`A 0 1 * C 1 0` and `C 1 0 * A 0 1`. -/
theorem peirceCut2_fiber_tower_transport {B : Type*} [Ring B]
    (A C : Matrix (Fin 2) (Fin 2) B) (n k : ℕ) :
    idempotencyDefect^[n] (genV peirceCut2 A C) =
      diag2RingHom B
        (idempotencyDefect^[n] (A 0 1 * C 1 0),
          idempotencyDefect^[n] (C 1 0 * A 0 1)) ∧
    newtonPeirceStep^[k] (genV peirceCut2 A C) =
      diag2RingHom B
        (newtonPeirceStep^[k] (A 0 1 * C 1 0),
          newtonPeirceStep^[k] (C 1 0 * A 0 1)) := by
  have hV := (peirceCut2_tetraktys_fiber_products A C).2.2
  have hDefProd : ∀ u v : B,
      idempotencyDefect^[n] (u, v) =
        (idempotencyDefect^[n] u, idempotencyDefect^[n] v) := by
    intro u v
    ext <;>
      [exact map_idempotencyDefect_iterates (RingHom.fst B B) (u, v) n;
       exact map_idempotencyDefect_iterates (RingHom.snd B B) (u, v) n]
  have hNewtProd : ∀ u v : B,
      newtonPeirceStep^[k] (u, v) =
        (newtonPeirceStep^[k] u, newtonPeirceStep^[k] v) := by
    intro u v
    ext <;>
      [exact map_newtonPeirceStep_iterates (RingHom.fst B B) (u, v) k;
       exact map_newtonPeirceStep_iterates (RingHom.snd B B) (u, v) k]
  constructor
  · rw [hV, ← map_idempotencyDefect_iterates (diag2RingHom B), hDefProd]
  · rw [hV, ← map_newtonPeirceStep_iterates (diag2RingHom B), hNewtProd]

/-! ### Explicit Noncommutative Matrix Operator Witnesses & Anti-Toy Counterexamples -/

/-- **Witness 1 (One-Sided Fiber Annihilation Impossible in Commutative Domains)**:
In `M₂(Mat2Z)` with `A 0 1 = e₁₁` and `C 1 0 = e₁₂`, the upper round-trip `qgtPlus` is
nonzero with nonzero defect, whereas the reverse-order round-trip `qgtMinus` and its defect
collapse identically to `0`. -/
theorem noncomm_fiber_one_sided_cycle_annihilation_witness :
    let b : InfoGeometry.Algebra.FiniteSpin.Mat2Z := !![1, 0; 0, 0]
    let c : InfoGeometry.Algebra.FiniteSpin.Mat2Z := !![0, 1; 0, 0]
    let blockA : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z :=
      Matrix.of ![![0, b], ![0, 0]]
    let blockC : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z :=
      Matrix.of ![![0, 0], ![c, 0]]
    qgtPlus peirceCut2 blockA blockC ≠ 0 ∧
    idempotencyDefect (qgtPlus peirceCut2 blockA blockC) ≠ 0 ∧
    qgtMinus peirceCut2 blockA blockC = 0 ∧
    idempotencyDefect (qgtMinus peirceCut2 blockA blockC) = 0 := by
  intro b c blockA blockC
  have hFib := peirceCut2_tetraktys_fiber_products blockA blockC
  have hbc : b * c = !![0, 1; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [b, c, Matrix.mul_apply, Fin.sum_univ_two]
  have hcb : c * b = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [b, c, Matrix.mul_apply, Fin.sum_univ_two]
  have hQP_ne : qgtPlus peirceCut2 blockA blockC ≠ 0 := by
    intro h0
    have h00 := congrArg (fun M => M 0 0 0 1) h0
    rw [hFib.1] at h00
    simp [diag2RingHom, blockA, blockC, hbc] at h00
  have hQM_eq : qgtMinus peirceCut2 blockA blockC = 0 := by
    rw [hFib.2.1]
    simp only [blockC, blockA, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hcb]
    exact (diag2RingHom InfoGeometry.Algebra.FiniteSpin.Mat2Z).map_zero
  have hDefPlus_ne : idempotencyDefect (qgtPlus peirceCut2 blockA blockC) ≠ 0 := by
    intro h0
    have h00 := congrArg (fun M => M 0 0 0 1) h0
    rw [idempotencyDefect, hFib.1, ← map_mul, ← map_sub] at h00
    simp only [blockA, blockC, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h00
    rw [hbc] at h00
    have hSq : (!![0, (1 : ℤ); 0, 0] : InfoGeometry.Algebra.FiniteSpin.Mat2Z) * !![0, 1; 0, 0] = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hProd : ((!![0, (1 : ℤ); 0, 0] : InfoGeometry.Algebra.FiniteSpin.Mat2Z),
          (0 : InfoGeometry.Algebra.FiniteSpin.Mat2Z)) *
        (!![0, 1; 0, 0], 0) - (!![0, 1; 0, 0], 0) = (-!![0, 1; 0, 0], 0) := by
      ext i j <;> fin_cases i <;> fin_cases j <;> simp [hSq]
    rw [hProd] at h00
    simp [diag2RingHom] at h00
  have hDefMinus_eq : idempotencyDefect (qgtMinus peirceCut2 blockA blockC) = 0 := by
    rw [hQM_eq]
    simp [idempotencyDefect]
  exact ⟨hQP_ne, hDefPlus_ne, hQM_eq, hDefMinus_eq⟩

/-- **Witness 2 (Noncommutative Shear Round-Trip Defect Asymmetry & All-Depth Intertwining)**:
For the noncommuting `SL(2, ℤ)` shears `U = !![1, 1; 0, 1]` and `L = !![1, 0; 1, 1]` in
`M₂(M₂(ℤ))`, upper and lower Peirce cycles have strictly distinct defects while their
entire recursive defect and Newton–Peirce towers intertwine across every depth `n, k : ℕ`. -/
theorem noncomm_shear_roundtrip_defect_asymmetry_witness (n k : ℕ) :
    let shearU : InfoGeometry.Algebra.FiniteSpin.Mat2Z := !![1, 1; 0, 1]
    let shearL : InfoGeometry.Algebra.FiniteSpin.Mat2Z := !![1, 0; 1, 1]
    let blockU : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z :=
      Matrix.of ![![0, shearU], ![0, 0]]
    let blockL : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z :=
      Matrix.of ![![0, 0], ![shearL, 0]]
    shearU * shearL ≠ shearL * shearU ∧
    idempotencyDefect (shearU * shearL) ≠ idempotencyDefect (shearL * shearU) ∧
    idempotencyDefect^[n] (qgtPlus peirceCut2 blockU blockL) * conePlus peirceCut2 blockU =
      conePlus peirceCut2 blockU * idempotencyDefect^[n] (qgtMinus peirceCut2 blockU blockL) ∧
    newtonPeirceStep^[k] (qgtPlus peirceCut2 blockU blockL) * conePlus peirceCut2 blockU =
      conePlus peirceCut2 blockU * newtonPeirceStep^[k] (qgtMinus peirceCut2 blockU blockL) := by
  intro shearU shearL blockU blockL
  have hUL : shearU * shearL = !![2, 1; 1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [shearU, shearL, Matrix.mul_apply, Fin.sum_univ_two]
  have hLU : shearL * shearU = !![1, 1; 1, 2] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [shearU, shearL, Matrix.mul_apply, Fin.sum_univ_two]
  have hNe : shearU * shearL ≠ shearL * shearU := by
    intro hEq
    have h00 := congrArg (fun M => M 0 0) hEq
    rw [hUL, hLU] at h00
    simp at h00
  have hDefNe : idempotencyDefect (shearU * shearL) ≠ idempotencyDefect (shearL * shearU) := by
    intro hEq
    have h00 := congrArg (fun M => M 0 0) hEq
    unfold idempotencyDefect at h00
    rw [hUL, hLU] at h00
    have hULsq : (!![2, (1 : ℤ); 1, 1]) * !![2, 1; 1, 1] = !![5, 3; 3, 2] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hLUsq : (!![1, (1 : ℤ); 1, 2]) * !![1, 1; 1, 2] = !![2, 3; 3, 5] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hULsq, hLUsq] at h00
    simp at h00
  have hConeDef :=
    (qgt_defect_iterates_cone_relations peirceCut2_idempotent blockU blockL n).2.2.1.symm
  have hConeNewt :=
    (qgt_newtonPeirce_iterates_cone_relations_and_split peirceCut2_idempotent blockU blockL k).2.1.symm
  exact ⟨hNe, hDefNe, hConeDef, hConeNewt⟩

/-- **Witness 3 (Strict 2-Step Non-Diagonal Nilpotent Defect & `2^2`-Power Stabilization)**:
Over `M₂(M₂(ℤ))`, `aporiaSeedX2 = limitIdemE + nilpPerturbN` fails to commute with
`peirceCut2`, has nonzero defect at step `0` and strictly nonzero defect after `1`
Newton–Peirce step, achieves `(idempotencyDefect aporiaSeedX2) ^ (2 ^ 2) = 0`, and
converges identically at step `k = 2` to the non-diagonal idempotent `limitIdemE`. -/
theorem strict_two_step_nondiag_newtonPeirce_matrix_witness :
    let limitIdemE : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z :=
      Matrix.of ![![!![1, 0; 0, 0], !![0, -1; 0, 0]], ![0, 0]]
    let nilpPerturbN : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z :=
      Matrix.of ![![0, !![0, 0; 1, 0]], ![0, !![0, 1; 0, 0]]]
    let aporiaSeedX2 := limitIdemE + nilpPerturbN
    peirceCut2 * aporiaSeedX2 ≠ aporiaSeedX2 * peirceCut2 ∧
    idempotencyDefect aporiaSeedX2 ≠ 0 ∧
    idempotencyDefect (newtonPeirceStep aporiaSeedX2) ≠ 0 ∧
    (idempotencyDefect aporiaSeedX2) ^ (2 ^ 2) = 0 ∧
    newtonPeirceStep^[2] aporiaSeedX2 = limitIdemE ∧
    limitIdemE * limitIdemE = limitIdemE ∧
    peirceCut2 * limitIdemE ≠ limitIdemE * peirceCut2 := by
  intro limitIdemE nilpPerturbN aporiaSeedX2
  have hE_idem : limitIdemE * limitIdemE = limitIdemE := by
    ext i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [limitIdemE, Matrix.mul_apply, Fin.sum_univ_two]
  have hEN : limitIdemE * nilpPerturbN = 0 := by
    ext i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [limitIdemE, nilpPerturbN, Matrix.mul_apply, Fin.sum_univ_two]
  have hNE : nilpPerturbN * limitIdemE = 0 := by
    ext i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [limitIdemE, nilpPerturbN, Matrix.mul_apply, Fin.sum_univ_two]
  have hN2_eq : nilpPerturbN * nilpPerturbN =
      Matrix.of ![![(0 : InfoGeometry.Algebra.FiniteSpin.Mat2Z), !![0, 0; 0, 1]],
                  ![0, 0]] := by
    ext i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [nilpPerturbN, Matrix.mul_apply, Fin.sum_univ_two]
  have hN3 : nilpPerturbN * nilpPerturbN * nilpPerturbN = 0 := by
    rw [hN2_eq]
    ext i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [nilpPerturbN, Matrix.mul_apply, Fin.sum_univ_two]
  have hN4 : (nilpPerturbN * nilpPerturbN) * (nilpPerturbN * nilpPerturbN) = 0 := by
    rw [hN2_eq]
    ext i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hN2_ne : nilpPerturbN * nilpPerturbN ≠ 0 := by
    intro h0
    have h0111 := congrArg (fun M => M 0 1 1 1) h0
    rw [hN2_eq] at h0111
    simp at h0111
  have hCutX : peirceCut2 * aporiaSeedX2 ≠ aporiaSeedX2 * peirceCut2 := by
    intro hEq
    have h0101 := congrArg (fun M => M 0 1 0 1) hEq
    simp [Matrix.mul_apply, Fin.sum_univ_two, peirceCut2, aporiaSeedX2,
      limitIdemE, nilpPerturbN] at h0101
  have hCutE : peirceCut2 * limitIdemE ≠ limitIdemE * peirceCut2 := by
    intro hEq
    have h0101 := congrArg (fun M => M 0 1 0 1) hEq
    simp [Matrix.mul_apply, Fin.sum_univ_two, peirceCut2, limitIdemE] at h0101
  have hDefE : idempotencyDefect limitIdemE = 0 :=
    idempotencyDefect_eq_zero_iff.mpr hE_idem
  have hDefX : idempotencyDefect aporiaSeedX2 = nilpPerturbN * nilpPerturbN - nilpPerturbN := by
    change idempotencyDefect (limitIdemE + nilpPerturbN) = _
    rw [idempotencyDefect_add_of_orthogonal hEN hNE, hDefE, zero_add]
    rfl
  have hDefX_ne : idempotencyDefect aporiaSeedX2 ≠ 0 := by
    intro h0
    rw [hDefX] at h0
    have h0110 := congrArg (fun M => M 0 1 1 0) h0
    rw [hN2_eq] at h0110
    simp [nilpPerturbN] at h0110
  have hStepE : newtonPeirceStep limitIdemE = limitIdemE :=
    newtonPeirceStep_eq_self_of_idempotent hE_idem
  have hStepN :
      newtonPeirceStep nilpPerturbN =
        (3 : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z) *
          (nilpPerturbN * nilpPerturbN) := by
    unfold newtonPeirceStep
    calc
      3 * nilpPerturbN * nilpPerturbN - 2 * nilpPerturbN * nilpPerturbN * nilpPerturbN
          = 3 * (nilpPerturbN * nilpPerturbN) -
              2 * (nilpPerturbN * nilpPerturbN * nilpPerturbN) := by
            noncomm_ring
      _ = 3 * (nilpPerturbN * nilpPerturbN) := by rw [hN3, mul_zero, sub_zero]
  have hStep1X :
      newtonPeirceStep aporiaSeedX2 =
        limitIdemE +
          (3 : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z) *
            (nilpPerturbN * nilpPerturbN) := by
    change newtonPeirceStep (limitIdemE + nilpPerturbN) = _
    rw [newtonPeirceStep_add_of_orthogonal hEN hNE, hStepE, hStepN]
  have hE_N2 :
      limitIdemE *
          ((3 : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z) *
            (nilpPerturbN * nilpPerturbN)) = 0 := by
    calc
      limitIdemE * (3 * (nilpPerturbN * nilpPerturbN))
          = 3 * ((limitIdemE * nilpPerturbN) * nilpPerturbN) := by noncomm_ring
      _ = 0 := by rw [hEN, zero_mul, mul_zero]
  have hN2_E :
      ((3 : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z) *
            (nilpPerturbN * nilpPerturbN)) * limitIdemE = 0 := by
    calc
      3 * (nilpPerturbN * nilpPerturbN) * limitIdemE
          = 3 * (nilpPerturbN * (nilpPerturbN * limitIdemE)) := by noncomm_ring
      _ = 0 := by rw [hNE, mul_zero, mul_zero]
  have hN2_sq3 :
      ((3 : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z) *
            (nilpPerturbN * nilpPerturbN)) *
        ((3 : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z) *
            (nilpPerturbN * nilpPerturbN)) = 0 := by
    calc
      (3 * (nilpPerturbN * nilpPerturbN)) * (3 * (nilpPerturbN * nilpPerturbN))
          = 9 * ((nilpPerturbN * nilpPerturbN) * (nilpPerturbN * nilpPerturbN)) := by
            noncomm_ring
      _ = 0 := by rw [hN4, mul_zero]
  have hDef1X_eq :
      idempotencyDefect (newtonPeirceStep aporiaSeedX2) =
        -((3 : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z) *
            (nilpPerturbN * nilpPerturbN)) := by
    rw [hStep1X, idempotencyDefect_add_of_orthogonal hE_N2 hN2_E, hDefE, zero_add]
    unfold idempotencyDefect
    rw [hN2_sq3, zero_sub]
  have hDef1X_ne : idempotencyDefect (newtonPeirceStep aporiaSeedX2) ≠ 0 := by
    intro h0
    rw [hDef1X_eq] at h0
    have h0111 := congrArg (fun M => M 0 1 1 1) h0
    rw [hN2_eq] at h0111
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h0111
    exact (by decide : (3 : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z) 0 0 1 1 ≠ 0) h0111
  have hDefX_sq :
      idempotencyDefect aporiaSeedX2 * idempotencyDefect aporiaSeedX2 =
        nilpPerturbN * nilpPerturbN := by
    rw [hDefX]
    calc
      (nilpPerturbN * nilpPerturbN - nilpPerturbN) *
          (nilpPerturbN * nilpPerturbN - nilpPerturbN)
          = (nilpPerturbN * nilpPerturbN) * (nilpPerturbN * nilpPerturbN) -
              (nilpPerturbN * nilpPerturbN * nilpPerturbN) -
              nilpPerturbN * (nilpPerturbN * nilpPerturbN) +
              nilpPerturbN * nilpPerturbN := by noncomm_ring
      _ = 0 - 0 - 0 + nilpPerturbN * nilpPerturbN := by
            rw [hN4, hN3, ← mul_assoc, hN3]
      _ = nilpPerturbN * nilpPerturbN := by abel
  have hDefX_pow4 : (idempotencyDefect aporiaSeedX2) ^ (2 ^ 2) = 0 := by
    have h4 : (2 ^ 2 : ℕ) = 4 := by norm_num
    rw [h4]
    calc
      (idempotencyDefect aporiaSeedX2) ^ 4
          = (idempotencyDefect aporiaSeedX2 * idempotencyDefect aporiaSeedX2) *
              (idempotencyDefect aporiaSeedX2 * idempotencyDefect aporiaSeedX2) := by
            noncomm_ring
      _ = (nilpPerturbN * nilpPerturbN) * (nilpPerturbN * nilpPerturbN) := by
            rw [hDefX_sq]
      _ = 0 := hN4
  have hStep2X : newtonPeirceStep^[2] aporiaSeedX2 = limitIdemE := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [hStep1X, newtonPeirceStep_add_of_orthogonal hE_N2 hN2_E, hStepE]
    have hStep3N2 :
        newtonPeirceStep
          ((3 : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z) *
            (nilpPerturbN * nilpPerturbN)) = 0 := by
      unfold newtonPeirceStep
      let M := (3 : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z) *
        (nilpPerturbN * nilpPerturbN)
      change 3 * M * M - 2 * M * M * M = 0
      calc
        3 * M * M - 2 * M * M * M = 3 * (M * M) - 2 * (M * M) * M := by noncomm_ring
        _ = 0 := by rw [hN2_sq3]; noncomm_ring
    rw [hStep3N2, add_zero]
  exact ⟨hCutX, hDefX_ne, hDef1X_ne, hDefX_pow4, hStep2X, hE_idem, hCutE⟩

/-- Noncommutativity witness for the `2 × 2` Peirce matrix carrier `Matrix (Fin 2) (Fin 2) B`
over any nontrivial ring `B`: `peirceCut2` and the upper-triangular unit shear fail to commute. -/
theorem matrix_fin2_peirce_noncomm_witness {B : Type*} [Ring B] [Nontrivial B] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) B, X * Y ≠ Y * X := by
  let shear01 : Matrix (Fin 2) (Fin 2) B := Matrix.of ![![0, (1 : B)], ![0, 0]]
  refine ⟨peirceCut2, shear01, ?_⟩
  intro hEq
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 0 1) hEq
  have hCut : ∀ i j : Fin 2,
      (peirceCut2 : Matrix (Fin 2) (Fin 2) B) i j = if i = 0 ∧ j = 0 then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [peirceCut2]
  simp [Matrix.mul_apply, hCut, shear01] at h01

/-- Concrete noncommutativity witness for the `M₂(Mat2Z)` block-matrix carrier
`Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z`. -/
theorem matrix_mat2z_peirce_noncomm_witness :
    ∃ X Y : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z, X * Y ≠ Y * X := by
  let limitIdemE : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z :=
    Matrix.of ![![!![1, 0; 0, 0], !![0, -1; 0, 0]], ![0, 0]]
  refine ⟨peirceCut2, limitIdemE, ?_⟩
  intro hEq
  have h0101 := congrArg (fun M => M 0 1 0 1) hEq
  simp [Matrix.mul_apply, Fin.sum_univ_two, peirceCut2, limitIdemE] at h0101

/-- **Master Noncommutative Epistemic Synthesis Theorem (`S1`–`S6`)**:
Over any associative ring `B` with idempotent cut `P * P = P` and operators `A, C, X, Y : B`,
unites the commutant equivalence, fourfold quiver product laws, Bruhat perspective ring
automorphism, all-`k` `2^k`-power Newton–Peirce factorization, pinched Bruhat-cut defect law,
and all-depth covariant constancy across both meta-towers. -/
theorem epistemic_peirce_bruhat_aporia_master_synthesis
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C X Y : B) (n k : ℕ) :
    (P * X = X * P ↔ evenGrade P X = X) ∧
    (peirce11 P (X * Y) = peirce11 P X * peirce11 P Y + conePlus P X * coneMinus P Y ∧
      conePlus P (X * Y) = peirce11 P X * conePlus P Y + conePlus P X * peirce00 P Y) ∧
    (chartBruhatRingEquiv hP A C (P + coneMinus P C) = P - conePlus P A ∧
      chartBruhatRingEquiv hP A C (genV P A C) = genV P A C) ∧
    (∃ Rk : B, Commute (idempotencyDefect X) Rk ∧
      idempotencyDefect (newtonPeirceStep^[k] X) = (idempotencyDefect X) ^ (2 ^ k) * Rk) ∧
    (idempotencyDefect (evenGrade P (chartBruhatRingEquiv hP A C P)) =
      idempotencyDefect (genV P A C)) ∧
    (peirceCovariantDeriv P A C (idempotencyDefect^[n] (genV P A C)) = 0 ∧
      peirceCovariantDeriv P A C (newtonPeirceStep^[k] (genV P A C)) = 0 ∧
      chartBruhatRingEquiv hP A C (idempotencyDefect^[n] (genV P A C)) =
        idempotencyDefect^[n] (genV P A C) ∧
      chartBruhatRingEquiv hP A C (newtonPeirceStep^[k] (genV P A C)) =
        newtonPeirceStep^[k] (genV P A C)) := by
  have hS1 := binaryCut_commutant_characterization hP X
  have hS2 := fourfold_peirce_noncomm_mul_blocks hP X Y
  have hS3 := bruhatPerspective_rotatedCut_and_metric_invariance hP A C
  have hS4 := idempotencyDefect_newtonPeirceStep_iterate_factor X k
  have hS5a := (pinched_bruhatPerspective_defect_eq_genV_defect hP A C).2.2
  have hS5b := all_depth_meta_tower_covariant_constancy_and_bruhat_invariance hP A C n k
  refine ⟨hS1.1.trans (hS1.2.1.trans hS1.2.2.1), ⟨hS2.1, hS2.2.1⟩, ⟨hS3.2.1, hS3.2.2.2.1⟩,
    hS4, hS5a, hS5b.1, hS5b.2.2.2.1, hS5b.2.2.1, hS5b.2.2.2.2.2⟩

/-! ### `TypedArchetype` Audit Registration & Certified `MetaEpistemicCompiler` Closure -/

/-- Parametric `TypedArchetype` packaging all six stages over an arbitrary noncommutative
ring `B : Type`, realized concretely below on `M₂(Mat2C)` and `M₂(Mat2Z)`. -/
def peirceBruhatAporiaPosetArchetype (B : Type) [Ring B] : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry.peirceBruhatAporiaPosetArchetype
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    ∀ (P : B) (hP : P * P = P) (A C X Y : B) (n k : ℕ),
      (P * X = X * P ↔ evenGrade P X = X) ∧
      (peirce11 P (X * Y) = peirce11 P X * peirce11 P Y + conePlus P X * coneMinus P Y ∧
        conePlus P (X * Y) = peirce11 P X * conePlus P Y + conePlus P X * peirce00 P Y) ∧
      (chartBruhatRingEquiv hP A C (P + coneMinus P C) = P - conePlus P A ∧
        chartBruhatRingEquiv hP A C (genV P A C) = genV P A C) ∧
      (∃ Rk : B, Commute (idempotencyDefect X) Rk ∧
        idempotencyDefect (newtonPeirceStep^[k] X) = (idempotencyDefect X) ^ (2 ^ k) * Rk) ∧
      (idempotencyDefect (evenGrade P (chartBruhatRingEquiv hP A C P)) =
        idempotencyDefect (genV P A C)) ∧
      (peirceCovariantDeriv P A C (idempotencyDefect^[n] (genV P A C)) = 0 ∧
        peirceCovariantDeriv P A C (newtonPeirceStep^[k] (genV P A C)) = 0 ∧
        chartBruhatRingEquiv hP A C (idempotencyDefect^[n] (genV P A C)) =
          idempotencyDefect^[n] (genV P A C) ∧
        chartBruhatRingEquiv hP A C (newtonPeirceStep^[k] (genV P A C)) =
          newtonPeirceStep^[k] (genV P A C))
  evidence := fun _ P hP A C X Y n k =>
    epistemic_peirce_bruhat_aporia_master_synthesis (P := P) hP A C X Y n k

/-- Node `S1` proved `TypedArchetype` on the 4-dimensional noncommutative spin-block carrier
`Matrix (Fin 2) (Fin 2) Mat2C`: binary cut commutant equivalence. -/
noncomputable def archS1BinaryCut :
    TypedArchetype (Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry.archS1BinaryCut
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun X =>
    let P : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C := peirceCut2
    (P * X = X * P ↔ peirceGradingDeriv P X = 0) ∧
    (peirceGradingDeriv P X = 0 ↔ oddGrade P X = 0) ∧
    (oddGrade P X = 0 ↔ evenGrade P X = X) ∧
    (P * X = X * P → parityConj P X = X)
  evidence := fun X =>
    binaryCut_commutant_characterization (peirceCut2_idempotent (B := InfoGeometry.Algebra.FiniteSpin.Mat2C)) X

/-- Node `S2` proved `TypedArchetype` on `M₂(Mat2C)`: fourfold quiver block product. -/
noncomputable def archS2FourfoldPeirce :
    TypedArchetype
      (Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C ×
        Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry.archS2FourfoldPeirce
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun xy =>
    let P : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C := peirceCut2
    peirce11 P (xy.1 * xy.2) = peirce11 P xy.1 * peirce11 P xy.2 + conePlus P xy.1 * coneMinus P xy.2 ∧
    conePlus P (xy.1 * xy.2) = peirce11 P xy.1 * conePlus P xy.2 + conePlus P xy.1 * peirce00 P xy.2 ∧
    coneMinus P (xy.1 * xy.2) = coneMinus P xy.1 * peirce11 P xy.2 + peirce00 P xy.1 * coneMinus P xy.2 ∧
    peirce00 P (xy.1 * xy.2) = coneMinus P xy.1 * conePlus P xy.2 + peirce00 P xy.1 * peirce00 P xy.2
  evidence := fun xy =>
    fourfold_peirce_noncomm_mul_blocks
      (peirceCut2_idempotent (B := InfoGeometry.Algebra.FiniteSpin.Mat2C)) xy.1 xy.2

/-- Node `S3` proved `TypedArchetype` on `M₂(Mat2C)`: Bruhat perspective automorphism,
`StarRing` self/skew-adjoint split, and star-Gram factorization. -/
noncomputable def archS3TranscendentBruhat :
    TypedArchetype
      (Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C ×
        Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry.archS3TranscendentBruhat
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun ac =>
    let P : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C := peirceCut2
    let hP : P * P = P := peirceCut2_idempotent
    let e := chartBruhatRingEquiv hP ac.1 ac.2
    e (P + coneMinus P ac.2) = P - conePlus P ac.1 ∧
    e (genV P ac.1 ac.2) = genV P ac.1 ac.2 ∧
    star (genPhi P ac.1 (star ac.1)) = genPhi P ac.1 (star ac.1) ∧
    star (genJ P ac.1 (star ac.1)) = -genJ P ac.1 (star ac.1) ∧
    genV P ac.1 (star ac.1) = star (genPhi P ac.1 (star ac.1)) * genPhi P ac.1 (star ac.1)
  evidence := fun ac => by
    have hP : (peirceCut2 : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C) *
        peirceCut2 = peirceCut2 := peirceCut2_idempotent
    have hPs : star (peirceCut2 : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C) =
        peirceCut2 := by
      ext i j k l
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
        simp [peirceCut2, Matrix.star_apply]
    have hB := bruhatPerspective_rotatedCut_and_metric_invariance hP ac.1 ac.2
    have hS := star_transcendent_adjoint_and_gram_factorization hP hPs ac.1
    exact ⟨hB.2.1, hB.2.2.2.1, hS.2.2.1, hS.2.2.2.1, hS.2.2.2.2.2.2⟩

/-- Node `S4` proved `TypedArchetype` on `M₂(Mat2C) × ℕ`: all-`k` `2^k`-power factorization
of Newton–Peirce idempotency defect. -/
noncomputable def archS4AporiaDefectTower :
    TypedArchetype (Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C × ℕ) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry.archS4AporiaDefectTower
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun xk =>
    ∃ Rk : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C,
      Commute (idempotencyDefect xk.1) Rk ∧
      idempotencyDefect (newtonPeirceStep^[xk.2] xk.1) = (idempotencyDefect xk.1) ^ (2 ^ xk.2) * Rk
  evidence := fun xk =>
    idempotencyDefect_newtonPeirceStep_iterate_factor xk.1 xk.2

/-- Node `S5` proved `TypedArchetype` on `M₂(Mat2C) × M₂(Mat2C) × ℕ × ℕ`: pinched rotated-cut
defect law and all-depth covariant constancy across both towers. -/
noncomputable def archS5CovariantMetaTower :
    TypedArchetype
      (Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C ×
        Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C × ℕ × ℕ) .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry.archS5CovariantMetaTower
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun params =>
    let P : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C := peirceCut2
    let hP : P * P = P := peirceCut2_idempotent
    let A := params.1
    let C := params.2.1
    let n := params.2.2.1
    let k := params.2.2.2
    idempotencyDefect (evenGrade P (chartBruhatRingEquiv hP A C P)) = idempotencyDefect (genV P A C) ∧
    peirceCovariantDeriv P A C (idempotencyDefect^[n] (genV P A C)) = 0 ∧
    peirceCovariantDeriv P A C (newtonPeirceStep^[k] (genV P A C)) = 0 ∧
    chartBruhatRingEquiv hP A C (idempotencyDefect^[n] (genV P A C)) =
      idempotencyDefect^[n] (genV P A C) ∧
    chartBruhatRingEquiv hP A C (newtonPeirceStep^[k] (genV P A C)) =
      newtonPeirceStep^[k] (genV P A C)
  evidence := fun params => by
    have hP : (peirceCut2 : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C) *
        peirceCut2 = peirceCut2 := peirceCut2_idempotent
    have hPinch := (pinched_bruhatPerspective_defect_eq_genV_defect hP params.1 params.2.1).2.2
    have hCov := all_depth_meta_tower_covariant_constancy_and_bruhat_invariance
      hP params.1 params.2.1 params.2.2.1 params.2.2.2
    exact ⟨hPinch, hCov.1, hCov.2.2.2.1, hCov.2.2.1, hCov.2.2.2.2.2⟩

/-- Node `S6` proved `TypedArchetype`: concrete noncommutative matrix witnesses over
`M₂(M₂(ℤ))` and `M₂(ℤ)` paired with the universal `M₂(Mat2C)` synthesis. -/
noncomputable def archS6NoncommMatrixCoagulation : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry.archS6NoncommMatrixCoagulation
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    (∃ A C : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z,
      qgtPlus peirceCut2 A C ≠ 0 ∧ qgtMinus peirceCut2 A C = 0) ∧
    (∃ X₂ : Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2Z,
      peirceCut2 * X₂ ≠ X₂ * peirceCut2 ∧
      idempotencyDefect X₂ ≠ 0 ∧
      idempotencyDefect (newtonPeirceStep X₂) ≠ 0 ∧
      (idempotencyDefect X₂) ^ (2 ^ 2) = 0 ∧
      newtonPeirceStep^[2] X₂ * newtonPeirceStep^[2] X₂ = newtonPeirceStep^[2] X₂) ∧
    (peirceBruhatAporiaPosetArchetype
      (Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C)).claim ()
  evidence := fun _ => by
    have hW1 := noncomm_fiber_one_sided_cycle_annihilation_witness
    have hW3 := strict_two_step_nondiag_newtonPeirce_matrix_witness
    have hUniv :=
      (peirceBruhatAporiaPosetArchetype
        (Matrix (Fin 2) (Fin 2) InfoGeometry.Algebra.FiniteSpin.Mat2C)).discharge ()
    refine ⟨⟨Matrix.of ![![0, !![1, 0; 0, 0]], ![0, 0]],
        Matrix.of ![![0, 0], ![!![0, 1; 0, 0], 0]], hW1.1, hW1.2.2.1⟩,
      ⟨_, hW3.1, hW3.2.1, hW3.2.2.1, hW3.2.2.2.1, ?_⟩, hUniv⟩
    rw [hW3.2.2.2.2.1]
    exact hW3.2.2.2.2.2.1

#register_archetype peirceBruhatAporiaPosetArchetype
#register_archetype archS1BinaryCut
#register_archetype archS2FourfoldPeirce
#register_archetype archS3TranscendentBruhat
#register_archetype archS4AporiaDefectTower
#register_archetype archS5CovariantMetaTower
#register_archetype archS6NoncommMatrixCoagulation

#audit_archetype archS1BinaryCut
#audit_archetype archS2FourfoldPeirce
#audit_archetype archS3TranscendentBruhat
#audit_archetype archS4AporiaDefectTower
#audit_archetype archS5CovariantMetaTower
#audit_archetype archS6NoncommMatrixCoagulation

/-- Target proposition map on the `CoagulationArchetype` diamond poset. -/
noncomputable def coagulationStatement : CoagulationArchetype → Prop
  | .S1_binaryCut => ∀ X, archS1BinaryCut.claim X
  | .S2_fourfoldPeirce => ∀ xy, archS2FourfoldPeirce.claim xy
  | .S3_transcendentBruhat => ∀ ac, archS3TranscendentBruhat.claim ac
  | .S4_aporiaDefectTower => ∀ xk, archS4AporiaDefectTower.claim xk
  | .S5_covariantMetaTower => ∀ params, archS5CovariantMetaTower.claim params
  | .S6_noncommMatrixCoagulation => archS6NoncommMatrixCoagulation.claim ()

lemma coagulationPosetRules : ProofRules coagulationStatement := by
  intro target prereqs
  cases target with
  | S1_binaryCut => exact fun X => archS1BinaryCut.discharge X
  | S2_fourfoldPeirce => exact fun xy => archS2FourfoldPeirce.discharge xy
  | S3_transcendentBruhat => exact fun ac => archS3TranscendentBruhat.discharge ac
  | S4_aporiaDefectTower => exact fun xk => archS4AporiaDefectTower.discharge xk
  | S5_covariantMetaTower =>
    have _ := prereqs .S3_transcendentBruhat (by decide)
    have _ := prereqs .S4_aporiaDefectTower (by decide)
    exact fun params => archS5CovariantMetaTower.discharge params
  | S6_noncommMatrixCoagulation =>
    have _ := prereqs .S5_covariantMetaTower (by decide)
    exact archS6NoncommMatrixCoagulation.discharge ()

/-- **Certified Execution of `MetaEpistemicCompiler` on `CoagulationArchetype`**:
Compiles the unordered worklist `canonicalPending` into a valid causal schedule preserving
the diamond partial order and discharging every target claim in `M₂(Mat2C)` and `M₂(Mat2Z)`. -/
theorem peirce_bruhat_aporia_executable_certified_compilation :
    ∃ schedule : List CoagulationArchetype,
      compile ∅ CoagulationArchetype.canonicalPending = some schedule ∧
      ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧
      schedule.length = Fintype.card CoagulationArchetype ∧
      schedule.toFinset = Finset.univ ∧
      ∀ target, coagulationStatement target :=
  executable_certified_compilation
    coagulationStatement
    coagulationPosetRules
    CoagulationArchetype.canonicalPending
    CoagulationArchetype.canonicalPending_nodup
    CoagulationArchetype.canonicalPending_univ

end Stage6_NoncommMatrixCoagulation

end InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry
