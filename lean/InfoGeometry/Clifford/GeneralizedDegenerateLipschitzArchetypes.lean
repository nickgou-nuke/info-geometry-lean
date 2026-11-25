/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.Tactic
import InfoGeometry.Clifford.GradedGraceContraction
import InfoGeometry.Clifford.LipschitzWittRieszPrimary

set_option maxHeartbeats 600000

/-!
# Archetypes for generalized degenerate Clifford and Lipschitz groups

This file formalizes the common algebraic input of Filimoshina--Shirokov,
arXiv:2505.07106v2, without imposing nondegeneracy on the quadratic form.
The paper's signature-specific centralizer tables, group classifications, and
dimension formulas are not asserted here.

The causal order records prerequisite structure: Clifford carrier, its two
involutions, their joint eigenspaces, centralizers and norm maps, stabilizers,
then group relations, examples, and Lie algebras. Centralizers and norm maps
are deliberately incomparable at their shared level.
-/

namespace InfoGeometry.Clifford.GeneralizedDegenerateLipschitzArchetypes

/-! ## A finite causal poset of mathematical archetypes -/

/-- The dependency strata extracted from Sections 2--6 and Appendix B. -/
inductive Archetype where
  | cliffordCarrier
  | gradeAndReversion
  | jointEigenspaces
  | centralizers
  | normMaps
  | stabilizerGroups
  | groupRelations
  | degenerateExamples
  | lieAlgebras
  deriving DecidableEq, Repr

/-- Rank witnesses that every direct prerequisite edge points forward. -/
def Archetype.rank : Archetype → Nat
  | .cliffordCarrier => 0
  | .gradeAndReversion => 1
  | .jointEigenspaces => 2
  | .centralizers => 3
  | .normMaps => 3
  | .stabilizerGroups => 4
  | .groupRelations => 5
  | .degenerateExamples => 5
  | .lieAlgebras => 5

/-- Direct mathematical prerequisite edges, oriented from prerequisite to use. -/
inductive DirectDependency : Archetype → Archetype → Prop where
  | carrierInvolutions : DirectDependency .cliffordCarrier .gradeAndReversion
  | involutionsJointTypes : DirectDependency .gradeAndReversion .jointEigenspaces
  | jointTypesCentralizers : DirectDependency .jointEigenspaces .centralizers
  | jointTypesNorms : DirectDependency .jointEigenspaces .normMaps
  | centralizersStabilizers : DirectDependency .centralizers .stabilizerGroups
  | normsStabilizers : DirectDependency .normMaps .stabilizerGroups
  | stabilizersRelations : DirectDependency .stabilizerGroups .groupRelations
  | stabilizersExamples : DirectDependency .stabilizerGroups .degenerateExamples
  | stabilizersLieAlgebras : DirectDependency .stabilizerGroups .lieAlgebras

/-- Reflexive-transitive closure of the direct prerequisite relation. -/
def descendants : Archetype → Finset Archetype
  | .cliffordCarrier => {.gradeAndReversion, .jointEigenspaces, .centralizers,
      .normMaps, .stabilizerGroups, .groupRelations, .degenerateExamples,
      .lieAlgebras}
  | .gradeAndReversion => {.jointEigenspaces, .centralizers, .normMaps,
      .stabilizerGroups, .groupRelations, .degenerateExamples, .lieAlgebras}
  | .jointEigenspaces => {.centralizers, .normMaps, .stabilizerGroups,
      .groupRelations, .degenerateExamples, .lieAlgebras}
  | .centralizers => {.stabilizerGroups, .groupRelations, .degenerateExamples,
      .lieAlgebras}
  | .normMaps => {.stabilizerGroups, .groupRelations, .degenerateExamples,
      .lieAlgebras}
  | .stabilizerGroups => {.groupRelations, .degenerateExamples, .lieAlgebras}
  | .groupRelations => ∅
  | .degenerateExamples => ∅
  | .lieAlgebras => ∅

/-- Explicit transitive closure of the prerequisite edges. -/
def CausalLE (a b : Archetype) : Prop := a = b ∨ b ∈ descendants a

/-- The dependency relation is a genuine partial order, not an informal DAG sketch. -/
instance : PartialOrder Archetype where
  le := CausalLE
  le_refl a := Or.inl rfl
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;>
      simp_all [CausalLE, descendants]
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;>
      simp_all [CausalLE, descendants]

theorem centralizers_incomparable_normMaps :
    ¬ CausalLE .centralizers .normMaps ∧ ¬ CausalLE .normMaps .centralizers := by
  constructor <;> intro h <;> simp [CausalLE, descendants] at h

/-! ## Strict algebraic language for the paper's core objects -/

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M)

abbrev GA := CliffordAlgebra Q

/-! ## Signature-indexed degenerate models -/

/-- Diagonal weights for the paper's signature `(p,q,r)`: positive, negative,
and radical coordinates respectively. -/
def degenerateSignatureWeight (p q r : ℕ) : Fin (p + q + r) → ℝ := fun i =>
  if i.val < p then 1 else if i.val < p + q then -1 else 0

/-- The native Mathlib quadratic form of signature `(p,q,r)`, with no
nondegeneracy assumption. -/
def degenerateSignatureForm (p q r : ℕ) :
    QuadraticForm ℝ (Fin (p + q + r) → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ (degenerateSignatureWeight p q r)

/-- The corresponding degenerate Clifford carrier `Cl_{p,q,r}`. -/
abbrev DegenerateClifford (p q r : ℕ) :=
  CliffordAlgebra (degenerateSignatureForm p q r)

/-- A coordinate basis vector in the radical block. -/
def radicalCoordinate (p q r : ℕ) (i : Fin (p + q + r)) :
    Fin (p + q + r) → ℝ := Pi.single i 1

/-- Every radical coordinate is null for the signature form. -/
theorem radicalCoordinate_form_eq_zero (p q r : ℕ)
    (i : Fin (p + q + r)) (hi : p + q ≤ i.val) :
    degenerateSignatureForm p q r (radicalCoordinate p q r i) = 0 := by
  rw [degenerateSignatureForm, QuadraticMap.weightedSumSquares_apply]
  simp only [radicalCoordinate, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp [degenerateSignatureWeight, hi, Nat.not_lt.mpr (by omega : p ≤ i.val)]
  · intro j hj hji
    simp [hji]
  · simp

/-- The quadratic value of each coordinate vector is its signature weight.
This exposes the positive, negative, and radical rows of the `(p,q,r)` table. -/
theorem signatureCoordinate_form_eq_weight (p q r : ℕ)
    (i : Fin (p + q + r)) :
    degenerateSignatureForm p q r (radicalCoordinate p q r i) =
      degenerateSignatureWeight p q r i := by
  rw [degenerateSignatureForm, QuadraticMap.weightedSumSquares_apply]
  simp only [radicalCoordinate, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp [degenerateSignatureWeight]
  · intro j hj hji
    simp [hji]
  · simp

/-- Positive coordinate vectors have quadratic value `+1`. -/
theorem positiveSignatureCoordinate_form_eq_one (p q r : ℕ)
    (i : Fin (p + q + r)) (hi : i.val < p) :
    degenerateSignatureForm p q r (radicalCoordinate p q r i) = 1 := by
  rw [signatureCoordinate_form_eq_weight]
  simp [degenerateSignatureWeight, hi]

/-- Negative coordinate vectors have quadratic value `-1`. -/
theorem negativeSignatureCoordinate_form_eq_neg_one (p q r : ℕ)
    (i : Fin (p + q + r)) (hi₁ : p ≤ i.val) (hi₂ : i.val < p + q) :
    degenerateSignatureForm p q r (radicalCoordinate p q r i) = -1 := by
  rw [signatureCoordinate_form_eq_weight]
  simp [degenerateSignatureWeight, Nat.not_lt.mpr hi₁, hi₂]

/-- Clifford generators in the radical have square zero. This is the basic
degenerate example underlying the Grassmann and plane-based cases. -/
theorem radicalGenerator_sq_zero (p q r : ℕ)
    (i : Fin (p + q + r)) (hi : p + q ≤ i.val) :
    (CliffordAlgebra.ι (degenerateSignatureForm p q r)
      (radicalCoordinate p q r i)) ^ 2 = 0 := by
  rw [pow_two, CliffordAlgebra.ι_sq_scalar,
    radicalCoordinate_form_eq_zero p q r i hi]
  simp

/-- Every positive radical dimension supplies a nonzero square-zero Clifford
generator, witnessed through Mathlib's exterior-algebra equivalence. -/
theorem exists_nonzero_radical_nilpotent (p q r : ℕ) (hr : 0 < r) :
    ∃ z : DegenerateClifford p q r, z ≠ 0 ∧ z ^ 2 = 0 := by
  let i : Fin (p + q + r) := ⟨p + q, by
    have hr' : r ≠ 0 := Nat.ne_of_gt hr
    omega⟩
  have hi : p + q ≤ i.val := by simp [i]
  refine ⟨CliffordAlgebra.ι (degenerateSignatureForm p q r)
      (radicalCoordinate p q r i), ?_, radicalGenerator_sq_zero p q r i hi⟩
  intro hz
  have hzero : CliffordAlgebra.ι (degenerateSignatureForm p q r)
      (radicalCoordinate p q r i) = CliffordAlgebra.ι _ 0 := by simpa using hz
  have hv := InfoGeometry.Clifford.GradedGraceContraction.clifford_ι_injective
    (degenerateSignatureForm p q r) hzero
  have hi := congrFun hv i
  simp [radicalCoordinate, i] at hi

/-- Grade-involution sign for the paper's quaternion type indexed by `Fin 4`. -/
def gradeSign (i : Fin 4) : ℝ :=
  if i.val = 1 ∨ i.val = 3 then -1 else 1

/-- Reversion sign for the paper's quaternion type indexed by `Fin 4`. -/
def reversionSign (i : Fin 4) : ℝ :=
  if i.val = 2 ∨ i.val = 3 then -1 else 1

/-- The four joint eigenspaces of grade involution and reversion, as actual
linear subspaces rather than just predicates on elements. Their sign pairs are
`(+,+)`, `(-,+)`, `(+,-)`, and `(-,-)`. -/
def jointTypeSubmodule (i : Fin 4) : Submodule ℝ (GA Q) :=
  LinearMap.ker
      (CliffordAlgebra.involute.toLinearMap - gradeSign i • LinearMap.id) ⊓
    LinearMap.ker
      (CliffordAlgebra.reverse - reversionSign i • LinearMap.id)

/-- Set carrier of the joint eigenspace. -/
def jointType (i : Fin 4) : Set (GA Q) := jointTypeSubmodule Q i

/-- A pair of quaternion types denotes their linear direct-sum carrier. -/
def jointPairSubmodule (i j : Fin 4) : Submodule ℝ (GA Q) :=
  jointTypeSubmodule Q i ⊔ jointTypeSubmodule Q j

theorem mem_jointType_iff (i : Fin 4) (x : GA Q) :
    x ∈ jointTypeSubmodule Q i ↔
      CliffordAlgebra.involute x = gradeSign i • x ∧
        CliffordAlgebra.reverse x = reversionSign i • x := by
  by_cases h1 : i.val = 1 ∨ i.val = 3
  <;> by_cases h2 : i.val = 2 ∨ i.val = 3
  <;> simp [jointTypeSubmodule, gradeSign, reversionSign, LinearMap.mem_ker,
    LinearMap.sub_apply, h1, h2, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- Simultaneous grade/reversion eigenspace projection. The factor `1/4` uses
the real coefficient field; no nondegeneracy assumption on `Q` is involved. -/
noncomputable def jointTypeProjector (i : Fin 4) (x : GA Q) : GA Q :=
  (1 / 4 : ℝ) •
    (x + gradeSign i • CliffordAlgebra.involute x +
      reversionSign i • CliffordAlgebra.reverse x +
      (gradeSign i * reversionSign i) •
        CliffordAlgebra.involute (CliffordAlgebra.reverse x))

/-- The simultaneous projector lands in the joint eigenspace with its indexed
sign pair. -/
theorem jointTypeProjector_mem (i : Fin 4) (x : GA Q) :
    jointTypeProjector Q i x ∈ jointTypeSubmodule Q i := by
  rw [mem_jointType_iff]
  fin_cases i <;>
    simp [jointTypeProjector, gradeSign, reversionSign, map_add, map_smul,
      CliffordAlgebra.involute_involute, CliffordAlgebra.reverse_reverse,
      CliffordAlgebra.reverse_involute] <;> abel <;> trivial

/-- The four simultaneous sign projectors sum to the identity. -/
theorem jointTypeProjector_sum (x : GA Q) :
    ∑ i : Fin 4, jointTypeProjector Q i x = x := by
  simp only [Fin.sum_univ_succ]
  simp [jointTypeProjector, gradeSign, reversionSign]
  abel
  rw [← Int.cast_smul_eq_zsmul ℝ]
  rw [smul_smul]
  norm_num

/-- The grade-even component of an element. -/
noncomputable def gradeEvenComponent (x : GA Q) : GA Q :=
  (1 / 2 : ℝ) • (x + CliffordAlgebra.involute x)

/-- The grade-odd component of an element. -/
noncomputable def gradeOddComponent (x : GA Q) : GA Q :=
  (1 / 2 : ℝ) • (x - CliffordAlgebra.involute x)

/-- The paper's joint types 0 and 1 together are exactly the reverse-fixed
subspace. This is a vector-space decomposition by grade parity, and uses the
commutation of grade involution with reversion. -/
theorem jointPair_01_eq_reverseFixed :
    (jointPairSubmodule Q 0 1 : Set (GA Q)) =
      {x | CliffordAlgebra.reverse x = x} := by
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, hv, rfl⟩
    have hu' := (mem_jointType_iff Q 0 u).mp hu
    have hv' := (mem_jointType_iff Q 1 v).mp hv
    change CliffordAlgebra.reverse (u + v) = u + v
    rw [map_add, hu'.2, hv'.2]
    norm_num [reversionSign]
  · intro hx
    change CliffordAlgebra.reverse x = x at hx
    let u := gradeEvenComponent Q x
    let v := gradeOddComponent Q x
    have hu : u ∈ jointTypeSubmodule Q 0 := by
      rw [mem_jointType_iff]
      constructor
      · simp [u, gradeEvenComponent, gradeSign, map_add]
        abel
      · simp [u, gradeEvenComponent, reversionSign, map_add,
          CliffordAlgebra.reverse_involute, hx]
    have hv : v ∈ jointTypeSubmodule Q 1 := by
      rw [mem_jointType_iff]
      constructor
      · simp [v, gradeOddComponent, gradeSign, map_sub]
        module
      · simp [v, gradeOddComponent, reversionSign, map_sub,
          CliffordAlgebra.reverse_involute, hx]
    have huv : u + v = x := by
      simp [u, v, gradeEvenComponent, gradeOddComponent]
      module
    exact Submodule.mem_sup.mpr ⟨u, hu, v, hv, huv⟩

/-- The paper's joint types 2 and 3 together are exactly the reverse-anti-fixed
subspace, again by grade-parity decomposition. -/
theorem jointPair_23_eq_reverseAntiFixed :
    (jointPairSubmodule Q 2 3 : Set (GA Q)) =
      {x | CliffordAlgebra.reverse x = -x} := by
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, hv, rfl⟩
    have hu' := (mem_jointType_iff Q 2 u).mp hu
    have hv' := (mem_jointType_iff Q 3 v).mp hv
    change CliffordAlgebra.reverse (u + v) = -(u + v)
    rw [map_add, hu'.2, hv'.2]
    norm_num [reversionSign]
    abel
  · intro hx
    change CliffordAlgebra.reverse x = -x at hx
    let u := gradeEvenComponent Q x
    let v := gradeOddComponent Q x
    have hu : u ∈ jointTypeSubmodule Q 2 := by
      rw [mem_jointType_iff]
      constructor
      · simp [u, gradeEvenComponent, gradeSign, map_add]
        abel
      · simp [u, gradeEvenComponent, reversionSign, map_add,
          CliffordAlgebra.reverse_involute, hx]
    have hv : v ∈ jointTypeSubmodule Q 3 := by
      rw [mem_jointType_iff]
      constructor
      · simp [v, gradeOddComponent, gradeSign, map_sub]
        module
      · simp [v, gradeOddComponent, reversionSign, map_sub,
          CliffordAlgebra.reverse_involute, hx]
        module
    have huv : u + v = x := by
      simp [u, v, gradeEvenComponent, gradeOddComponent]
      module
    exact Submodule.mem_sup.mpr ⟨u, hu, v, hv, huv⟩

/-- The four quaternion types have the paper's exact grade/reversion sign table. -/
theorem quaternionType_sign_table :
    (gradeSign (0 : Fin 4), reversionSign 0) = (1, 1) ∧
    (gradeSign (1 : Fin 4), reversionSign 1) = (-1, 1) ∧
    (gradeSign (2 : Fin 4), reversionSign 2) = (1, -1) ∧
    (gradeSign (3 : Fin 4), reversionSign 3) = (-1, -1) := by
  norm_num [gradeSign, reversionSign]

/-- Centralizer of a set, with multiplication order matching the paper. -/
def centralizerSet (S : Set (GA Q)) : Set (GA Q) :=
  {x | ∀ y, y ∈ S → x * y = y * x}

/-- Grade-twisted centralizer: `involute x * y = y * x`. -/
def twistedCentralizerSet (S : Set (GA Q)) : Set (GA Q) :=
  {x | ∀ y, y ∈ S → CliffordAlgebra.involute x * y = y * x}

/-- Reversion norm `reverse(g) * g`, the paper's `ψ(g)`. -/
def reversionNorm (g : (GA Q)ˣ) : GA Q :=
  CliffordAlgebra.reverse (g : GA Q) * (g : GA Q)

/-- Clifford norm `involute(reverse(g)) * g`, the paper's `χ(g)`. -/
def cliffordNorm (g : (GA Q)ˣ) : GA Q :=
  CliffordAlgebra.involute (CliffordAlgebra.reverse (g : GA Q)) * (g : GA Q)

/-- Paper's fixed-grade carrier `Cl^m`, using the repository's grade projector.
This construction is available over arbitrary quadratic forms, including
degenerate ones. -/
noncomputable def fixedGradeCarrier (m : ℕ) : Submodule ℝ (GA Q) :=
  InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeSubmodule Q m

/-- Sum of homogeneous grade carriers `Cl^k ⊕ Cl^l`. This is distinct from
`jointPairSubmodule`, whose indices refer to involution eigenspaces. -/
noncomputable def homogeneousGradePairCarrier (k l : ℕ) : Submodule ℝ (GA Q) :=
  fixedGradeCarrier Q k ⊔ fixedGradeCarrier Q l

/-- Ordinary centralizer of a fixed homogeneous grade, in paper notation `Z^m`. -/
def fixedGradeCentralizer (m : ℕ) : Set (GA Q) :=
  centralizerSet Q (fixedGradeCarrier Q m : Set (GA Q))

/-- Grade-twisted centralizer of a fixed homogeneous grade, in paper notation
`Ž^m`. -/
def fixedGradeTwistedCentralizer (m : ℕ) : Set (GA Q) :=
  twistedCentralizerSet Q (fixedGradeCarrier Q m : Set (GA Q))

/-- Ordinary centralizer of a sum of homogeneous grade carriers. -/
def homogeneousGradePairCentralizer (k l : ℕ) : Set (GA Q) :=
  centralizerSet Q (homogeneousGradePairCarrier Q k l : Set (GA Q))

/-- Grade zero is exactly the image of the scalar algebra map. -/
theorem fixedGradeCarrier_zero_eq_scalarRange :
    (fixedGradeCarrier Q 0 : Set (GA Q)) = Set.range (algebraMap ℝ (GA Q)) := by
  ext x
  change x ∈ InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeSubmodule Q 0 ↔ _
  rw [InfoGeometry.Clifford.GradedGraceContraction.mem_cliffordGradeSubmodule_iff]
  constructor
  · intro hx
    rw [InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj_zero_eq_algebraMap_hTrace]
      at hx
    exact ⟨_, hx⟩
  · rintro ⟨r, rfl⟩
    rw [InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj_zero_algebraMap]

/-- The paper's `Z^{01} = Z^1` reduction: adjoining grade zero scalars to
grade one does not change its ordinary centralizer. -/
theorem homogeneousGradePairCentralizer_01_eq_gradeOne :
    homogeneousGradePairCentralizer Q 0 1 = fixedGradeCentralizer Q 1 := by
  ext x
  constructor
  · intro hx y hy
    exact hx y (Submodule.mem_sup_right hy)
  · intro hx y hy
    rcases Submodule.mem_sup.mp hy with ⟨a, ha, b, hb, hab⟩
    have ha' : a ∈ Set.range (algebraMap ℝ (GA Q)) := by
      rw [← fixedGradeCarrier_zero_eq_scalarRange Q]
      exact ha
    rcases ha' with ⟨r, rfl⟩
    rw [← hab, mul_add, add_mul, hx b hb]
    exact congrArg (fun z : GA Q => z + b * x)
      ((Algebra.commutes r x).symm)

/-- Grade zero consists of scalars, so adjoining it to any homogeneous grade
does not change the ordinary centralizer. -/
theorem homogeneousGradePairCentralizer_zero_eq_fixedGrade (k : ℕ) :
    homogeneousGradePairCentralizer Q 0 k = fixedGradeCentralizer Q k := by
  ext x
  constructor
  · intro hx y hy
    exact hx y (Submodule.mem_sup_right hy)
  · intro hx y hy
    rcases Submodule.mem_sup.mp hy with ⟨a, ha, b, hb, hab⟩
    have ha' : a ∈ Set.range (algebraMap ℝ (GA Q)) := by
      rw [← fixedGradeCarrier_zero_eq_scalarRange Q]
      exact ha
    rcases ha' with ⟨r, rfl⟩
    rw [← hab, mul_add, add_mul, hx b hb]
    exact congrArg (fun z : GA Q => z + b * x)
      ((Algebra.commutes r x).symm)

/-- The homogeneous-grade pair cases with grade zero and grade two. -/
theorem homogeneousGradePairCentralizer_02_eq_gradeTwo :
    homogeneousGradePairCentralizer Q 0 2 = fixedGradeCentralizer Q 2 :=
  homogeneousGradePairCentralizer_zero_eq_fixedGrade Q 2

theorem homogeneousGradePairCentralizer_03_eq_gradeThree :
    homogeneousGradePairCentralizer Q 0 3 = fixedGradeCentralizer Q 3 :=
  homogeneousGradePairCentralizer_zero_eq_fixedGrade Q 3

/-- Centralizing the direct sum of homogeneous grades two and three is
equivalent to centralizing each summand. -/
theorem homogeneousGradePairCentralizer_23_eq_gradeTwo_inter_gradeThree :
    homogeneousGradePairCentralizer Q 2 3 =
      fixedGradeCentralizer Q 2 ∩ fixedGradeCentralizer Q 3 := by
  ext x
  simp only [homogeneousGradePairCentralizer, homogeneousGradePairCarrier, fixedGradeCentralizer,
    centralizerSet, Set.mem_inter_iff]
  constructor
  · intro h
    constructor
    · intro y hy
      exact h y (Submodule.mem_sup_left hy)
    · intro y hy
      exact h y (Submodule.mem_sup_right hy)
  · rintro ⟨h₂, h₃⟩ y hy
    rcases Submodule.mem_sup.mp hy with ⟨a, ha, b, hb, hab⟩
    rw [← hab, mul_add, add_mul, h₂ a ha, h₃ b hb]

/-- Each Clifford generator belongs to the paper's grade-one carrier. -/
theorem cliffordGenerator_mem_fixedGradeCarrier_one (v : M) :
    CliffordAlgebra.ι Q v ∈ fixedGradeCarrier Q 1 := by
  rw [fixedGradeCarrier,
    InfoGeometry.Clifford.GradedGraceContraction.mem_cliffordGradeSubmodule_iff]
  exact InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj_one_ι Q v

/-- Every grade-one element is fixed by reversion. -/
theorem fixedGradeCarrier_one_subset_reverseFixed :
    (fixedGradeCarrier Q 1 : Set (GA Q)) ⊆
      {x | CliffordAlgebra.reverse x = x} := by
  intro x hx
  have hxProj : InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q 1 x = x :=
    (InfoGeometry.Clifford.GradedGraceContraction.mem_cliffordGradeSubmodule_iff 1 x).mp hx
  rw [← hxProj]
  simpa using
    InfoGeometry.Clifford.LipschitzWittRieszPrimary.cliffordGradeProj_reverse Q 1 x

/-- The centralizer of grade one is the center: commuting with all generators
extends to the whole Clifford algebra by its universal-property induction. -/
theorem fixedGradeCentralizer_one_eq_centralizer_univ :
    fixedGradeCentralizer Q 1 = centralizerSet Q Set.univ := by
  ext a
  constructor
  · intro ha y _
    have hcomm : ∀ y : GA Q, a * y = y * a := by
      intro y
      induction y using CliffordAlgebra.induction with
      | algebraMap r => exact (Algebra.commutes r a).symm
      | ι v => exact ha _ (cliffordGenerator_mem_fixedGradeCarrier_one Q v)
      | add y z hy hz => simp only [mul_add, add_mul, hy, hz]
      | mul y z hy hz =>
        calc
          a * (y * z) = (a * y) * z := by noncomm_ring
          _ = (y * a) * z := congrArg (fun t => t * z) hy
          _ = y * (a * z) := by noncomm_ring
          _ = y * (z * a) := congrArg (fun t => y * t) hz
          _ = (y * z) * a := by noncomm_ring
    exact hcomm y
  · intro ha y _
    exact ha y (Set.mem_univ y)

/-- The reverse-fixed sector and the grade-one carrier have the same ordinary
centralizer, the paper's joint-sector reduction used in Theorem 4.1. -/
theorem reverseFixedCentralizer_eq_fixedGradeCentralizer_one :
    centralizerSet Q {x | CliffordAlgebra.reverse x = x} =
      fixedGradeCentralizer Q 1 := by
  ext a
  constructor
  · intro ha y hy
    exact ha y (fixedGradeCarrier_one_subset_reverseFixed Q hy)
  · intro ha y hy
    have ha' : a ∈ centralizerSet Q Set.univ := by
      rw [← fixedGradeCentralizer_one_eq_centralizer_univ Q]
      exact ha
    exact ha' y (Set.mem_univ y)

/-- Ordinary centralizer of one of the four grade-involution/reversion joint
eigenspaces. -/
def quaternionTypeCentralizer (i : Fin 4) : Set (GA Q) :=
  centralizerSet Q (jointTypeSubmodule Q i : Set (GA Q))

/-- Grade-twisted centralizer of one quaternion type. -/
def quaternionTypeTwistedCentralizer (i : Fin 4) : Set (GA Q) :=
  twistedCentralizerSet Q (jointTypeSubmodule Q i : Set (GA Q))

/-- Ordinary centralizer of a direct sum of two quaternion types. -/
def quaternionPairCentralizer (i j : Fin 4) : Set (GA Q) :=
  centralizerSet Q (jointPairSubmodule Q i j : Set (GA Q))

/-- Twisted centralizer of a direct sum of two quaternion types. -/
def quaternionPairTwistedCentralizer (i j : Fin 4) : Set (GA Q) :=
  twistedCentralizerSet Q (jointPairSubmodule Q i j : Set (GA Q))

/-- The centralizer of a sum of two joint-involution sectors is the
intersection of their centralizers. Identifying these with the paper's
grade-indexed table uses the separate grade-centralizer lemmas. -/
theorem quaternionPairCentralizer_eq_inter (i j : Fin 4) :
    quaternionPairCentralizer Q i j =
      quaternionTypeCentralizer Q i ∩ quaternionTypeCentralizer Q j := by
  ext x
  simp only [quaternionPairCentralizer, quaternionTypeCentralizer, jointPairSubmodule,
    centralizerSet, Set.mem_inter_iff]
  constructor
  · intro h
    constructor
    · intro y hy
      exact h y (Submodule.mem_sup_left hy)
    · intro y hy
      exact h y (Submodule.mem_sup_right hy)
  · rintro ⟨hi, hj⟩ y hy
    rcases Submodule.mem_sup.mp hy with ⟨a, ha, b, hb, hab⟩
    rw [← hab, mul_add, add_mul, hi a ha, hj b hb]

/-- Norm-table carrier `A^01`: reversion norm in the centralizer of grade one. -/
def PaperA01 : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈ fixedGradeCentralizer Q 1}

/-- Norm-table carrier `A^23`: reversion norm centralizes paper grades 2 and 3. -/
def PaperA23 : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈
    fixedGradeCentralizer Q 2 ∩ fixedGradeCentralizer Q 3}

/-- Norm-table carrier `B^12`: Clifford norm in the centralizer of grade one. -/
def PaperB12 : Set (GA Q)ˣ :=
  {g | cliffordNorm Q g ∈ fixedGradeCentralizer Q 1}

/-- Norm-table carrier `B^03`: Clifford norm centralizes quaternion type 3. -/
def PaperB03 : Set (GA Q)ˣ :=
  {g | cliffordNorm Q g ∈ quaternionTypeCentralizer Q 3}

/-- Checked norm-table carrier `Ǎ^12`. -/
def PaperACheck12 : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈
    fixedGradeTwistedCentralizer Q 1 ∩ fixedGradeTwistedCentralizer Q 2}

/-- Checked norm-table carrier `Ǎ^03`. -/
def PaperACheck03 : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈
    fixedGradeCentralizer Q 3 ∩ fixedGradeCarrier Q 0}

/-- Checked norm-table carrier `B̌^01`. -/
def PaperBCheck01 : Set (GA Q)ˣ :=
  {g | cliffordNorm Q g ∈
    fixedGradeTwistedCentralizer Q 1 ∩ fixedGradeCarrier Q 0}

/-- Checked norm-table carrier `B̌^23`. -/
def PaperBCheck23 : Set (GA Q)ˣ :=
  {g | cliffordNorm Q g ∈
    fixedGradeTwistedCentralizer Q 2 ∩ fixedGradeTwistedCentralizer Q 3}

/-- Modified twisted norm-table carrier `Q̃^01`. -/
def PaperQCheck01 : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈ fixedGradeCentralizer Q 4 ∧
    cliffordNorm Q g ∈ fixedGradeTwistedCentralizer Q 1}

/-- Modified twisted norm-table carrier `Q̃^23`. -/
def PaperQCheck23 : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈ fixedGradeCentralizer Q 2 ∧
    cliffordNorm Q g ∈ fixedGradeTwistedCentralizer Q 3}

/-- Modified twisted norm-table carrier `Q̃^12`. -/
def PaperQCheck12 : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈ fixedGradeTwistedCentralizer Q 1 ∧
    cliffordNorm Q g ∈ fixedGradeCentralizer Q 2}

/-- Modified twisted norm-table carrier `Q̃^03`. -/
def PaperQCheck03 : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈ fixedGradeTwistedCentralizer Q 3 ∧
    cliffordNorm Q g ∈ fixedGradeCentralizer Q 4}

/-- Ordinary adjoint action by a Clifford unit. -/
def adjointAction (g : (GA Q)ˣ) (x : GA Q) : GA Q :=
  (g : GA Q) * x * ((g⁻¹ : (GA Q)ˣ) : GA Q)

/-- Grade-twisted adjoint action used for the generalized Lipschitz lane. -/
def gradeTwistedAdjointAction (g : (GA Q)ˣ) (x : GA Q) : GA Q :=
  CliffordAlgebra.involute (g : GA Q) * x * ((g⁻¹ : (GA Q)ˣ) : GA Q)

/-- Even component for the grade-involution splitting. -/
noncomputable def evenGradePart (x : GA Q) : GA Q :=
  (1 / 2 : ℝ) • (x + CliffordAlgebra.involute x)

/-- Odd component for the grade-involution splitting. -/
noncomputable def oddGradePart (x : GA Q) : GA Q :=
  (1 / 2 : ℝ) • (x - CliffordAlgebra.involute x)

/-- The paper's second twisted action `ad~`: conjugate the even part by `g` and
the odd part by the grade involution of `g`. -/
noncomputable def modifiedTwistedAdjointAction (g : (GA Q)ˣ) (x : GA Q) : GA Q :=
  (g : GA Q) * evenGradePart Q x * ((g⁻¹ : (GA Q)ˣ) : GA Q) +
    CliffordAlgebra.involute (g : GA Q) * oddGradePart Q x *
      ((g⁻¹ : (GA Q)ˣ) : GA Q)

/-- Setwise stabilizer predicate for a unit action. -/
def stabilizes (act : (GA Q)ˣ → GA Q → GA Q) (S : Set (GA Q)) :
    Set (GA Q)ˣ :=
  {g | ∀ x, x ∈ S → act g x ∈ S}

/-- Geometric group carrier preserving the direct sum of quaternion types `i,j`
under ordinary adjoint action. -/
def adjointPairStabilizer (i j : Fin 4) : Set (GA Q)ˣ :=
  stabilizes Q (adjointAction Q) (jointPairSubmodule Q i j : Set (GA Q))

/-- Geometric group carrier preserving a quaternion-type pair under the first
twisted adjoint action. -/
def twistedPairStabilizer (i j : Fin 4) : Set (GA Q)ˣ :=
  stabilizes Q (gradeTwistedAdjointAction Q) (jointPairSubmodule Q i j : Set (GA Q))

/-- Geometric group carrier preserving a quaternion-type pair under the second
twisted adjoint action. -/
def modifiedTwistedPairStabilizer (i j : Fin 4) : Set (GA Q)ˣ :=
  stabilizes Q (modifiedTwistedAdjointAction Q) (jointPairSubmodule Q i j : Set (GA Q))

/-- Reversion-norm carrier for the reverse-fixed sector. Identifying this with
the paper's grade-one center carrier requires a further centralizer theorem. -/
def ReverseFixedNormCarrier : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈ centralizerSet Q
    {x | CliffordAlgebra.reverse x = x}}

/-- Reversion-norm carrier for the reverse-anti-fixed sector. Its identification
with the paper's quaternion-pair carrier requires a joint-type decomposition. -/
def ReverseAntiFixedNormCarrier : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈ centralizerSet Q
    {x | CliffordAlgebra.reverse x = -x}}

/-- Geometric `Γ^01` carrier: units whose ordinary adjoint action preserves the
reverse-fixed sector. -/
def Gamma01Carrier : Set (GA Q)ˣ :=
  stabilizes Q (adjointAction Q) {x | CliffordAlgebra.reverse x = x}

/-- Geometric `Γ^23` carrier: units whose ordinary adjoint action preserves the
reverse-anti-fixed sector. -/
def Gamma23Carrier : Set (GA Q)ˣ :=
  stabilizes Q (adjointAction Q) {x | CliffordAlgebra.reverse x = -x}

@[simp] theorem involute_reversion_commute (x : GA Q) :
    CliffordAlgebra.involute (CliffordAlgebra.reverse x) =
      CliffordAlgebra.reverse (CliffordAlgebra.involute x) :=
  (CliffordAlgebra.reverse_involute x).symm

@[simp] theorem reversionNorm_reverse_fixed (g : (GA Q)ˣ) :
    CliffordAlgebra.reverse (reversionNorm Q g) = reversionNorm Q g := by
  simp [reversionNorm, CliffordAlgebra.reverse.map_mul]

theorem adjointAction_mem_reverseFixed_iff_norm_commutes
    (g : (GA Q)ˣ) (x : GA Q) (hx : CliffordAlgebra.reverse x = x) :
    CliffordAlgebra.reverse (adjointAction Q g x) = adjointAction Q g x ↔
      reversionNorm Q g * x = x * reversionNorm Q g := by
  -- This local equivalence is the reverse-involution mechanism behind the
  -- paper's norm/centralizer characterization.  Its application to the
  -- four joint grade/reversion pieces requires the paper's sign bookkeeping.
  let a : GA Q := (g : GA Q)
  let ai : GA Q := ((g⁻¹ : (GA Q)ˣ) : GA Q)
  let r : GA Q := CliffordAlgebra.reverse a
  let ri : GA Q := CliffordAlgebra.reverse ai
  have hai : a * ai = 1 := by simp [a, ai]
  have hia : ai * a = 1 := by simp [a, ai]
  have hri_r : ri * r = 1 := by
    change CliffordAlgebra.reverse ai * CliffordAlgebra.reverse a = 1
    rw [← CliffordAlgebra.reverse.map_mul, hai]
    simp
  have hr_ri : r * ri = 1 := by
    change CliffordAlgebra.reverse a * CliffordAlgebra.reverse ai = 1
    rw [← CliffordAlgebra.reverse.map_mul, hia]
    simp
  have hrevAction : CliffordAlgebra.reverse (adjointAction Q g x) = ri * x * r := by
    dsimp [adjointAction, r, ri, a, ai]
    rw [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse.map_mul, hx]
    noncomm_ring
  constructor
  · intro h
    have heq : ri * x * r = a * x * ai := by
      rw [hrevAction] at h
      simpa [adjointAction, a, ai] using h
    have hEq : x * r * a = r * a * x := by
      calc
        x * r * a = (r * ri) * x * r * a := by simp [hr_ri]
        _ = r * (ri * x * r) * a := by noncomm_ring
        _ = r * (a * x * ai) * a := by rw [heq]
        _ = r * a * x := by noncomm_ring [hia]
    have hEq' : x * (r * a) = (r * a) * x := by
      calc
        x * (r * a) = x * r * a := by noncomm_ring
        _ = r * a * x := hEq
    change (r * a) * x = x * (r * a)
    exact hEq'.symm
  · intro h
    have hcentral : (r * a) * x = x * (r * a) := by
      simpa [reversionNorm, r, a] using h
    have heq : ri * x * r = a * x * ai := by
      calc
        ri * x * r = ri * (x * r * a) * ai := by noncomm_ring [hai]
        _ = ri * (r * a * x) * ai := by noncomm_ring [hcentral]
        _ = a * x * ai := by
          calc
            ri * (r * a * x) * ai = (ri * r) * a * x * ai := by noncomm_ring
            _ = 1 * a * x * ai := by rw [hri_r]
            _ = a * x * ai := by simp
    rw [hrevAction, heq]
    rfl

/-- The paper's ordinary stabilizer predicate on the reverse-fixed sector is
exactly a preimage of the corresponding norm centralizer. -/
theorem stabilizes_reverseFixed_iff_reversionNormCentralizes (g : (GA Q)ˣ) :
    g ∈ stabilizes Q (adjointAction Q) {x | CliffordAlgebra.reverse x = x} ↔
      reversionNorm Q g ∈ centralizerSet Q {x | CliffordAlgebra.reverse x = x} := by
  constructor
  · intro hg x hx
    exact (adjointAction_mem_reverseFixed_iff_norm_commutes Q g x hx).mp (hg x hx)
  · intro hg x hx
    exact (adjointAction_mem_reverseFixed_iff_norm_commutes Q g x hx).mpr
      (hg x hx)

/-- The ordinary adjoint action preserves the reverse-anti-fixed subspace exactly
when the reversion norm commutes with each element of that subspace. -/
theorem adjointAction_mem_reverseAntiFixed_iff_norm_commutes
    (g : (GA Q)ˣ) (x : GA Q) (hx : CliffordAlgebra.reverse x = -x) :
    CliffordAlgebra.reverse (adjointAction Q g x) = -adjointAction Q g x ↔
      reversionNorm Q g * x = x * reversionNorm Q g := by
  let a : GA Q := (g : GA Q)
  let ai : GA Q := ((g⁻¹ : (GA Q)ˣ) : GA Q)
  let r : GA Q := CliffordAlgebra.reverse a
  let ri : GA Q := CliffordAlgebra.reverse ai
  have hai : a * ai = 1 := by simp [a, ai]
  have hia : ai * a = 1 := by simp [a, ai]
  have hri_r : ri * r = 1 := by
    change CliffordAlgebra.reverse ai * CliffordAlgebra.reverse a = 1
    rw [← CliffordAlgebra.reverse.map_mul, hai]
    simp
  have hr_ri : r * ri = 1 := by
    change CliffordAlgebra.reverse a * CliffordAlgebra.reverse ai = 1
    rw [← CliffordAlgebra.reverse.map_mul, hia]
    simp
  have hrevAction : CliffordAlgebra.reverse (adjointAction Q g x) =
      -(ri * x * r) := by
    dsimp [adjointAction, r, ri, a, ai]
    rw [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse.map_mul, hx]
    noncomm_ring
  constructor
  · intro h
    have heq : ri * x * r = a * x * ai := by
      apply neg_injective
      rw [← hrevAction, h]
      simp [adjointAction, a, ai]
    have hEq : x * r * a = r * a * x := by
      calc
        x * r * a = (r * ri) * x * r * a := by simp [hr_ri]
        _ = r * (ri * x * r) * a := by noncomm_ring
        _ = r * (a * x * ai) * a := by rw [heq]
        _ = r * a * x := by noncomm_ring [hia]
    have hEq' : x * (r * a) = (r * a) * x := by
      calc
        x * (r * a) = x * r * a := by noncomm_ring
        _ = r * a * x := hEq
    change (r * a) * x = x * (r * a)
    exact hEq'.symm
  · intro h
    have hcentral : (r * a) * x = x * (r * a) := by
      simpa [reversionNorm, r, a] using h
    have heq : ri * x * r = a * x * ai := by
      calc
        ri * x * r = ri * (x * r * a) * ai := by noncomm_ring [hai]
        _ = ri * (r * a * x) * ai := by noncomm_ring [hcentral]
        _ = a * x * ai := by
          calc
            ri * (r * a * x) * ai = (ri * r) * a * x * ai := by noncomm_ring
            _ = 1 * a * x * ai := by rw [hri_r]
            _ = a * x * ai := by simp
    rw [hrevAction, heq]
    simp [adjointAction, a, ai]

/-- The grade-twisted adjoint action preserves reverse-fixed elements exactly
when the Clifford norm lies in their grade-twisted centralizer. -/
theorem gradeTwistedAdjoint_mem_reverseFixed_iff_norm_twistedCentralizes
    (g : (GA Q)ˣ) (x : GA Q) (hx : CliffordAlgebra.reverse x = x) :
    CliffordAlgebra.reverse (gradeTwistedAdjointAction Q g x) =
        gradeTwistedAdjointAction Q g x ↔
      CliffordAlgebra.involute (cliffordNorm Q g) * x =
        x * cliffordNorm Q g := by
  let a : GA Q := (g : GA Q)
  let ai : GA Q := ((g⁻¹ : (GA Q)ˣ) : GA Q)
  let r : GA Q := CliffordAlgebra.reverse a
  let ri : GA Q := CliffordAlgebra.reverse ai
  let hatA : GA Q := CliffordAlgebra.involute a
  let hatR : GA Q := CliffordAlgebra.involute r
  have hai : a * ai = 1 := by simp [a, ai]
  have hia : ai * a = 1 := by simp [a, ai]
  have hri_r : ri * r = 1 := by
    change CliffordAlgebra.reverse ai * CliffordAlgebra.reverse a = 1
    rw [← CliffordAlgebra.reverse.map_mul, hai]
    simp
  have hr_ri : r * ri = 1 := by
    change CliffordAlgebra.reverse a * CliffordAlgebra.reverse ai = 1
    rw [← CliffordAlgebra.reverse.map_mul, hia]
    simp
  have hrevAction : CliffordAlgebra.reverse (gradeTwistedAdjointAction Q g x) =
      ri * x * hatR := by
    dsimp [gradeTwistedAdjointAction, a, ai, r, ri, hatR]
    rw [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse.map_mul, hx,
      CliffordAlgebra.reverse_involute]
    noncomm_ring
  have hchi : CliffordAlgebra.involute (cliffordNorm Q g) =
      r * hatA ∧ cliffordNorm Q g = hatR * a := by
    constructor
    · change CliffordAlgebra.involute
        (CliffordAlgebra.involute (CliffordAlgebra.reverse a) * a) = r * hatA
      rw [map_mul, CliffordAlgebra.involute_involute]
    · rfl
  constructor
  · intro h
    have heq : ri * x * hatR = hatA * x * ai := by
      calc
        ri * x * hatR = CliffordAlgebra.reverse (gradeTwistedAdjointAction Q g x) :=
          hrevAction.symm
        _ = gradeTwistedAdjointAction Q g x := h
        _ = hatA * x * ai := rfl
    have hEq : x * hatR * a = r * hatA * x := by
      calc
        x * hatR * a = (r * ri) * x * hatR * a := by rw [hr_ri]; noncomm_ring
        _ = r * (ri * x * hatR) * a := by noncomm_ring
        _ = r * (hatA * x * ai) * a := by rw [heq]
        _ = r * hatA * x := by noncomm_ring [hia]
    rw [hchi.1, hchi.2]
    calc
      (r * hatA) * x = (x * hatR) * a := hEq.symm
      _ = x * (hatR * a) := by noncomm_ring
  · intro h
    rw [hchi.1, hchi.2] at h
    have h' : (r * hatA) * x = x * (hatR * a) := h
    have h'Assoc : r * hatA * x = x * hatR * a := by
      calc
        r * hatA * x = (r * hatA) * x := rfl
        _ = x * (hatR * a) := h'
        _ = x * hatR * a := by noncomm_ring
    have heq : ri * x * hatR = hatA * x * ai := by
      calc
        ri * x * hatR = ri * (x * hatR * a) * ai := by noncomm_ring [hai]
        _ = ri * (r * hatA * x) * ai := by rw [h'Assoc]
        _ = hatA * x * ai := by
          calc
            ri * (r * hatA * x) * ai = (ri * r) * hatA * x * ai := by noncomm_ring
            _ = 1 * hatA * x * ai := by rw [hri_r]
            _ = hatA * x * ai := by simp
    rw [hrevAction, heq]
    rfl

/-- Setwise form of the reverse-fixed Clifford-norm criterion for the
grade-twisted adjoint action. -/
theorem stabilizes_reverseFixed_iff_cliffordNorm_twistedCentralizes
    (g : (GA Q)ˣ) :
    g ∈ stabilizes Q (gradeTwistedAdjointAction Q)
      {x | CliffordAlgebra.reverse x = x} ↔
      cliffordNorm Q g ∈ twistedCentralizerSet Q
        {x | CliffordAlgebra.reverse x = x} := by
  constructor
  · intro hg x hx
    exact (gradeTwistedAdjoint_mem_reverseFixed_iff_norm_twistedCentralizes Q g x hx).mp
      (hg x hx)
  · intro hg x hx
    exact (gradeTwistedAdjoint_mem_reverseFixed_iff_norm_twistedCentralizes Q g x hx).mpr
      (hg x hx)

/-- Setwise form of the reverse-anti-fixed norm-centralizer characterization. -/
theorem stabilizes_reverseAntiFixed_iff_reversionNormCentralizes (g : (GA Q)ˣ) :
    g ∈ stabilizes Q (adjointAction Q)
      {x | CliffordAlgebra.reverse x = -x} ↔
      reversionNorm Q g ∈ centralizerSet Q {x | CliffordAlgebra.reverse x = -x} := by
  constructor
  · intro hg x hx
    exact (adjointAction_mem_reverseAntiFixed_iff_norm_commutes Q g x hx).mp (hg x hx)
  · intro hg x hx
    exact (adjointAction_mem_reverseAntiFixed_iff_norm_commutes Q g x hx).mpr
      (hg x hx)

/-- Action-level norm criterion for the reverse-fixed sector, valid for arbitrary
(possibly degenerate) quadratic forms over `ℝ`. Identifying the carrier with
the paper's `A^01` table entry requires the grade-centralizer decomposition. -/
theorem reverseFixedNormCarrier_eq_Gamma01Carrier :
    ReverseFixedNormCarrier Q = Gamma01Carrier Q := by
  ext g
  exact (stabilizes_reverseFixed_iff_reversionNormCentralizes Q g).symm

/-- Action-level norm criterion for the reverse-anti-fixed sector, valid for
arbitrary (possibly degenerate) quadratic forms over `ℝ`. Identifying this with
the paper's `A^23` entry requires the joint-type decomposition. -/
theorem reverseAntiFixedNormCarrier_eq_Gamma23Carrier :
    ReverseAntiFixedNormCarrier Q = Gamma23Carrier Q := by
  ext g
  exact (stabilizes_reverseAntiFixed_iff_reversionNormCentralizes Q g).symm

/-- The ordinary adjoint stabilizer of quaternion types 0 and 1 is exactly the
reverse-fixed geometric group, and hence its reversion-norm centralizer group.
This is a pair-level classification for arbitrary real quadratic forms. -/
theorem adjointPairStabilizer_01_eq_ReverseFixedNormCarrier :
    adjointPairStabilizer Q 0 1 = ReverseFixedNormCarrier Q := by
  ext g
  change (∀ x, x ∈ (jointPairSubmodule Q 0 1 : Set (GA Q)) →
      adjointAction Q g x ∈ (jointPairSubmodule Q 0 1 : Set (GA Q))) ↔
    g ∈ ReverseFixedNormCarrier Q
  rw [jointPair_01_eq_reverseFixed]
  exact stabilizes_reverseFixed_iff_reversionNormCentralizes Q g

/-- The first ordinary-adjoint classification in Theorem 4.1: the stabilizer
of the paper's joint sector pair `0,1` is exactly the `A^01` norm carrier. -/
theorem adjointPairStabilizer_01_eq_PaperA01 :
    adjointPairStabilizer Q 0 1 = PaperA01 Q := by
  calc
    adjointPairStabilizer Q 0 1 = ReverseFixedNormCarrier Q :=
      adjointPairStabilizer_01_eq_ReverseFixedNormCarrier Q
    _ = PaperA01 Q := by
      ext g
      change reversionNorm Q g ∈
          centralizerSet Q {x | CliffordAlgebra.reverse x = x} ↔
        reversionNorm Q g ∈ fixedGradeCentralizer Q 1
      rw [reverseFixedCentralizer_eq_fixedGradeCentralizer_one Q]

/-- The ordinary adjoint stabilizer of quaternion types 2 and 3 is exactly the
reverse-anti-fixed geometric group, and hence its reversion-norm centralizer
group, for arbitrary real quadratic forms. -/
theorem adjointPairStabilizer_23_eq_ReverseAntiFixedNormCarrier :
    adjointPairStabilizer Q 2 3 = ReverseAntiFixedNormCarrier Q := by
  ext g
  change (∀ x, x ∈ (jointPairSubmodule Q 2 3 : Set (GA Q)) →
      adjointAction Q g x ∈ (jointPairSubmodule Q 2 3 : Set (GA Q))) ↔
    g ∈ ReverseAntiFixedNormCarrier Q
  rw [jointPair_23_eq_reverseAntiFixed]
  exact stabilizes_reverseAntiFixed_iff_reversionNormCentralizes Q g

end InfoGeometry.Clifford.GeneralizedDegenerateLipschitzArchetypes
