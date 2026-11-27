/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.Tactic
import InfoGeometry.Clifford.GradedGraceContraction
import InfoGeometry.Clifford.LipschitzWittRieszPrimary

set_option maxHeartbeats 600000

/-!
# Archetypes for generalized degenerate Clifford and Lipschitz groups

This file formalizes the common algebraic input of Filimoshina--Shirokov,
arXiv:2505.07106v2, without imposing nondegeneracy on the quadratic form.
The paper's signature-specific centralizer tables, remaining group
classifications, and Lie-algebra dimension tables are not asserted here.

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

/-- Exact coordinate formula for the diagonal `(p,q,r)` quadratic form. -/
theorem degenerateSignatureForm_apply (p q r : ℕ)
    (x : Fin (p + q + r) → ℝ) :
    degenerateSignatureForm p q r x =
      ∑ i : Fin (p + q + r), degenerateSignatureWeight p q r i • (x i * x i) := by
  rw [degenerateSignatureForm, QuadraticMap.weightedSumSquares_apply]

/-- The quadratic value depends only on the positive and negative coordinates;
changing the radical coordinates does not change it. -/
theorem degenerateSignatureForm_eq_of_nonradical_coords_eq (p q r : ℕ)
    (x y : Fin (p + q + r) → ℝ)
    (hxy : ∀ i, i.val < p + q → x i = y i) :
    degenerateSignatureForm p q r x = degenerateSignatureForm p q r y := by
  rw [degenerateSignatureForm_apply, degenerateSignatureForm_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i.val < p + q
  · rw [hxy i h]
  · have hweight : degenerateSignatureWeight p q r i = 0 := by
      simp [degenerateSignatureWeight, Nat.not_lt.mpr (by omega : p ≤ i.val), h]
    simp [hweight]

/-- The signature `(0,0,r)` has identically zero quadratic form. -/
theorem degenerateSignatureForm_radicalOnly_eq_zero (r : ℕ) :
    degenerateSignatureForm 0 0 r = 0 := by
  ext x
  rw [degenerateSignatureForm_apply]
  simp [degenerateSignatureWeight]

/-- In the radical-only signature, every vector generator is square-zero. -/
theorem radicalOnly_generator_sq_zero (r : ℕ) (v : Fin (0 + 0 + r) → ℝ) :
    (CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) v) ^ 2 = 0 := by
  rw [pow_two, CliffordAlgebra.ι_sq_scalar,
    degenerateSignatureForm_radicalOnly_eq_zero]
  simp

/-- Generators in the radical-only Clifford algebra anticommute, as in the
exterior algebra presentation. -/
theorem radicalOnly_generators_anticommute (r : ℕ)
    (v w : Fin (0 + 0 + r) → ℝ) :
    CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) v *
        CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) w +
      CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) w *
        CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) v = 0 := by
  have hv := radicalOnly_generator_sq_zero r v
  have hw := radicalOnly_generator_sq_zero r w
  have hvw := radicalOnly_generator_sq_zero r (v + w)
  rw [map_add] at hvw
  rw [pow_two] at hvw hv hw
  calc
    CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) v *
          CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) w +
        CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) w *
          CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) v =
        (CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) v +
          CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) w) *
            (CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) v +
              CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) w) -
          CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) v *
            CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) v -
          CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) w *
            CliffordAlgebra.ι (degenerateSignatureForm 0 0 r) w := by noncomm_ring
    _ = 0 := by rw [hvw, hv, hw]; noncomm_ring

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

/-- Clifford square table for coordinate generators: the square is the
signature weight times the unit, covering positive, negative, and radical
coordinates in one statement. -/
theorem signatureCoordinate_generator_sq (p q r : ℕ)
    (i : Fin (p + q + r)) :
    (CliffordAlgebra.ι (degenerateSignatureForm p q r)
      (radicalCoordinate p q r i)) ^ 2 =
      degenerateSignatureWeight p q r i •
        (1 : CliffordAlgebra (degenerateSignatureForm p q r)) := by
  rw [pow_two, CliffordAlgebra.ι_sq_scalar, signatureCoordinate_form_eq_weight]
  rw [← Algebra.algebraMap_eq_smul_one]

/-- Positive signature basis generators square to `+1`. -/
theorem positiveSignatureCoordinate_generator_sq (p q r : ℕ)
    (i : Fin (p + q + r)) (hi : i.val < p) :
    (CliffordAlgebra.ι (degenerateSignatureForm p q r)
      (radicalCoordinate p q r i)) ^ 2 = 1 := by
  rw [signatureCoordinate_generator_sq]
  simp [degenerateSignatureWeight, hi]

/-- Negative signature basis generators square to `-1`. -/
theorem negativeSignatureCoordinate_generator_sq (p q r : ℕ)
    (i : Fin (p + q + r)) (hi₁ : p ≤ i.val) (hi₂ : i.val < p + q) :
    (CliffordAlgebra.ι (degenerateSignatureForm p q r)
      (radicalCoordinate p q r i)) ^ 2 = -1 := by
  rw [signatureCoordinate_generator_sq]
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

/-- Quaternion types `0,3` are exactly the fixed subspace of Clifford
conjugation `star = reverse ∘ involute`. The paper's `B^03` table uses the
type-three centralizer; identifying it with this pair centralizer is a
separate bridge. -/
theorem jointPair_03_eq_starFixed :
    (jointPairSubmodule Q 0 3 : Set (GA Q)) = {x | star x = x} := by
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, hv, rfl⟩
    have hu' := (mem_jointType_iff Q 0 u).mp hu
    have hv' := (mem_jointType_iff Q 3 v).mp hv
    change CliffordAlgebra.reverse (CliffordAlgebra.involute (u + v)) = u + v
    simp [map_add, hu'.1, hv'.1, hu'.2, hv'.2,
      gradeSign, reversionSign]
  · intro hx
    change CliffordAlgebra.reverse (CliffordAlgebra.involute x) = x at hx
    have hx' : CliffordAlgebra.reverse (CliffordAlgebra.involute x) = x := by
      simpa only [CliffordAlgebra.star_def] using hx
    have hxR : CliffordAlgebra.reverse x = CliffordAlgebra.involute x := by
      have h := congrArg CliffordAlgebra.reverse hx'
      simpa using h.symm
    let u := gradeEvenComponent Q x
    let v := gradeOddComponent Q x
    have hu : u ∈ jointTypeSubmodule Q 0 := by
      rw [mem_jointType_iff]
      constructor
      · simp [u, gradeEvenComponent, gradeSign, map_add]
        abel
      · simp [u, gradeEvenComponent, reversionSign, map_add,
          CliffordAlgebra.reverse_involute, hxR]
        abel
    have hv : v ∈ jointTypeSubmodule Q 3 := by
      rw [mem_jointType_iff]
      constructor
      · simp [v, gradeOddComponent, gradeSign, map_sub]
        module
      · simp [v, gradeOddComponent, reversionSign, map_sub,
          CliffordAlgebra.reverse_involute, hxR]
        module
    have huv : u + v = x := by
      simp [u, v, gradeEvenComponent, gradeOddComponent]
      norm_num
      module
    exact Submodule.mem_sup.mpr ⟨u, hu, v, hv, huv⟩

/-- Quaternion types `1,2` together are the Clifford-conjugation anti-fixed
subspace. This is the carrier underlying the ordinary-adjoint `B^12` norm
criterion. -/
theorem jointPair_12_eq_starAntiFixed :
    (jointPairSubmodule Q 1 2 : Set (GA Q)) = {x | star x = -x} := by
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, hv, rfl⟩
    have hu' := (mem_jointType_iff Q 1 u).mp hu
    have hv' := (mem_jointType_iff Q 2 v).mp hv
    change star (u + v) = -(u + v)
    simp [CliffordAlgebra.star_def, hu'.1, hu'.2, hv'.1, hv'.2,
      gradeSign, reversionSign]
    abel
  · intro hx
    change star x = -x at hx
    have hx' : CliffordAlgebra.reverse (CliffordAlgebra.involute x) = -x := by
      simpa only [CliffordAlgebra.star_def] using hx
    have hxR : CliffordAlgebra.reverse x = -CliffordAlgebra.involute x := by
      have h := congrArg CliffordAlgebra.reverse hx'
      have h' : CliffordAlgebra.involute x = -CliffordAlgebra.reverse x := by
        simpa using h
      rw [h']
      simp
    let u := gradeEvenComponent Q x
    let v := gradeOddComponent Q x
    have hu : u ∈ jointTypeSubmodule Q 2 := by
      rw [mem_jointType_iff]
      constructor
      · simp [u, gradeEvenComponent, gradeSign, map_add]
        abel
      · simp [u, gradeEvenComponent, reversionSign, map_add,
          CliffordAlgebra.reverse_involute, hxR]
        module
    have hv : v ∈ jointTypeSubmodule Q 1 := by
      rw [mem_jointType_iff]
      constructor
      · simp [v, gradeOddComponent, gradeSign, map_sub]
        module
      · simp [v, gradeOddComponent, reversionSign, map_sub,
          CliffordAlgebra.reverse_involute, hxR]
        module
    have huv : u + v = x := by
      simp [u, v, gradeEvenComponent, gradeOddComponent]
      module
    exact Submodule.mem_sup.mpr ⟨v, hv, u, hu, (by simpa [add_comm] using huv)⟩

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

/-- Every homogeneous Clifford grade has the binomial rank determined only by
the dimension of the quadratic-form carrier. In particular, degenerating the
form changes multiplication but not the dimensions of its grade subspaces. -/
theorem fixedGradeCarrier_finrank_eq_choose [FiniteDimensional ℝ M] (k : ℕ) :
    Module.finrank ℝ (fixedGradeCarrier Q k) =
      (Module.finrank ℝ M).choose k := by
  classical
  let e := CliffordAlgebra.equivExterior Q
  have hRange :
      LinearMap.range
          (InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q k) =
        Submodule.map e.symm.toLinearMap
          (LinearMap.range
            (InfoGeometry.Clifford.GradedGraceContraction.exteriorGradeProj ℝ M k)) := by
    change LinearMap.range
        ((e.symm.toLinearMap.comp
          (InfoGeometry.Clifford.GradedGraceContraction.exteriorGradeProj ℝ M k)).comp
            e.toLinearMap) = _
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      apply Submodule.mem_map.mpr
      refine ⟨InfoGeometry.Clifford.GradedGraceContraction.exteriorGradeProj ℝ M k
        (e y), ⟨e y, rfl⟩, rfl⟩
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨z, hz, hxz⟩
      rcases hz with ⟨y, rfl⟩
      refine ⟨e.symm y, ?_⟩
      change e.symm
        (InfoGeometry.Clifford.GradedGraceContraction.exteriorGradeProj ℝ M k
          (e (e.symm y))) = x
      rw [e.apply_symm_apply]
      exact hxz
  have hExteriorRange :
      LinearMap.range
          (InfoGeometry.Clifford.GradedGraceContraction.exteriorGradeProj ℝ M k) =
        (⋀[ℝ]^k M) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact InfoGeometry.Clifford.GradedGraceContraction.exteriorGradeProj_mem ℝ M k _
    · intro hx
      exact ⟨x,
        InfoGeometry.Clifford.GradedGraceContraction.exteriorGradeProj_of_mem hx⟩
  rw [fixedGradeCarrier, InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeSubmodule,
    hRange, hExteriorRange, e.symm.finrank_map_eq,
    exteriorPower.finrank_eq ℝ M]

/-- The full Clifford carrier has dimension `2^n` for every real quadratic
form, including degenerate forms. The exterior-algebra basis makes explicit
that this dimension depends on the vector-space dimension, not the signature.
-/
theorem clifford_finrank_eq_two_pow [FiniteDimensional ℝ M] :
    Module.finrank ℝ (GA Q) = 2 ^ Module.finrank ℝ M := by
  classical
  let b := Module.finBasis ℝ M
  let extBasis : Module.Basis (Finset (Fin (Module.finrank ℝ M))) ℝ
      (ExteriorAlgebra ℝ M) := b.ExteriorAlgebra
  rw [LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior Q),
    Module.finrank_eq_card_basis extBasis]
  simp [Fintype.card_finset, Fintype.card_fin]

/-- Full carrier and homogeneous-grade dimension table for every diagonal
signature `(p,q,r)`. These are Clifford-algebra vector-space dimensions, not
the dimensions of the paper's generalized groups or their Lie algebras. -/
theorem degenerateSignature_grade_dimension_table (p q r : ℕ) :
    Module.finrank ℝ (DegenerateClifford p q r) = 2 ^ (p + q + r) ∧
    ∀ k : ℕ,
      Module.finrank ℝ
        (fixedGradeCarrier (degenerateSignatureForm p q r) k) =
        Nat.choose (p + q + r) k := by
  constructor
  · rw [clifford_finrank_eq_two_pow]
    simp
  · intro k
    rw [fixedGradeCarrier_finrank_eq_choose]
    simp

/-- Every homogeneous grade above the dimension of the signature carrier
vanishes, uniformly in the positive, negative, and radical dimensions. This
turns the all-signature grade-rank formula into a reusable carrier identity
for the degenerate group reductions. -/
theorem degenerateSignature_fixedGradeCarrier_eq_bot_of_gt_dimension
    (p q r k : ℕ) (hk : p + q + r < k) :
    fixedGradeCarrier (degenerateSignatureForm p q r) k = ⊥ := by
  rw [fixedGradeCarrier]
  have hproj :
      InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj
          (degenerateSignatureForm p q r) k = 0 := by
    apply InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj_eq_zero_of_gt_finrank
    simpa using hk
  change LinearMap.range
      (InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj
        (degenerateSignatureForm p q r) k) = ⊥
  rw [hproj]
  exact LinearMap.range_zero

/-- Homogeneous grades above the vector-space dimension vanish for every
finite-dimensional real quadratic form, without requiring a diagonal
signature presentation. -/
theorem fixedGradeCarrier_eq_bot_of_gt_finrank [FiniteDimensional ℝ M]
    (k : ℕ) (hk : Module.finrank ℝ M < k) :
    fixedGradeCarrier Q k = ⊥ := by
  rw [fixedGradeCarrier]
  have hproj :
      InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q k = 0 := by
    apply InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj_eq_zero_of_gt_finrank
    exact hk
  change LinearMap.range
      (InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q k) = ⊥
  rw [hproj]
  exact LinearMap.range_zero

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

/-- Grade-twisted centralizer of a sum of homogeneous grade carriers. -/
def homogeneousGradePairTwistedCentralizer (k l : ℕ) : Set (GA Q) :=
  twistedCentralizerSet Q (homogeneousGradePairCarrier Q k l : Set (GA Q))

/-- Twisted centralization of a direct sum is equivalent to twisted
centralization of each summand. -/
theorem homogeneousGradePairTwistedCentralizer_eq_inter (k l : ℕ) :
    homogeneousGradePairTwistedCentralizer Q k l =
      fixedGradeTwistedCentralizer Q k ∩ fixedGradeTwistedCentralizer Q l := by
  ext x
  simp only [homogeneousGradePairTwistedCentralizer, homogeneousGradePairCarrier,
    fixedGradeTwistedCentralizer, twistedCentralizerSet, Set.mem_inter_iff]
  constructor
  · intro h
    constructor
    · intro y hy
      exact h y (Submodule.mem_sup_left hy)
    · intro y hy
      exact h y (Submodule.mem_sup_right hy)
  · rintro ⟨hk, hl⟩ y hy
    rcases Submodule.mem_sup.mp hy with ⟨a, ha, b, hb, hab⟩
    rw [← hab, mul_add, add_mul, hk a ha, hl b hb]

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

/-- Every homogeneous grade-one element belongs to quaternion type one. -/
theorem fixedGradeCarrier_one_subset_jointType_one :
    (fixedGradeCarrier Q 1 : Set (GA Q)) ⊆ jointTypeSubmodule Q 1 := by
  intro x hx
  have hxProj : InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q 1 x = x :=
    (InfoGeometry.Clifford.GradedGraceContraction.mem_cliffordGradeSubmodule_iff 1 x).mp hx
  have hrev : CliffordAlgebra.reverse x = x :=
    fixedGradeCarrier_one_subset_reverseFixed Q hx
  have hstar : star x = -x := by
    calc
      star x = star
          (InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q 1 x) :=
            congrArg star hxProj.symm
      _ = (-1 : ℝ) ^ (1 * (1 + 1) / 2) •
          InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q 1 x :=
        InfoGeometry.Clifford.LipschitzWittRieszPrimary.cliffordGradeProj_star Q 1 x
      _ = -x := by norm_num [hxProj]
  have hinv : CliffordAlgebra.involute x = -x := by
    calc
      CliffordAlgebra.involute x = CliffordAlgebra.reverse (star x) := by
        simp only [CliffordAlgebra.star_def, CliffordAlgebra.reverse_involute,
          CliffordAlgebra.reverse_reverse]
      _ = CliffordAlgebra.reverse (-x) := congrArg CliffordAlgebra.reverse hstar
      _ = -x := by rw [map_neg, hrev]
  exact (mem_jointType_iff Q 1 x).mpr
    ⟨by simpa [gradeSign] using hinv, by simpa [reversionSign] using hrev⟩

/-- Homogeneous grade two is contained in quaternion type two. This is the
easy carrier direction in the paper's grade/quaternion centralizer bridge. -/
theorem fixedGradeCarrier_two_subset_jointType_two :
    (fixedGradeCarrier Q 2 : Set (GA Q)) ⊆ jointTypeSubmodule Q 2 := by
  intro x hx
  have hxProj : InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q 2 x = x :=
    (InfoGeometry.Clifford.GradedGraceContraction.mem_cliffordGradeSubmodule_iff 2 x).mp hx
  have hrev : CliffordAlgebra.reverse x = -x := by
    calc
      CliffordAlgebra.reverse x = CliffordAlgebra.reverse
          (InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q 2 x) :=
            congrArg CliffordAlgebra.reverse hxProj.symm
      _ = (-1 : ℝ) ^ (2 * (2 - 1) / 2) •
          InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q 2 x :=
        InfoGeometry.Clifford.LipschitzWittRieszPrimary.cliffordGradeProj_reverse Q 2 x
      _ = -x := by norm_num [hxProj]
  have hstar : star x = -x := by
    calc
      star x = star
          (InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q 2 x) :=
            congrArg star hxProj.symm
      _ = (-1 : ℝ) ^ (2 * (2 + 1) / 2) •
          InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q 2 x :=
        InfoGeometry.Clifford.LipschitzWittRieszPrimary.cliffordGradeProj_star Q 2 x
      _ = -x := by norm_num [hxProj]
  have hinv : CliffordAlgebra.involute x = x := by
    calc
      CliffordAlgebra.involute x = CliffordAlgebra.reverse (star x) := by
        simp only [CliffordAlgebra.star_def, CliffordAlgebra.reverse_involute,
          CliffordAlgebra.reverse_reverse]
      _ = CliffordAlgebra.reverse (-x) := congrArg CliffordAlgebra.reverse hstar
      _ = x := by rw [map_neg, hrev]; simp
  exact (mem_jointType_iff Q 2 x).mpr
    ⟨by simpa [gradeSign] using hinv, by simpa [reversionSign] using hrev⟩

/-- Homogeneous grade three is contained in quaternion type three. This is
the easy carrier direction in the paper's grade/quaternion centralizer bridge. -/
theorem fixedGradeCarrier_three_subset_jointType_three :
    (fixedGradeCarrier Q 3 : Set (GA Q)) ⊆ jointTypeSubmodule Q 3 := by
  intro x hx
  have hxProj : InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q 3 x = x :=
    (InfoGeometry.Clifford.GradedGraceContraction.mem_cliffordGradeSubmodule_iff 3 x).mp hx
  have hrev : CliffordAlgebra.reverse x = -x := by
    calc
      CliffordAlgebra.reverse x = CliffordAlgebra.reverse
          (InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q 3 x) :=
            congrArg CliffordAlgebra.reverse hxProj.symm
      _ = (-1 : ℝ) ^ (3 * (3 - 1) / 2) •
          InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q 3 x :=
        InfoGeometry.Clifford.LipschitzWittRieszPrimary.cliffordGradeProj_reverse Q 3 x
      _ = -x := by norm_num [hxProj]
  have hstar : star x = x := by
    calc
      star x = star
          (InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q 3 x) :=
            congrArg star hxProj.symm
      _ = (-1 : ℝ) ^ (3 * (3 + 1) / 2) •
          InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj Q 3 x :=
        InfoGeometry.Clifford.LipschitzWittRieszPrimary.cliffordGradeProj_star Q 3 x
      _ = x := by norm_num [hxProj]
  have hinv : CliffordAlgebra.involute x = -x := by
    calc
      CliffordAlgebra.involute x = CliffordAlgebra.reverse (star x) := by
        simp only [CliffordAlgebra.star_def, CliffordAlgebra.reverse_involute,
          CliffordAlgebra.reverse_reverse]
      _ = CliffordAlgebra.reverse x := by rw [hstar]
      _ = -x := hrev
  exact (mem_jointType_iff Q 3 x).mpr
    ⟨by simpa [gradeSign] using hinv, by simpa [reversionSign] using hrev⟩

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

/-- The ordinary centralizers of homogeneous grade one and quaternion type one
coincide. Grade one is contained in joint type one, while its centralizer is
already the center of the full Clifford algebra. This is the grade-one
ordinary-centralizer instance of the paper's grade/type comparison. -/
theorem quaternionTypeCentralizer_one_eq_fixedGradeCentralizer_one :
    quaternionTypeCentralizer Q 1 = fixedGradeCentralizer Q 1 := by
  ext a
  constructor
  · intro ha x hx
    have hAll : a ∈ centralizerSet Q Set.univ := by
      rw [← fixedGradeCentralizer_one_eq_centralizer_univ Q]
      intro y hy
      exact ha y (fixedGradeCarrier_one_subset_jointType_one Q hy)
    exact hAll x (Set.mem_univ x)
  · intro ha x hx
    have hAll : a ∈ centralizerSet Q Set.univ := by
      rw [← fixedGradeCentralizer_one_eq_centralizer_univ Q]
      exact ha
    exact hAll x (Set.mem_univ x)

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

/-- Twisted centralization of a direct sum of joint types is equivalent to
twisted centralization of each joint type. -/
theorem quaternionPairTwistedCentralizer_eq_inter (i j : Fin 4) :
    quaternionPairTwistedCentralizer Q i j =
      quaternionTypeTwistedCentralizer Q i ∩ quaternionTypeTwistedCentralizer Q j := by
  ext x
  simp only [quaternionPairTwistedCentralizer, quaternionTypeTwistedCentralizer,
    jointPairSubmodule, twistedCentralizerSet, Set.mem_inter_iff]
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

/-- The centralizer of joint types `1,2` is the center, hence the grade-one
centralizer. The grade-one carrier is contained in type one. -/
theorem quaternionPairCentralizer_12_eq_gradeOne :
    quaternionPairCentralizer Q 1 2 = fixedGradeCentralizer Q 1 := by
  ext a
  constructor
  · intro ha y hy
    exact ha y (Submodule.mem_sup_left
      (fixedGradeCarrier_one_subset_jointType_one Q hy))
  · intro ha y hy
    have hcenter : a ∈ centralizerSet Q Set.univ := by
      rw [← fixedGradeCentralizer_one_eq_centralizer_univ Q]
      exact ha
    exact hcenter y (Set.mem_univ y)

/-- Norm-table carrier `A^01`: reversion norm in the centralizer of grade one. -/
def PaperA01 : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈ fixedGradeCentralizer Q 1}

/-- Reversion-norm carrier of the joint-type `2,3` centralizer used by the
separate quaternion-eigenspace action lane. This is not the paper's `A^{23}`
carrier, whose indices denote homogeneous grades. -/
def JointTypeA23NormCarrier : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈ quaternionPairCentralizer Q 2 3}

/-- Paper's `A^{23}` carrier: the reversion norm centralizes both homogeneous
grade-two and homogeneous grade-three subspaces. -/
def PaperA23 : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈
    fixedGradeCentralizer Q 2 ∩ fixedGradeCentralizer Q 3}

/-- Norm-table carrier `B^12`: Clifford norm in the centralizer of grade one. -/
def PaperB12 : Set (GA Q)ˣ :=
  {g | cliffordNorm Q g ∈ fixedGradeCentralizer Q 1}

/-- The paper's `Cl⁽⁰⁾` carrier: the full even-parity subspace. This is
distinct from the homogeneous scalar-grade carrier `Cl⁰`. -/
def evenCarrier : Set (GA Q) :=
  {x | CliffordAlgebra.involute x = x}

/-- The grade-twisted centralizer of a set containing `1` forces its element
to be grade-involution fixed. For the Clifford-star-fixed sector, the twisted
centralizer is therefore exactly the even part intersected with its ordinary
centralizer. This is a structural reduction; identifying the latter
centralizer with the paper's grade-three centralizer is a further theorem. -/
theorem twistedCentralizer_starFixed_eq_even_inter_centralizer_starFixed :
    twistedCentralizerSet Q {x | star x = x} =
      evenCarrier Q ∩ centralizerSet Q {x | star x = x} := by
  ext a
  constructor
  · intro ha
    have hEven : CliffordAlgebra.involute a = a := by
      have h := ha 1 (by simp)
      simpa using h
    refine ⟨hEven, ?_⟩
    intro x hx
    simpa [hEven] using ha x hx
  · rintro ⟨hEven, ha⟩ x hx
    calc
      CliffordAlgebra.involute a * x = a * x := by rw [hEven]
      _ = x * a := ha x hx

/-- The paper's parity-even notation is exactly grade-involution fixedness. -/
theorem mem_evenCarrier_iff (x : GA Q) :
    x ∈ evenCarrier Q ↔ x ∈ CliffordAlgebra.evenOdd Q 0 := by
  constructor
  · intro hx
    rcases InfoGeometry.Clifford.LipschitzWittRieszPrimary.clifford_evenOdd_canonical_decomposition
        Q x with ⟨he, ho, hsum⟩
    have ho0 : InfoGeometry.Clifford.LipschitzWittRieszPrimary.cliffordOddPart Q x = 0 := by
      dsimp [InfoGeometry.Clifford.LipschitzWittRieszPrimary.cliffordOddPart]
      rw [hx]
      simp
    rw [← hsum, ho0, add_zero]
    exact he
  · exact CliffordAlgebra.involute_eq_of_mem_even

/-- Clifford-norm carrier of the joint-type-three centralizer. Kept separate
from the paper's `B^{03}`, which uses the homogeneous grade-three centralizer. -/
def JointTypeB03NormCarrier : Set (GA Q)ˣ :=
  {g | cliffordNorm Q g ∈ quaternionTypeCentralizer Q 3}

/-- Paper's `B^{03}` carrier: the Clifford norm centralizes the homogeneous
grade-three subspace. -/
def PaperB03 : Set (GA Q)ˣ :=
  {g | cliffordNorm Q g ∈ fixedGradeCentralizer Q 3}

/-- The paper's homogeneous-grade norm carrier `B^{03}` is the full unit group
whenever the underlying finite-dimensional vector space has dimension below
three: its grade-three test space is zero. This is a carrier classification;
it makes no claim about the separate joint-type stabilizer. -/
theorem PaperB03_eq_univ_of_finrank_lt_three [FiniteDimensional ℝ M]
    (hM : Module.finrank ℝ M < 3) : PaperB03 Q = Set.univ := by
  have hgrade : fixedGradeCarrier Q 3 = ⊥ :=
    fixedGradeCarrier_eq_bot_of_gt_finrank Q 3 hM
  ext g
  simp [PaperB03, fixedGradeCentralizer, centralizerSet, hgrade]

/-- A norm centralizing the full joint-type `2⊕3` carrier centralizes its
homogeneous-grade-two and grade-three subspaces. The reverse inclusion is the
nontrivial grade/quaternion centralizer identity from paper Lemma 3.2. -/
theorem JointTypeA23NormCarrier_subset_PaperA23 :
    JointTypeA23NormCarrier Q ⊆ PaperA23 Q := by
  intro g hg
  change reversionNorm Q g ∈ quaternionPairCentralizer Q 2 3 at hg
  constructor
  · intro x hx
    exact hg x (Submodule.mem_sup_left
      (fixedGradeCarrier_two_subset_jointType_two Q hx))
  · intro x hx
    exact hg x (Submodule.mem_sup_right
      (fixedGradeCarrier_three_subset_jointType_three Q hx))

/-- A Clifford norm centralizing joint type three centralizes homogeneous
grade three. The converse requires paper Lemma 3.2. -/
theorem JointTypeB03NormCarrier_subset_PaperB03 :
    JointTypeB03NormCarrier Q ⊆ PaperB03 Q := by
  intro g hg x hx
  exact hg x (fixedGradeCarrier_three_subset_jointType_three Q hx)

/-- Checked norm-table carrier `Ǎ^12`. -/
def PaperACheck12 : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈
    fixedGradeTwistedCentralizer Q 1 ∩ fixedGradeTwistedCentralizer Q 2}

/-- Checked norm-table carrier `Ǎ^03`. -/
def PaperACheck03 : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈
    fixedGradeCentralizer Q 3 ∩ evenCarrier Q}

/-- Reversion preserves the parity-even sector. Consequently the reversion
norm of any even unit is even, independently of the quadratic form. -/
theorem reversionNorm_mem_evenCarrier_of_even (g : (GA Q)ˣ)
    (hg : CliffordAlgebra.involute (g : GA Q) = (g : GA Q)) :
    reversionNorm Q g ∈ evenCarrier Q := by
  change CliffordAlgebra.involute
      (CliffordAlgebra.reverse (g : GA Q) * (g : GA Q)) = _
  have hRev : CliffordAlgebra.involute (CliffordAlgebra.reverse (g : GA Q)) =
      CliffordAlgebra.reverse (g : GA Q) := by
    rw [← CliffordAlgebra.reverse_involute, hg]
  rw [map_mul, hRev, hg]
  rfl

/-- Checked norm-table carrier `B̌^01`. -/
def PaperBCheck01 : Set (GA Q)ˣ :=
  {g | cliffordNorm Q g ∈
    fixedGradeCentralizer Q 1 ∩ evenCarrier Q}

/-- The grade-twisted centralizer of the reverse-fixed sector is the ordinary
grade-one centralizer restricted to even elements. The scalar test forces
grade-involution fixedness; on even elements the twisted equation is ordinary
commutation. -/
theorem reverseFixedTwistedCentralizer_eq_gradeOne_even :
    twistedCentralizerSet Q {x | CliffordAlgebra.reverse x = x} =
      fixedGradeCentralizer Q 1 ∩ evenCarrier Q := by
  ext a
  constructor
  · intro ha
    have hEven : CliffordAlgebra.involute a = a := by
      have h := ha 1 (by simp)
      simpa using h
    refine ⟨?_, hEven⟩
    intro v hv
    have hvRev : CliffordAlgebra.reverse v = v :=
      fixedGradeCarrier_one_subset_reverseFixed Q hv
    simpa [hEven] using ha v hvRev
  · rintro ⟨ha, hEven⟩ x hx
    have hcenter : a ∈ centralizerSet Q Set.univ := by
      rw [← fixedGradeCentralizer_one_eq_centralizer_univ Q]
      exact ha
    calc
      CliffordAlgebra.involute a * x = a * x := by rw [hEven]
      _ = x * a := hcenter x (Set.mem_univ x)

/-- Checked norm-table carrier `B̌^23`. -/
def PaperBCheck23 : Set (GA Q)ˣ :=
  {g | cliffordNorm Q g ∈
    fixedGradeTwistedCentralizer Q 2 ∩ fixedGradeTwistedCentralizer Q 3}

/-- Table 1's `B̌^{23}` norm condition is equivalently twisted centralization
of the direct sum of homogeneous grades two and three. -/
theorem PaperBCheck23_eq_homogeneousGradePairTwistedCentralizer_preimage :
    PaperBCheck23 Q =
      {g | cliffordNorm Q g ∈ homogeneousGradePairTwistedCentralizer Q 2 3} := by
  ext g
  change cliffordNorm Q g ∈
      fixedGradeTwistedCentralizer Q 2 ∩ fixedGradeTwistedCentralizer Q 3 ↔
    cliffordNorm Q g ∈ homogeneousGradePairTwistedCentralizer Q 2 3
  rw [← homogeneousGradePairTwistedCentralizer_eq_inter Q 2 3]

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

/-- The inclusion `A^{01} ⊆ A^{23}` from Theorem 4.1.  The grade-one
centralizer is the center of the Clifford algebra, so its reversion norm
centralizes both grade-two and grade-three carriers. -/
theorem PaperA01_subset_PaperA23 : PaperA01 Q ⊆ PaperA23 Q := by
  intro g hg
  change reversionNorm Q g ∈ fixedGradeCentralizer Q 1 at hg
  have hcenter : reversionNorm Q g ∈ centralizerSet Q Set.univ := by
    rw [← fixedGradeCentralizer_one_eq_centralizer_univ Q]
    exact hg
  constructor <;> intro x hx
  · exact hcenter x (Set.mem_univ x)
  · exact hcenter x (Set.mem_univ x)

/-- The inclusion `B^{12} ⊆ B^{03}` from Theorem 4.1. A Clifford norm
centralizing homogeneous grade one is central, hence centralizes homogeneous
grade three. -/
theorem PaperB12_subset_PaperB03 : PaperB12 Q ⊆ PaperB03 Q := by
  intro g hg
  change cliffordNorm Q g ∈ fixedGradeCentralizer Q 1 at hg
  have hcenter : cliffordNorm Q g ∈ centralizerSet Q Set.univ := by
    rw [← fixedGradeCentralizer_one_eq_centralizer_univ Q]
    exact hg
  intro x hx
  exact hcenter x (Set.mem_univ x)

/-- The checked-group inclusion `B̌^{01} ⊆ B̌^{23}` from Theorem 4.2.
The `B̌^{01}` norm is even and central (commuting with grade one is central
in the Clifford algebra), hence lies in both grade-twisted centralizers. -/
theorem PaperBCheck01_subset_PaperBCheck23 :
    PaperBCheck01 Q ⊆ PaperBCheck23 Q := by
  intro g hg
  change cliffordNorm Q g ∈
    fixedGradeCentralizer Q 1 ∩ evenCarrier Q at hg
  rcases hg with ⟨hgradeOne, heven⟩
  have hcenter : cliffordNorm Q g ∈ centralizerSet Q Set.univ := by
    rw [← fixedGradeCentralizer_one_eq_centralizer_univ Q]
    exact hgradeOne
  change cliffordNorm Q g ∈
    fixedGradeTwistedCentralizer Q 2 ∩ fixedGradeTwistedCentralizer Q 3
  constructor
  · intro x hx
    calc
      CliffordAlgebra.involute (cliffordNorm Q g) * x = cliffordNorm Q g * x := by
        rw [heven]
      _ = x * cliffordNorm Q g := hcenter x (Set.mem_univ x)
  · intro x hx
    calc
      CliffordAlgebra.involute (cliffordNorm Q g) * x = cliffordNorm Q g * x := by
        rw [heven]
      _ = x * cliffordNorm Q g := hcenter x (Set.mem_univ x)

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

/-- Clifford-norm carrier for the star-fixed sector. The paper's `B^03`
identification additionally uses its centralizer reduction `Z^{03}=Z^3`. -/
def StarFixedNormCarrier : Set (GA Q)ˣ :=
  {g | cliffordNorm Q g ∈ centralizerSet Q {x | star x = x}}

/-- Reversion-norm carrier for the grade-twisted stabilizer of the star-fixed
sector. Its reduction to the paper's `Ǎ^{03}` table entry is a separate
centralizer theorem. -/
def StarFixedTwistedNormCarrier : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈ twistedCentralizerSet Q {x | star x = x}}

/-- Equivalent carrier for the grade-twisted stabilizer of the star-fixed
sector, exposing separately the evenness and ordinary-centralizer conditions. -/
def StarFixedEvenCentralizerNormCarrier : Set (GA Q)ˣ :=
  {g | reversionNorm Q g ∈
    evenCarrier Q ∩ centralizerSet Q {x | star x = x}}

/-- Geometric `Γ^01` carrier: units whose ordinary adjoint action preserves the
reverse-fixed sector. -/
def Gamma01Carrier : Set (GA Q)ˣ :=
  stabilizes Q (adjointAction Q) {x | CliffordAlgebra.reverse x = x}

/-- Geometric `Γ^23` carrier: units whose ordinary adjoint action preserves the
reverse-anti-fixed sector. -/
def Gamma23Carrier : Set (GA Q)ˣ :=
  stabilizes Q (adjointAction Q) {x | CliffordAlgebra.reverse x = -x}

/-- Geometric `Γ^03` carrier: units whose ordinary adjoint action preserves
the Clifford-star-fixed sector. -/
def Gamma03Carrier : Set (GA Q)ˣ :=
  stabilizes Q (adjointAction Q) {x | star x = x}

@[simp] theorem involute_reversion_commute (x : GA Q) :
    CliffordAlgebra.involute (CliffordAlgebra.reverse x) =
      CliffordAlgebra.reverse (CliffordAlgebra.involute x) :=
  (CliffordAlgebra.reverse_involute x).symm

@[simp] theorem reversionNorm_reverse_fixed (g : (GA Q)ˣ) :
    CliffordAlgebra.reverse (reversionNorm Q g) = reversionNorm Q g := by
  simp [reversionNorm, CliffordAlgebra.reverse.map_mul]

/-- The paper's `ψ(g) = reverse(g) * g` lies in the joint sector pair
`0⊕1`, since that pair is exactly the reverse-fixed subspace. -/
theorem reversionNorm_mem_jointPair_01 (g : (GA Q)ˣ) :
    reversionNorm Q g ∈ (jointPairSubmodule Q 0 1 : Set (GA Q)) := by
  rw [jointPair_01_eq_reverseFixed Q]
  exact reversionNorm_reverse_fixed Q g

/-- The paper's `χ(g) = star(g) * g` lies in the joint sector pair `0⊕3`,
since that pair is exactly the Clifford-star-fixed subspace. -/
theorem cliffordNorm_star_fixed (g : (GA Q)ˣ) :
    star (cliffordNorm Q g) = cliffordNorm Q g := by
  unfold cliffordNorm
  rw [← CliffordAlgebra.star_def']
  rw [star_mul]
  simp

theorem cliffordNorm_mem_jointPair_03 (g : (GA Q)ˣ) :
    cliffordNorm Q g ∈ (jointPairSubmodule Q 0 3 : Set (GA Q)) := by
  rw [jointPair_03_eq_starFixed Q]
  exact cliffordNorm_star_fixed Q g

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

/-- Ordinary adjoint action preserves the star-anti-fixed sector exactly when
the Clifford norm `star(g) * g` commutes with that sector. -/
theorem adjointAction_mem_starAntiFixed_iff_cliffordNorm_commutes
    (g : (GA Q)ˣ) (x : GA Q) (hx : star x = -x) :
    star (adjointAction Q g x) = -adjointAction Q g x ↔
      cliffordNorm Q g * x = x * cliffordNorm Q g := by
  let a : GA Q := (g : GA Q)
  let ai : GA Q := ((g⁻¹ : (GA Q)ˣ) : GA Q)
  let r : GA Q := star a
  let ri : GA Q := star ai
  have hai : a * ai = 1 := by simp [a, ai]
  have hia : ai * a = 1 := by simp [a, ai]
  have hri_r : ri * r = 1 := by
    change star ai * star a = 1
    rw [← star_mul, hai]
    simp
  have hr_ri : r * ri = 1 := by
    change star a * star ai = 1
    rw [← star_mul, hia]
    simp
  have hstarAction : star (adjointAction Q g x) = ri * star x * r := by
    dsimp [adjointAction, r, ri, a, ai]
    rw [star_mul, star_mul]
    noncomm_ring
  have hnorm : cliffordNorm Q g = r * a := by
    change CliffordAlgebra.involute (CliffordAlgebra.reverse a) * a = star a * a
    rw [CliffordAlgebra.star_def']
  constructor
  · intro h
    have heq : ri * x * r = a * x * ai := by
      apply neg_injective
      calc
        -(ri * x * r) = star (adjointAction Q g x) := by
          rw [hstarAction, hx]
          noncomm_ring
        _ = -(adjointAction Q g x) := h
        _ = -(a * x * ai) := by rfl
    have hEq : x * r * a = r * a * x := by
      calc
        x * r * a = (r * ri) * x * r * a := by simp [hr_ri]
        _ = r * (ri * x * r) * a := by noncomm_ring
        _ = r * (a * x * ai) * a := by rw [heq]
        _ = r * a * x := by noncomm_ring [hia]
    rw [hnorm]
    calc
      (r * a) * x = r * a * x := rfl
      _ = x * r * a := hEq.symm
      _ = x * (r * a) := by noncomm_ring
  · intro h
    have hcentral : (r * a) * x = x * (r * a) := by
      calc
        (r * a) * x = cliffordNorm Q g * x := by rw [hnorm]
        _ = x * cliffordNorm Q g := h
        _ = x * (r * a) := by rw [hnorm]
    have heq : ri * x * r = a * x * ai := by
      calc
        ri * x * r = ri * (x * r * a) * ai := by noncomm_ring [hai]
        _ = ri * (r * a * x) * ai := by noncomm_ring [hcentral]
        _ = a * x * ai := by
          calc
            ri * (r * a * x) * ai = (ri * r) * a * x * ai := by noncomm_ring
            _ = 1 * a * x * ai := by rw [hri_r]
            _ = a * x * ai := by simp
    rw [hstarAction, hx]
    noncomm_ring [heq]
    simpa [adjointAction, a, ai] using
      congrArg (fun z : GA Q => (-1 : ℝ) • z) (Semigroup.mul_assoc a x ai).symm

/-- Ordinary adjoint action preserves the Clifford-star-fixed sector exactly
when the Clifford norm commutes with that sector. -/
theorem adjointAction_mem_starFixed_iff_cliffordNorm_commutes
    (g : (GA Q)ˣ) (x : GA Q) (hx : star x = x) :
    star (adjointAction Q g x) = adjointAction Q g x ↔
      cliffordNorm Q g * x = x * cliffordNorm Q g := by
  let a : GA Q := (g : GA Q)
  let ai : GA Q := ((g⁻¹ : (GA Q)ˣ) : GA Q)
  let r : GA Q := star a
  let ri : GA Q := star ai
  have hai : a * ai = 1 := by simp [a, ai]
  have hia : ai * a = 1 := by simp [a, ai]
  have hri_r : ri * r = 1 := by
    change star ai * star a = 1
    rw [← star_mul, hai]
    simp
  have hr_ri : r * ri = 1 := by
    change star a * star ai = 1
    rw [← star_mul, hia]
    simp
  have hstarAction : star (adjointAction Q g x) = ri * star x * r := by
    dsimp [adjointAction, r, ri, a, ai]
    rw [star_mul, star_mul]
    noncomm_ring
  have hnorm : cliffordNorm Q g = r * a := by
    change CliffordAlgebra.involute (CliffordAlgebra.reverse a) * a = star a * a
    rw [CliffordAlgebra.star_def']
  constructor
  · intro h
    have heq : ri * x * r = a * x * ai := by
      rw [hstarAction, hx] at h
      simpa [adjointAction, a, ai] using h
    have hEq : x * r * a = r * a * x := by
      calc
        x * r * a = (r * ri) * x * r * a := by simp [hr_ri]
        _ = r * (ri * x * r) * a := by noncomm_ring
        _ = r * (a * x * ai) * a := by rw [heq]
        _ = r * a * x := by noncomm_ring [hia]
    rw [hnorm]
    calc
      (r * a) * x = r * a * x := rfl
      _ = x * r * a := hEq.symm
      _ = x * (r * a) := by noncomm_ring
  · intro h
    have hcentral : (r * a) * x = x * (r * a) := by
      calc
        (r * a) * x = cliffordNorm Q g * x := by rw [hnorm]
        _ = x * cliffordNorm Q g := h
        _ = x * (r * a) := by rw [hnorm]
    have heq : ri * x * r = a * x * ai := by
      calc
        ri * x * r = ri * (x * r * a) * ai := by noncomm_ring [hai]
        _ = ri * (r * a * x) * ai := by noncomm_ring [hcentral]
        _ = a * x * ai := by
          calc
            ri * (r * a * x) * ai = (ri * r) * a * x * ai := by noncomm_ring
            _ = 1 * a * x * ai := by rw [hri_r]
            _ = a * x * ai := by simp
    rw [hstarAction, hx, heq]
    rfl

/-- The grade-twisted adjoint action preserves the Clifford-star-fixed sector
exactly when the reversion norm lies in its grade-twisted centralizer. -/
theorem gradeTwistedAdjoint_mem_starFixed_iff_reversionNorm_twistedCentralizes
    (g : (GA Q)ˣ) (x : GA Q) (hx : star x = x) :
    star (gradeTwistedAdjointAction Q g x) = gradeTwistedAdjointAction Q g x ↔
      CliffordAlgebra.involute (reversionNorm Q g) * x =
        x * reversionNorm Q g := by
  let a : GA Q := (g : GA Q)
  let ai : GA Q := ((g⁻¹ : (GA Q)ˣ) : GA Q)
  let r : GA Q := CliffordAlgebra.reverse a
  let ri : GA Q := star ai
  let s : GA Q := star a
  let hatA : GA Q := CliffordAlgebra.involute a
  have hai : a * ai = 1 := by simp [a, ai]
  have hia : ai * a = 1 := by simp [a, ai]
  have hsi_s : ri * s = 1 := by
    change star ai * star a = 1
    rw [← star_mul, hai]
    simp
  have hs_si : s * ri = 1 := by
    change star a * star ai = 1
    rw [← star_mul, hia]
    simp
  have hstarHat : star hatA = r := by
    dsimp [hatA, r]
    simp [CliffordAlgebra.star_def]
  have hstarAction : star (gradeTwistedAdjointAction Q g x) = ri * x * r := by
    change star (CliffordAlgebra.involute a * x * ai) = ri * x * r
    rw [star_mul, star_mul, hx, hstarHat]
    noncomm_ring
  have hnorm : reversionNorm Q g = r * a := rfl
  have hnormHat : CliffordAlgebra.involute (reversionNorm Q g) = s * hatA := by
    change CliffordAlgebra.involute (CliffordAlgebra.reverse a * a) = s * hatA
    rw [map_mul]
    change CliffordAlgebra.involute (CliffordAlgebra.reverse a) *
        CliffordAlgebra.involute a = star a * CliffordAlgebra.involute a
    rw [← CliffordAlgebra.star_def']
  constructor
  · intro h
    have heq : ri * x * r = hatA * x * ai := by
      calc
        ri * x * r = star (gradeTwistedAdjointAction Q g x) := hstarAction.symm
        _ = gradeTwistedAdjointAction Q g x := h
        _ = hatA * x * ai := rfl
    have hEq : x * r * a = (s * hatA) * x := by
      calc
        x * r * a = (s * ri) * x * r * a := by rw [hs_si]; noncomm_ring
        _ = s * (ri * x * r) * a := by noncomm_ring
        _ = s * (hatA * x * ai) * a := by rw [heq]
        _ = (s * hatA * x) * (ai * a) := by noncomm_ring
        _ = (s * hatA * x) * 1 := by rw [hia]
        _ = (s * hatA) * x := by noncomm_ring
    calc
      CliffordAlgebra.involute (reversionNorm Q g) * x = (s * hatA) * x := by
        rw [hnormHat]
      _ = x * r * a := hEq.symm
      _ = x * reversionNorm Q g := by rw [hnorm]; noncomm_ring
  · intro h
    have hEq : (s * hatA) * x = x * r * a := by
      calc
        (s * hatA) * x = CliffordAlgebra.involute (reversionNorm Q g) * x := by
          rw [hnormHat]
        _ = x * reversionNorm Q g := h
        _ = x * r * a := by rw [hnorm]; noncomm_ring
    have heq : ri * x * r = hatA * x * ai := by
      calc
        ri * x * r = ri * (x * r * a) * ai := by noncomm_ring [hai]
        _ = ri * ((s * hatA) * x) * ai := by rw [hEq]
        _ = (ri * s) * hatA * x * ai := by noncomm_ring
        _ = 1 * hatA * x * ai := by rw [hsi_s]
        _ = hatA * x * ai := by noncomm_ring
    rw [hstarAction, heq]
    rfl

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

/-- The grade-twisted geometric stabilizer of joint sectors `0,1` is exactly
the Clifford-norm twisted centralizer of the reverse-fixed sector. This is an
action-level classification; conversion to a grade-indexed table is separate. -/
theorem twistedPairStabilizer_01_iff_cliffordNorm_twistedCentralizes_reverseFixed
    (g : (GA Q)ˣ) :
    g ∈ twistedPairStabilizer Q 0 1 ↔
      cliffordNorm Q g ∈ twistedCentralizerSet Q
        {x | CliffordAlgebra.reverse x = x} := by
  change g ∈ stabilizes Q (gradeTwistedAdjointAction Q)
    (jointPairSubmodule Q 0 1 : Set (GA Q)) ↔ _
  rw [jointPair_01_eq_reverseFixed]
  exact stabilizes_reverseFixed_iff_cliffordNorm_twistedCentralizes Q g

/-- The first checked twisted group in Table 1: preserving joint types `0,1`
under the grade-twisted adjoint action is exactly the paper's norm condition
`χ(g) ∈ Z₁ ∩ Cl⁽⁰⁾`. -/
theorem twistedPairStabilizer_01_eq_PaperBCheck01 :
    twistedPairStabilizer Q 0 1 = PaperBCheck01 Q := by
  ext g
  change (g ∈ twistedPairStabilizer Q 0 1) ↔
    cliffordNorm Q g ∈ fixedGradeCentralizer Q 1 ∩ evenCarrier Q
  rw [twistedPairStabilizer_01_iff_cliffordNorm_twistedCentralizes_reverseFixed Q g]
  rw [reverseFixedTwistedCentralizer_eq_gradeOne_even Q]

/-- The grade-twisted adjoint action preserves reverse-anti-fixed elements
exactly when the Clifford norm lies in their grade-twisted centralizer. -/
theorem gradeTwistedAdjoint_mem_reverseAntiFixed_iff_norm_twistedCentralizes
    (g : (GA Q)ˣ) (x : GA Q) (hx : CliffordAlgebra.reverse x = -x) :
    CliffordAlgebra.reverse (gradeTwistedAdjointAction Q g x) =
        -(gradeTwistedAdjointAction Q g x) ↔
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
    rw [← CliffordAlgebra.reverse.map_mul]
    rw [hia]
    simp
  have hrevAction : CliffordAlgebra.reverse (gradeTwistedAdjointAction Q g x) =
      -(ri * x * hatR) := by
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
      apply neg_injective
      calc
        -(ri * x * hatR) = CliffordAlgebra.reverse (gradeTwistedAdjointAction Q g x) :=
          hrevAction.symm
        _ = -(gradeTwistedAdjointAction Q g x) := h
        _ = -(hatA * x * ai) := by rfl
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

/-- Setwise form of the reverse-anti-fixed Clifford-norm criterion for the
grade-twisted adjoint action. -/
theorem stabilizes_reverseAntiFixed_iff_cliffordNorm_twistedCentralizes
    (g : (GA Q)ˣ) :
    g ∈ stabilizes Q (gradeTwistedAdjointAction Q)
      {x | CliffordAlgebra.reverse x = -x} ↔
      cliffordNorm Q g ∈ twistedCentralizerSet Q
        {x | CliffordAlgebra.reverse x = -x} := by
  constructor
  · intro hg x hx
    exact (gradeTwistedAdjoint_mem_reverseAntiFixed_iff_norm_twistedCentralizes
      Q g x hx).mp (hg x hx)
  · intro hg x hx
    exact (gradeTwistedAdjoint_mem_reverseAntiFixed_iff_norm_twistedCentralizes
      Q g x hx).mpr (hg x hx)

/-- The grade-twisted stabilizer of joint sectors `2,3` is classified by the
Clifford-norm twisted centralizer of the reverse-anti-fixed sector. -/
theorem twistedPairStabilizer_23_iff_cliffordNorm_twistedCentralizes_reverseAntiFixed
    (g : (GA Q)ˣ) :
    g ∈ twistedPairStabilizer Q 2 3 ↔
      cliffordNorm Q g ∈ twistedCentralizerSet Q
        {x | CliffordAlgebra.reverse x = -x} := by
  change g ∈ stabilizes Q (gradeTwistedAdjointAction Q)
    (jointPairSubmodule Q 2 3 : Set (GA Q)) ↔ _
  rw [jointPair_23_eq_reverseAntiFixed]
  exact stabilizes_reverseAntiFixed_iff_cliffordNorm_twistedCentralizes Q g

/-- Set equality form: the `2⊕3` grade-twisted geometric stabilizer is the
Clifford-norm preimage of the twisted centralizer of its joint-type carrier. -/
theorem twistedPairStabilizer_23_eq_quaternionPairTwistedCentralizer_preimage :
    twistedPairStabilizer Q 2 3 =
      {g | cliffordNorm Q g ∈ quaternionPairTwistedCentralizer Q 2 3} := by
  ext g
  change g ∈ twistedPairStabilizer Q 2 3 ↔
    cliffordNorm Q g ∈
      twistedCentralizerSet Q (jointPairSubmodule Q 2 3 : Set (GA Q))
  rw [twistedPairStabilizer_23_iff_cliffordNorm_twistedCentralizes_reverseAntiFixed]
  rw [← jointPair_23_eq_reverseAntiFixed Q]

/-- The grade-twisted `2⊕3` stabilizer is contained in the paper's checked
`B̌^{23}` norm carrier. The reverse inclusion requires the paper's
grade/quaternion twisted-centralizer identity. -/
theorem twistedPairStabilizer_23_subset_PaperBCheck23 :
    twistedPairStabilizer Q 2 3 ⊆ PaperBCheck23 Q := by
  intro g hg
  rw [twistedPairStabilizer_23_eq_quaternionPairTwistedCentralizer_preimage Q] at hg
  change cliffordNorm Q g ∈
      twistedCentralizerSet Q (jointPairSubmodule Q 2 3 : Set (GA Q)) at hg
  constructor
  · intro x hx
    exact hg x (Submodule.mem_sup_left
      (fixedGradeCarrier_two_subset_jointType_two Q hx))
  · intro x hx
    exact hg x (Submodule.mem_sup_right
      (fixedGradeCarrier_three_subset_jointType_three Q hx))

/-- Setwise form of the grade-twisted star-fixed criterion. -/
theorem stabilizes_starFixed_iff_reversionNorm_twistedCentralizes (g : (GA Q)ˣ) :
    g ∈ stabilizes Q (gradeTwistedAdjointAction Q) {x | star x = x} ↔
      reversionNorm Q g ∈ twistedCentralizerSet Q {x | star x = x} := by
  constructor
  · intro hg x hx
    exact (gradeTwistedAdjoint_mem_starFixed_iff_reversionNorm_twistedCentralizes
      Q g x hx).mp (hg x hx)
  · intro hg x hx
    exact (gradeTwistedAdjoint_mem_starFixed_iff_reversionNorm_twistedCentralizes
      Q g x hx).mpr (hg x hx)

/-- The grade-twisted stabilizer of joint types `0,3` is the reversion-norm
preimage of the twisted centralizer of their star-fixed carrier. -/
theorem twistedPairStabilizer_03_eq_StarFixedTwistedNormCarrier :
    twistedPairStabilizer Q 0 3 = StarFixedTwistedNormCarrier Q := by
  ext g
  change g ∈ stabilizes Q (gradeTwistedAdjointAction Q)
      (jointPairSubmodule Q 0 3 : Set (GA Q)) ↔ _
  rw [jointPair_03_eq_starFixed Q]
  exact stabilizes_starFixed_iff_reversionNorm_twistedCentralizes Q g

/-- The `0⊕3` grade-twisted stabilizer also has a norm description in which
the grade-evenness of the reversion norm is explicit. This follows because
the star-fixed sector contains `1`, so twisted centralization forces evenness.
The further reduction to `Z^3 ∩ Cl⁽⁰⁾` is not asserted here. -/
theorem twistedPairStabilizer_03_eq_StarFixedEvenCentralizerNormCarrier :
    twistedPairStabilizer Q 0 3 = StarFixedEvenCentralizerNormCarrier Q := by
  calc
    twistedPairStabilizer Q 0 3 = StarFixedTwistedNormCarrier Q :=
      twistedPairStabilizer_03_eq_StarFixedTwistedNormCarrier Q
    _ = StarFixedEvenCentralizerNormCarrier Q := by
      ext g
      change reversionNorm Q g ∈ twistedCentralizerSet Q {x | star x = x} ↔
        reversionNorm Q g ∈
          evenCarrier Q ∩ centralizerSet Q {x | star x = x}
      rw [twistedCentralizer_starFixed_eq_even_inter_centralizer_starFixed Q]

/-- The grade-twisted `0⊕3` stabilizer is contained in the paper's checked
`Ǎ^{03}` norm carrier. The proof uses grade-three's inclusion in the
star-fixed sector; the reverse direction is part of the paper's centralizer
reduction. -/
theorem twistedPairStabilizer_03_subset_PaperACheck03 :
    twistedPairStabilizer Q 0 3 ⊆ PaperACheck03 Q := by
  intro g hg
  rw [twistedPairStabilizer_03_eq_StarFixedEvenCentralizerNormCarrier Q] at hg
  change reversionNorm Q g ∈
    evenCarrier Q ∩ centralizerSet Q {x | star x = x} at hg
  rcases hg with ⟨heven, hcentral⟩
  refine ⟨?_, heven⟩
  intro x hx
  have htype : x ∈ jointTypeSubmodule Q 3 :=
    fixedGradeCarrier_three_subset_jointType_three Q hx
  have hstar : star x = x := by
    have hsign := (mem_jointType_iff Q 3 x).mp htype
    change CliffordAlgebra.reverse (CliffordAlgebra.involute x) = x
    rw [hsign.1]
    simp [gradeSign, reversionSign, hsign.2]
  exact hcentral x hstar

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

/-- The ordinary-adjoint stabilizer of joint quaternion types `2,3` is the
reversion-norm preimage of their joint centralizer. This is the joint-type
action lane, not the paper's homogeneous-grade `A^{23}` group. -/
theorem adjointPairStabilizer_23_eq_JointTypeA23NormCarrier :
    adjointPairStabilizer Q 2 3 = JointTypeA23NormCarrier Q := by
  calc
    adjointPairStabilizer Q 2 3 = ReverseAntiFixedNormCarrier Q :=
      adjointPairStabilizer_23_eq_ReverseAntiFixedNormCarrier Q
    _ = JointTypeA23NormCarrier Q := by
      ext g
      change reversionNorm Q g ∈
          centralizerSet Q {x | CliffordAlgebra.reverse x = -x} ↔
        reversionNorm Q g ∈
          centralizerSet Q (jointPairSubmodule Q 2 3 : Set (GA Q))
      rw [← jointPair_23_eq_reverseAntiFixed Q]

/-- The ordinary adjoint stabilizer of the star-anti-fixed sector is exactly
the centralizer carrier of the Clifford norm. -/
theorem stabilizes_starAntiFixed_iff_cliffordNormCentralizes (g : (GA Q)ˣ) :
    g ∈ stabilizes Q (adjointAction Q)
      {x | star x = -x} ↔
      cliffordNorm Q g ∈ centralizerSet Q {x | star x = -x} := by
  constructor
  · intro hg x hx
    exact (adjointAction_mem_starAntiFixed_iff_cliffordNorm_commutes Q g x hx).mp
      (hg x hx)
  · intro hg x hx
    exact (adjointAction_mem_starAntiFixed_iff_cliffordNorm_commutes Q g x hx).mpr
      (hg x hx)

/-- Setwise star-fixed stabilizer criterion for the ordinary adjoint action. -/
theorem stabilizes_starFixed_iff_cliffordNormCentralizes (g : (GA Q)ˣ) :
    g ∈ Gamma03Carrier Q ↔ g ∈ StarFixedNormCarrier Q := by
  constructor
  · intro hg x hx
    exact (adjointAction_mem_starFixed_iff_cliffordNorm_commutes Q g x hx).mp
      (hg x hx)
  · intro hg x hx
    exact (adjointAction_mem_starFixed_iff_cliffordNorm_commutes Q g x hx).mpr
      (hg x hx)

/-- Theorem 4.1's `B^12` classification: the ordinary-adjoint stabilizer of
joint types `1,2` is the Clifford-norm preimage of the grade-one centralizer. -/
theorem adjointPairStabilizer_12_eq_PaperB12 :
    adjointPairStabilizer Q 1 2 = PaperB12 Q := by
  ext g
  change (∀ x, x ∈ (jointPairSubmodule Q 1 2 : Set (GA Q)) →
      adjointAction Q g x ∈ (jointPairSubmodule Q 1 2 : Set (GA Q))) ↔
    cliffordNorm Q g ∈ fixedGradeCentralizer Q 1
  rw [jointPair_12_eq_starAntiFixed Q]
  change g ∈ stabilizes Q (adjointAction Q) {x | star x = -x} ↔ _
  rw [stabilizes_starAntiFixed_iff_cliffordNormCentralizes Q g]
  rw [← jointPair_12_eq_starAntiFixed Q]
  change cliffordNorm Q g ∈ quaternionPairCentralizer Q 1 2 ↔ _
  rw [quaternionPairCentralizer_12_eq_gradeOne Q]

/-- The ordinary-adjoint stabilizer of joint types `0,3` is the Clifford-norm
centralizer of the star-fixed sector. Identifying it with `B^03` still requires
the paper's centralizer reduction `Z^{03}=Z^3`. -/
theorem adjointPairStabilizer_03_eq_StarFixedNormCarrier :
    adjointPairStabilizer Q 0 3 = StarFixedNormCarrier Q := by
  ext g
  change (∀ x, x ∈ (jointPairSubmodule Q 0 3 : Set (GA Q)) →
      adjointAction Q g x ∈ (jointPairSubmodule Q 0 3 : Set (GA Q))) ↔
    g ∈ StarFixedNormCarrier Q
  rw [jointPair_03_eq_starFixed Q]
  exact stabilizes_starFixed_iff_cliffordNormCentralizes Q g

/-- The ordinary-adjoint `0⊕3` stabilizer is contained in the paper's
homogeneous-grade `B^{03}` carrier. The converse is the grade-three instance
of the paper's centralizer comparison in Lemma 3.2. -/
theorem adjointPairStabilizer_03_subset_PaperB03 :
    adjointPairStabilizer Q 0 3 ⊆ PaperB03 Q := by
  intro g hg x hx
  have hstarCarrier : x ∈ {y : GA Q | star y = y} := by
    have htype : x ∈ jointTypeSubmodule Q 3 :=
      fixedGradeCarrier_three_subset_jointType_three Q hx
    have hpair : x ∈ (jointPairSubmodule Q 0 3 : Set (GA Q)) :=
      Submodule.mem_sup_right htype
    rw [← jointPair_03_eq_starFixed Q]
    exact hpair
  rw [adjointPairStabilizer_03_eq_StarFixedNormCarrier Q] at hg
  change cliffordNorm Q g ∈ centralizerSet Q {y | star y = y} at hg
  exact hg x hstarCarrier

/-- The ordinary-adjoint `2⊕3` stabilizer is contained in the paper's
homogeneous-grade `A^{23}` carrier. This proves one direction of the paper's
classification; the converse uses its grade/quaternion centralizer identity. -/
theorem adjointPairStabilizer_23_subset_PaperA23 :
    adjointPairStabilizer Q 2 3 ⊆ PaperA23 Q := by
  rw [adjointPairStabilizer_23_eq_JointTypeA23NormCarrier]
  exact JointTypeA23NormCarrier_subset_PaperA23 Q

/-! ## The one-dimensional radical example `Cl_{0,0,1}` -/

/-- The paper's one-dimensional radical Clifford algebra, represented on `ℝ`
with the zero quadratic form. Mathlib identifies this algebra with the dual
numbers. -/
abbrev RadicalLineClifford := CliffordAlgebra (0 : QuadraticForm ℝ ℝ)

/-- The one-dimensional radical Clifford product is commutative, transported
from the dual-number algebra equivalence. -/
theorem radicalLine_mul_comm (x y : RadicalLineClifford) : x * y = y * x := by
  apply (CliffordAlgebraDualNumber.equiv (R := ℝ)).injective
  simp only [map_mul]
  exact mul_comm _ _

/-- Reversion is the identity in the one-generator radical Clifford algebra:
it is anti-multiplicative, and this particular Clifford algebra is
commutative. -/
theorem radicalLine_reverse_eq_self (x : RadicalLineClifford) :
    CliffordAlgebra.reverse x = x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v => simp
  | add x y hx hy => simp only [CliffordAlgebra.reverse.map_add, hx, hy]
  | mul x y hx hy =>
      simp only [CliffordAlgebra.reverse.map_mul, hx, hy]
      exact radicalLine_mul_comm y x

/-- In the one-dimensional radical model, homogeneous grades above the
underlying vector-space dimension vanish. -/
theorem radicalLine_fixedGradeCarrier_eq_bot {k : ℕ} (hk : 1 < k) :
    fixedGradeCarrier (0 : QuadraticForm ℝ ℝ) k = ⊥ := by
  rw [fixedGradeCarrier]
  have hproj :
      InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj
        (0 : QuadraticForm ℝ ℝ) k = 0 := by
    apply InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj_eq_zero_of_gt_finrank
    simpa using hk
  change LinearMap.range
      (InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj
        (0 : QuadraticForm ℝ ℝ) k) = ⊥
  rw [hproj]
  exact LinearMap.range_zero

/-- The checked `B̌^{23}` norm carrier is the full unit group for
`Cl_{0,0,1}`: both homogeneous grade-two and grade-three sectors vanish. -/
theorem radicalLine_PaperBCheck23_eq_univ :
    PaperBCheck23 (0 : QuadraticForm ℝ ℝ) = Set.univ := by
  ext g
  change (cliffordNorm (0 : QuadraticForm ℝ ℝ) g ∈
      fixedGradeTwistedCentralizer (0 : QuadraticForm ℝ ℝ) 2 ∩
        fixedGradeTwistedCentralizer (0 : QuadraticForm ℝ ℝ) 3) ↔ True
  constructor
  · intro _; trivial
  · intro _
    constructor
    · intro x hx
      have hx0 : x = 0 := by
        rw [radicalLine_fixedGradeCarrier_eq_bot (k := 2) (by omega)] at hx
        simpa using hx
      simp [hx0]
    · intro x hx
      have hx0 : x = 0 := by
        rw [radicalLine_fixedGradeCarrier_eq_bot (k := 3) (by omega)] at hx
        simpa using hx
      simp [hx0]

/-- The checked `B̌^{01}` norm carrier is the full unit group for
`Cl_{0,0,1}`. The Clifford norm lies in the star-fixed `0⊕3` sector; in this
one-generator commutative algebra reversion is the identity, so star-fixedness
implies the required evenness. Commutativity supplies the grade-one
centralizer condition. -/
theorem radicalLine_PaperBCheck01_eq_univ :
    PaperBCheck01 (0 : QuadraticForm ℝ ℝ) = Set.univ := by
  ext g
  change (cliffordNorm (0 : QuadraticForm ℝ ℝ) g ∈
      fixedGradeCentralizer (0 : QuadraticForm ℝ ℝ) 1 ∩
        evenCarrier (0 : QuadraticForm ℝ ℝ)) ↔ True
  constructor
  · intro _
    trivial
  · intro _
    constructor
    · intro x hx
      exact radicalLine_mul_comm _ _
    · have hmem : cliffordNorm (0 : QuadraticForm ℝ ℝ) g ∈
          (jointPairSubmodule (0 : QuadraticForm ℝ ℝ) 0 3 : Set RadicalLineClifford) :=
        cliffordNorm_mem_jointPair_03 (0 : QuadraticForm ℝ ℝ) g
      rw [jointPair_03_eq_starFixed (0 : QuadraticForm ℝ ℝ)] at hmem
      have hstar : star (cliffordNorm (0 : QuadraticForm ℝ ℝ) g) =
          cliffordNorm (0 : QuadraticForm ℝ ℝ) g := hmem
      change CliffordAlgebra.involute
          (cliffordNorm (0 : QuadraticForm ℝ ℝ) g) =
        cliffordNorm (0 : QuadraticForm ℝ ℝ) g
      change CliffordAlgebra.reverse (CliffordAlgebra.involute
          (cliffordNorm (0 : QuadraticForm ℝ ℝ) g)) =
        cliffordNorm (0 : QuadraticForm ℝ ℝ) g at hstar
      rw [radicalLine_reverse_eq_self] at hstar
      exact hstar

/-- Every element of the one-generator radical Clifford algebra satisfies
the grade-twisted commutation relation with its grade-one generator. The
induction uses that every product of two generators vanishes in the zero
quadratic form. -/
theorem radicalLine_involute_mul_generator (a : RadicalLineClifford) :
    CliffordAlgebra.involute a * CliffordAlgebra.ι
        (0 : QuadraticForm ℝ ℝ) 1 =
      CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1 * a := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r =>
      simpa using (Algebra.commutes r
        (CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1))
  | ι v =>
      rw [CliffordAlgebra.involute_ι, neg_mul,
        CliffordAlgebraDualNumber.ι_mul_ι v 1,
        CliffordAlgebraDualNumber.ι_mul_ι 1 v]
      simp
  | add a b ha hb =>
      rw [map_add, add_mul, mul_add, ha, hb]
  | mul a b ha hb =>
      rw [map_mul]
      calc
        (CliffordAlgebra.involute a * CliffordAlgebra.involute b) *
            CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1 =
          CliffordAlgebra.involute a *
            (CliffordAlgebra.involute b *
              CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1) :=
                by noncomm_ring
        _ = CliffordAlgebra.involute a *
              (CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1 * b) := by rw [hb]
        _ = (CliffordAlgebra.involute a *
              CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1) * b :=
                by noncomm_ring
        _ = (CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1 * a) * b := by rw [ha]
        _ = CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1 * (a * b) :=
              by noncomm_ring

/-- Every element of `Cl_{0,0,1}` twisted-centralizes homogeneous grade one.
The grade-one carrier is the span of its single radical generator, and the
generator intertwining identity extends by scalar linearity. -/
theorem radicalLine_fixedGradeTwistedCentralizer_one_eq_univ :
    fixedGradeTwistedCentralizer (0 : QuadraticForm ℝ ℝ) 1 = Set.univ := by
  ext a
  change (∀ x, x ∈ (fixedGradeCarrier (0 : QuadraticForm ℝ ℝ) 1 :
      Set RadicalLineClifford) →
      CliffordAlgebra.involute a * x = x * a) ↔ True
  constructor
  · intro _
    trivial
  · intro _ x hx
    have hdim : Module.finrank ℝ
        (fixedGradeCarrier (0 : QuadraticForm ℝ ℝ) 1) = 1 := by
      rw [fixedGradeCarrier_finrank_eq_choose]
      norm_num
    have hgen : CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1 ∈
        fixedGradeCarrier (0 : QuadraticForm ℝ ℝ) 1 :=
      cliffordGenerator_mem_fixedGradeCarrier_one (0 : QuadraticForm ℝ ℝ) 1
    have hgen0 : CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1 ≠ 0 := by
      intro h
      have h' := congrArg (CliffordAlgebraDualNumber.equiv (R := ℝ)) h
      have hsnd := congrArg TrivSqZeroExt.snd h'
      simp [CliffordAlgebraDualNumber.equiv_ι] at hsnd
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim hgen hgen0
    have hxspan : x ∈ ℝ ∙ CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1 := by
      rw [← hspan]
      exact hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxspan
    calc
      CliffordAlgebra.involute a * x =
          c • (CliffordAlgebra.involute a *
            CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1) := by
              rw [← hc, Algebra.mul_smul_comm]
      _ = c • (CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1 * a) := by
            rw [radicalLine_involute_mul_generator]
      _ = x * a := by rw [← hc, Algebra.smul_mul_assoc]

/-- The paper's `Ǎ^{12}` norm carrier in `Cl_{0,0,1}` is the full unit group,
matching the odd-dimensional `r=1` row of its §6 signature table. The grade-two
test vanishes, while every element twisted-centralizes grade one. -/
theorem radicalLine_PaperACheck12_eq_univ :
    PaperACheck12 (0 : QuadraticForm ℝ ℝ) = Set.univ := by
  ext g
  change (reversionNorm (0 : QuadraticForm ℝ ℝ) g ∈
      fixedGradeTwistedCentralizer (0 : QuadraticForm ℝ ℝ) 1 ∧
    reversionNorm (0 : QuadraticForm ℝ ℝ) g ∈
      fixedGradeTwistedCentralizer (0 : QuadraticForm ℝ ℝ) 2) ↔ True
  constructor
  · intro _
    trivial
  · intro _
    constructor
    · rw [radicalLine_fixedGradeTwistedCentralizer_one_eq_univ]
      trivial
    · intro x hx
      have hx0 : x = 0 := by
        rw [radicalLine_fixedGradeCarrier_eq_bot (k := 2) (by omega)] at hx
        simpa using hx
      simp [hx0]

/-- In `Cl_{0,0,1}`, the modified twisted carrier `Q̃^12` is the full unit
group. Its grade-two centralizer test vanishes, and the grade-one test reduces
to the relation of the preceding lemma because the grade-one carrier is the
span of its generator. This completes the four radical-line identities in
equation (6.15). -/
theorem radicalLine_PaperQCheck12_eq_univ :
    PaperQCheck12 (0 : QuadraticForm ℝ ℝ) = Set.univ := by
  ext g
  change (reversionNorm (0 : QuadraticForm ℝ ℝ) g ∈
      fixedGradeTwistedCentralizer (0 : QuadraticForm ℝ ℝ) 1 ∧
    cliffordNorm (0 : QuadraticForm ℝ ℝ) g ∈
      fixedGradeCentralizer (0 : QuadraticForm ℝ ℝ) 2) ↔ True
  constructor
  · intro _
    trivial
  · intro _
    constructor
    · intro x hx
      have hdim : Module.finrank ℝ
          (fixedGradeCarrier (0 : QuadraticForm ℝ ℝ) 1) = 1 := by
        rw [fixedGradeCarrier_finrank_eq_choose]
        norm_num
      have hgen : CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1 ∈
          fixedGradeCarrier (0 : QuadraticForm ℝ ℝ) 1 :=
        cliffordGenerator_mem_fixedGradeCarrier_one (0 : QuadraticForm ℝ ℝ) 1
      have hgen0 : CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1 ≠ 0 := by
        intro h
        have h' := congrArg (CliffordAlgebraDualNumber.equiv (R := ℝ)) h
        have hsnd := congrArg TrivSqZeroExt.snd h'
        simp [CliffordAlgebraDualNumber.equiv_ι] at hsnd
      have hspan := eq_span_singleton_of_mem_of_finrank_eq_one
        hdim hgen hgen0
      have hxspan : x ∈ ℝ ∙ CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1 := by
        rw [← hspan]
        exact hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxspan
      rw [reversionNorm, radicalLine_reverse_eq_self]
      calc
        CliffordAlgebra.involute
            ((g : RadicalLineClifford) * (g : RadicalLineClifford)) * x =
            c • (CliffordAlgebra.involute
              ((g : RadicalLineClifford) * (g : RadicalLineClifford)) *
              CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1) :=
                by rw [← hc, Algebra.mul_smul_comm]
        _ = c • (CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) 1 *
              ((g : RadicalLineClifford) * (g : RadicalLineClifford))) := by
                rw [radicalLine_involute_mul_generator]
        _ = x * ((g : RadicalLineClifford) * (g : RadicalLineClifford)) :=
              by rw [← hc, Algebra.smul_mul_assoc]
    · intro x hx
      rw [radicalLine_fixedGradeCarrier_eq_bot (k := 2) (by omega)] at hx
      subst x
      simp

/-- The modified twisted carrier `Q̃^01` is the full unit group in
`Cl_{0,0,1}`. The grade-four test vanishes by dimension; the grade-one
twisted test follows because the Clifford norm is even and the algebra is
commutative. This is an instance of equation (6.15) in the paper. -/
theorem radicalLine_PaperQCheck01_eq_univ :
    PaperQCheck01 (0 : QuadraticForm ℝ ℝ) = Set.univ := by
  ext g
  change (reversionNorm (0 : QuadraticForm ℝ ℝ) g ∈
      fixedGradeCentralizer (0 : QuadraticForm ℝ ℝ) 4 ∧
    cliffordNorm (0 : QuadraticForm ℝ ℝ) g ∈
      fixedGradeTwistedCentralizer (0 : QuadraticForm ℝ ℝ) 1) ↔ True
  constructor
  · intro _
    trivial
  · intro _
    constructor
    · intro x hx
      rw [radicalLine_fixedGradeCarrier_eq_bot (k := 4) (by omega)] at hx
      subst x
      simp
    · intro x hx
      have hmem : cliffordNorm (0 : QuadraticForm ℝ ℝ) g ∈
          (jointPairSubmodule (0 : QuadraticForm ℝ ℝ) 0 3 : Set RadicalLineClifford) :=
        cliffordNorm_mem_jointPair_03 (0 : QuadraticForm ℝ ℝ) g
      rw [jointPair_03_eq_starFixed (0 : QuadraticForm ℝ ℝ)] at hmem
      have hstar : star (cliffordNorm (0 : QuadraticForm ℝ ℝ) g) =
          cliffordNorm (0 : QuadraticForm ℝ ℝ) g := hmem
      have hEven : CliffordAlgebra.involute
          (cliffordNorm (0 : QuadraticForm ℝ ℝ) g) =
            cliffordNorm (0 : QuadraticForm ℝ ℝ) g := by
        change CliffordAlgebra.reverse (CliffordAlgebra.involute
            (cliffordNorm (0 : QuadraticForm ℝ ℝ) g)) =
          cliffordNorm (0 : QuadraticForm ℝ ℝ) g at hstar
        rw [radicalLine_reverse_eq_self] at hstar
        exact hstar
      have hcentral : cliffordNorm (0 : QuadraticForm ℝ ℝ) g * x =
          x * cliffordNorm (0 : QuadraticForm ℝ ℝ) g :=
        radicalLine_mul_comm _ _
      rw [hEven, hcentral]

/-- The modified twisted carrier `Q̃^23` is the full unit group in
`Cl_{0,0,1}`. Both centralizer tests are on grades above the carrier
dimension, hence their tested subspaces are zero. This is one of the four
radical Grassmann identities listed in equation (6.15) of the paper. -/
theorem radicalLine_PaperQCheck23_eq_univ :
    PaperQCheck23 (0 : QuadraticForm ℝ ℝ) = Set.univ := by
  ext g
  change (∀ x, x ∈ (fixedGradeCarrier (0 : QuadraticForm ℝ ℝ) 2 : Set _)
      → reversionNorm (0 : QuadraticForm ℝ ℝ) g * x = x * reversionNorm (0 : QuadraticForm ℝ ℝ) g) ∧
    (∀ x, x ∈ (fixedGradeCarrier (0 : QuadraticForm ℝ ℝ) 3 : Set _)
      → CliffordAlgebra.involute (cliffordNorm (0 : QuadraticForm ℝ ℝ) g) * x =
        x * cliffordNorm (0 : QuadraticForm ℝ ℝ) g) ↔ True
  constructor
  · intro _
    trivial
  · intro _
    constructor
    · intro x hx
      rw [radicalLine_fixedGradeCarrier_eq_bot (k := 2) (by omega)] at hx
      subst x
      simp
    · intro x hx
      rw [radicalLine_fixedGradeCarrier_eq_bot (k := 3) (by omega)] at hx
      subst x
      simp

/-- The modified twisted carrier `Q̃^03` is the full unit group in
`Cl_{0,0,1}`. Its tests are on grades three and four, both zero in this
one-dimensional carrier. This is another instance of equation (6.15). -/
theorem radicalLine_PaperQCheck03_eq_univ :
    PaperQCheck03 (0 : QuadraticForm ℝ ℝ) = Set.univ := by
  ext g
  change (∀ x, x ∈ (fixedGradeCarrier (0 : QuadraticForm ℝ ℝ) 3 : Set _)
      → CliffordAlgebra.involute (reversionNorm (0 : QuadraticForm ℝ ℝ) g) * x =
        x * reversionNorm (0 : QuadraticForm ℝ ℝ) g) ∧
    (∀ x, x ∈ (fixedGradeCarrier (0 : QuadraticForm ℝ ℝ) 4 : Set _)
      → cliffordNorm (0 : QuadraticForm ℝ ℝ) g * x = x * cliffordNorm (0 : QuadraticForm ℝ ℝ) g) ↔ True
  constructor
  · intro _
    trivial
  · intro _
    constructor
    · intro x hx
      rw [radicalLine_fixedGradeCarrier_eq_bot (k := 3) (by omega)] at hx
      subst x
      simp
    · intro x hx
      rw [radicalLine_fixedGradeCarrier_eq_bot (k := 4) (by omega)] at hx
      subst x
      simp

/-- The paper's `Ǎ^{03}` norm carrier in `Cl_{0,0,1}` reduces to the condition
that the reversion norm is even: grade three vanishes in this dimension. -/
theorem radicalLine_PaperACheck03_eq_evenNormCarrier :
    PaperACheck03 (0 : QuadraticForm ℝ ℝ) =
      {g | reversionNorm (0 : QuadraticForm ℝ ℝ) g ∈
        evenCarrier (0 : QuadraticForm ℝ ℝ)} := by
  ext g
  simp [PaperACheck03, fixedGradeCentralizer, centralizerSet,
    radicalLine_fixedGradeCarrier_eq_bot (k := 3) (by omega)]

/-- In the radical-line Clifford algebra, the even subalgebra is exactly the
scalar subalgebra. The even induction reduces every positive even word to a
product of two radical generators, which vanishes. -/
theorem radicalLine_evenCarrier_eq_scalarRange :
    evenCarrier (0 : QuadraticForm ℝ ℝ) =
      Set.range (algebraMap ℝ RadicalLineClifford) := by
  have hevenScalar : ∀ x : RadicalLineClifford,
      x ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℝ ℝ) 0 →
        ∃ r : ℝ, algebraMap ℝ RadicalLineClifford r = x := by
    intro x hx
    exact CliffordAlgebra.even_induction (Q := (0 : QuadraticForm ℝ ℝ))
      (motive := fun x _ => ∃ r : ℝ, algebraMap ℝ RadicalLineClifford r = x)
      (fun r => ⟨r, rfl⟩)
      (fun x y hx hy ihx ihy => by
        obtain ⟨r, rfl⟩ := ihx
        obtain ⟨s, rfl⟩ := ihy
        exact ⟨r + s, by simp⟩)
      (fun v w x hx ih => by
        have hprod : CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) v *
            CliffordAlgebra.ι (0 : QuadraticForm ℝ ℝ) w = 0 :=
          CliffordAlgebraDualNumber.ι_mul_ι v w
        exact ⟨0, by simp [hprod]⟩)
      x hx
  ext x
  constructor
  · intro hx
    exact hevenScalar x ((mem_evenCarrier_iff (0 : QuadraticForm ℝ ℝ) x).mp hx)
  · rintro ⟨r, rfl⟩
    simp [evenCarrier]

/-- In `Cl_{0,0,1}`, the checked `Ǎ^{03}` condition is exactly that the
reversion norm be scalar-valued. This is the norm-carrier form of the paper's
low-dimensional collapse; it does not yet identify the group elements
themselves with scalar units. -/
theorem radicalLine_PaperACheck03_eq_scalarNormCarrier :
    PaperACheck03 (0 : QuadraticForm ℝ ℝ) =
      {g | ∃ r : ℝ, reversionNorm (0 : QuadraticForm ℝ ℝ) g =
        algebraMap ℝ RadicalLineClifford r} := by
  ext g
  rw [radicalLine_PaperACheck03_eq_evenNormCarrier,
    radicalLine_evenCarrier_eq_scalarRange]
  change (∃ r : ℝ, algebraMap ℝ RadicalLineClifford r =
      reversionNorm (0 : QuadraticForm ℝ ℝ) g) ↔
    ∃ r : ℝ, reversionNorm (0 : QuadraticForm ℝ ℝ) g =
      algebraMap ℝ RadicalLineClifford r
  constructor <;> rintro ⟨r, hr⟩ <;> exact ⟨r, hr.symm⟩

/-- A unit in the radical-line Clifford algebra whose square is scalar is
itself scalar. In dual-number coordinates, invertibility makes the scalar
coordinate nonzero, and the vanishing nilpotent coordinate of the square
then forces the nilpotent coordinate itself to vanish. -/
theorem radicalLine_unit_sq_scalar_implies_scalar (g : RadicalLineCliffordˣ)
    (h : ∃ r : ℝ, (g : RadicalLineClifford) ^ 2 = algebraMap ℝ RadicalLineClifford r) :
    ∃ a : ℝ, (g : RadicalLineClifford) = algebraMap ℝ RadicalLineClifford a := by
  let e := CliffordAlgebraDualNumber.equiv (R := ℝ)
  let z : DualNumber ℝ := e g
  let zi : DualNumber ℝ := e (↑(g⁻¹) : RadicalLineClifford)
  have hzInv : z * zi = 1 := by
    dsimp [z, zi]
    rw [← map_mul]
    simp
  have ha0 : TrivSqZeroExt.fst z ≠ 0 := by
    intro ha
    have hfst : TrivSqZeroExt.fst z * TrivSqZeroExt.fst zi = 1 := by
      rw [← TrivSqZeroExt.fst_mul]
      exact congrArg TrivSqZeroExt.fst hzInv
    rw [ha, zero_mul] at hfst
    exact zero_ne_one hfst
  rcases h with ⟨r, hr⟩
  have hsq : z * z = algebraMap ℝ (DualNumber ℝ) r := by
    have h := congrArg e hr
    simpa [z, pow_two] using h
  have hnil : TrivSqZeroExt.fst z * TrivSqZeroExt.snd z +
      TrivSqZeroExt.snd z * TrivSqZeroExt.fst z = 0 := by
    have hsnd := congrArg TrivSqZeroExt.snd hsq
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl] at hsnd
    simpa only [DualNumber.snd_mul] using hsnd
  have hmul : TrivSqZeroExt.fst z * TrivSqZeroExt.snd z = 0 := by
    rw [mul_comm (TrivSqZeroExt.snd z) (TrivSqZeroExt.fst z)] at hnil
    nlinarith
  have hz2 : z.2 = 0 := by
    change TrivSqZeroExt.snd z = 0
    exact (mul_eq_zero.mp hmul).resolve_left ha0
  have hzscalar : z = algebraMap ℝ (DualNumber ℝ) (TrivSqZeroExt.fst z) := by
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.algebraMap_eq_inl]
    · exact hz2
  refine ⟨TrivSqZeroExt.fst z, ?_⟩
  apply e.injective
  simpa [z] using hzscalar

/-- The paper's `Cl_{0,0,1}` checked `Ǎ^{03}` group consists exactly of scalar
units (expressed as units whose underlying element is a nonzero scalar). -/
theorem radicalLine_PaperACheck03_eq_scalarUnits :
    PaperACheck03 (0 : QuadraticForm ℝ ℝ) =
      {g : RadicalLineCliffordˣ | ∃ a : ℝ, a ≠ 0 ∧
        (g : RadicalLineClifford) = algebraMap ℝ RadicalLineClifford a} := by
  ext g
  constructor
  · intro hg
    rw [radicalLine_PaperACheck03_eq_scalarNormCarrier] at hg
    have hscalarNorm : ∃ r : ℝ,
        reversionNorm (0 : QuadraticForm ℝ ℝ) g = algebraMap ℝ RadicalLineClifford r := by
      exact hg
    have hsqScalar : ∃ r : ℝ,
        (g : RadicalLineClifford) ^ 2 = algebraMap ℝ RadicalLineClifford r := by
      rcases hscalarNorm with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      simpa [pow_two, reversionNorm, radicalLine_reverse_eq_self] using hr
    obtain ⟨a, ha⟩ := radicalLine_unit_sq_scalar_implies_scalar g hsqScalar
    refine ⟨a, ?_, ha⟩
    intro ha0
    have hg0 : (g : RadicalLineClifford) = 0 := by simp [ha, ha0]
    exact (Units.ne_zero g) hg0
  · rintro ⟨a, ha, hscalar⟩
    rw [radicalLine_PaperACheck03_eq_scalarNormCarrier]
    refine ⟨a ^ 2, ?_⟩
    rw [reversionNorm, radicalLine_reverse_eq_self, hscalar]
    rw [← map_mul]
    congr 1
    ring

/-- In the one-dimensional radical example, the grade-twisted stabilizer of
joint types `0,3` is exactly the paper's checked `Ǎ^{03}` group. Both norm
descriptions reduce to evenness of the reversion norm: the relevant ordinary
centralizers are unrestricted because the algebra is commutative. -/
theorem radicalLine_twistedPairStabilizer_03_eq_PaperACheck03 :
    twistedPairStabilizer (0 : QuadraticForm ℝ ℝ) 0 3 =
      PaperACheck03 (0 : QuadraticForm ℝ ℝ) := by
  calc
    twistedPairStabilizer (0 : QuadraticForm ℝ ℝ) 0 3 =
        StarFixedEvenCentralizerNormCarrier (0 : QuadraticForm ℝ ℝ) :=
      twistedPairStabilizer_03_eq_StarFixedEvenCentralizerNormCarrier
        (0 : QuadraticForm ℝ ℝ)
    _ = PaperACheck03 (0 : QuadraticForm ℝ ℝ) := by
      ext g
      change (reversionNorm (0 : QuadraticForm ℝ ℝ) g ∈
          evenCarrier (0 : QuadraticForm ℝ ℝ) ∩
            centralizerSet (0 : QuadraticForm ℝ ℝ) {x | star x = x}) ↔
        reversionNorm (0 : QuadraticForm ℝ ℝ) g ∈
          fixedGradeCentralizer (0 : QuadraticForm ℝ ℝ) 3 ∩
            evenCarrier (0 : QuadraticForm ℝ ℝ)
      simp [fixedGradeCentralizer, centralizerSet,
        radicalLine_fixedGradeCarrier_eq_bot (k := 3) (by omega),
        radicalLine_mul_comm]

/-- Every ordinary adjoint action in `Cl_{0,0,1}` is the identity because this
Clifford algebra is commutative. -/
theorem radicalLine_adjointAction_eq (g : RadicalLineCliffordˣ)
    (x : RadicalLineClifford) :
    adjointAction (0 : QuadraticForm ℝ ℝ) g x = x := by
  change (g : RadicalLineClifford) * x *
      ((g⁻¹ : RadicalLineCliffordˣ) : RadicalLineClifford) = x
  calc
    (g : RadicalLineClifford) * x *
        ((g⁻¹ : RadicalLineCliffordˣ) : RadicalLineClifford) =
      x * ((g : RadicalLineClifford) *
        ((g⁻¹ : RadicalLineCliffordˣ) : RadicalLineClifford)) := by
          rw [radicalLine_mul_comm (g : RadicalLineClifford) x]
          exact Semigroup.mul_assoc x (g : RadicalLineClifford)
            ((g⁻¹ : RadicalLineCliffordˣ) : RadicalLineClifford)
    _ = x := by simp

/-- In a commutative Clifford algebra every set has the full algebra as its
ordinary centralizer. -/
theorem radicalLine_centralizer_eq_univ (S : Set RadicalLineClifford) :
    centralizerSet (0 : QuadraticForm ℝ ℝ) S = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true, centralizerSet]
  intro y hy
  exact radicalLine_mul_comm x y

/-- All four ordinary norm-table carriers in the `Cl_{0,0,1}` model are the
full unit group. -/
theorem radicalLine_ordinary_norm_carriers_eq_univ :
    PaperA01 (0 : QuadraticForm ℝ ℝ) = Set.univ ∧
    PaperA23 (0 : QuadraticForm ℝ ℝ) = Set.univ ∧
    PaperB12 (0 : QuadraticForm ℝ ℝ) = Set.univ ∧
    PaperB03 (0 : QuadraticForm ℝ ℝ) = Set.univ := by
  simp [PaperA01, PaperA23, PaperB12, PaperB03, fixedGradeCentralizer,
    centralizerSet, radicalLine_mul_comm]

/-- Every ordinary-adjoint pair stabilizer is the full unit group in the
`Cl_{0,0,1}` radical example. -/
theorem radicalLine_adjointPairStabilizer_eq_univ (i j : Fin 4) :
    adjointPairStabilizer (0 : QuadraticForm ℝ ℝ) i j = Set.univ := by
  ext g
  change (∀ x, x ∈ (jointPairSubmodule (0 : QuadraticForm ℝ ℝ) i j :
      Set RadicalLineClifford) →
      adjointAction (0 : QuadraticForm ℝ ℝ) g x ∈
        (jointPairSubmodule (0 : QuadraticForm ℝ ℝ) i j :
          Set RadicalLineClifford)) ↔ True
  simp only [iff_true]
  intro x hx
  rw [radicalLine_adjointAction_eq]
  exact hx

/-- Low-dimensional degenerate instance of the ordinary group classifications:
all four geometric stabilizers equal their paper norm-table groups in
`Cl_{0,0,1}`. -/
theorem radicalLine_ordinary_group_classifications :
    adjointPairStabilizer (0 : QuadraticForm ℝ ℝ) 0 1 =
        PaperA01 (0 : QuadraticForm ℝ ℝ) ∧
    adjointPairStabilizer (0 : QuadraticForm ℝ ℝ) 2 3 =
        PaperA23 (0 : QuadraticForm ℝ ℝ) ∧
    adjointPairStabilizer (0 : QuadraticForm ℝ ℝ) 1 2 =
        PaperB12 (0 : QuadraticForm ℝ ℝ) ∧
    adjointPairStabilizer (0 : QuadraticForm ℝ ℝ) 0 3 =
        PaperB03 (0 : QuadraticForm ℝ ℝ) := by
  rcases radicalLine_ordinary_norm_carriers_eq_univ with ⟨hA01, hA23, hB12, hB03⟩
  rw [radicalLine_adjointPairStabilizer_eq_univ,
    radicalLine_adjointPairStabilizer_eq_univ,
    radicalLine_adjointPairStabilizer_eq_univ,
    radicalLine_adjointPairStabilizer_eq_univ,
    hA01, hA23, hB12, hB03]
  simp

/-! ## Two-dimensional radical example -/

/-- The carrier of the paper's `Cl_{0,0,2}` radical-only example. -/
abbrev RadicalPlaneClifford := DegenerateClifford 0 0 2

/-- Exact carrier and homogeneous-grade dimensions for the `Cl_{0,0,2}` row.
These are dimensions of real vector spaces; they do not assert a group
classification. -/
theorem radicalPlane_signature_grade_dimension_table :
    Module.finrank ℝ RadicalPlaneClifford = 4 ∧
    Module.finrank ℝ (fixedGradeCarrier (degenerateSignatureForm 0 0 2) 0) = 1 ∧
    Module.finrank ℝ (fixedGradeCarrier (degenerateSignatureForm 0 0 2) 1) = 2 ∧
    Module.finrank ℝ (fixedGradeCarrier (degenerateSignatureForm 0 0 2) 2) = 1 ∧
    Module.finrank ℝ (fixedGradeCarrier (degenerateSignatureForm 0 0 2) 3) = 0 := by
  have hdim : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change Module.finrank ℝ
      (CliffordAlgebra (degenerateSignatureForm 0 0 2)) = 4
    rw [clifford_finrank_eq_two_pow]
    rw [hdim]
    norm_num
  · rw [fixedGradeCarrier_finrank_eq_choose, hdim]
    norm_num
  · rw [fixedGradeCarrier_finrank_eq_choose, hdim]
    norm_num
  · rw [fixedGradeCarrier_finrank_eq_choose, hdim]
    norm_num
  · rw [fixedGradeCarrier_finrank_eq_choose, hdim]
    norm_num

/-- Grade three vanishes in the two-dimensional radical Clifford algebra. -/
theorem radicalPlane_fixedGradeCarrier3_eq_bot :
    fixedGradeCarrier (degenerateSignatureForm 0 0 2) 3 = ⊥ := by
  exact degenerateSignature_fixedGradeCarrier_eq_bot_of_gt_dimension 0 0 2 3 (by decide)

/-- In `Cl_{0,0,2}`, the checked `Ǎ^{03}` condition reduces to evenness of
the reversion norm: its grade-three centralizer condition is vacuous because
the grade-three carrier is zero. -/
theorem radicalPlane_PaperACheck03_eq_evenNormCarrier :
    PaperACheck03 (degenerateSignatureForm 0 0 2) =
      {g | reversionNorm (degenerateSignatureForm 0 0 2) g ∈
        evenCarrier (degenerateSignatureForm 0 0 2)} := by
  ext g
  simp [PaperACheck03, fixedGradeCentralizer, centralizerSet,
    radicalPlane_fixedGradeCarrier3_eq_bot]

/-- Every even unit belongs to the paper's checked `Ǎ^{03}` carrier in
`Cl_{0,0,2}`. The converse is a separate low-dimensional norm calculation;
this inclusion alone is not the paper's full group classification. -/
theorem radicalPlane_evenUnits_subset_PaperACheck03 :
    {g : RadicalPlaneCliffordˣ |
      CliffordAlgebra.involute (g : RadicalPlaneClifford) = (g : RadicalPlaneClifford)} ⊆
      PaperACheck03 (degenerateSignatureForm 0 0 2) := by
  intro g hg
  rw [radicalPlane_PaperACheck03_eq_evenNormCarrier]
  exact reversionNorm_mem_evenCarrier_of_even
    (Q := degenerateSignatureForm 0 0 2) g hg

/-- The radical plane has an explicit odd unit `1 + e` for a nonzero
square-zero generator `e`; its inverse is `1 - e`. -/
def radicalPlaneOddUnit : RadicalPlaneCliffordˣ := by
  let e : RadicalPlaneClifford := CliffordAlgebra.ι
    (degenerateSignatureForm 0 0 2) (radicalCoordinate 0 0 2 0)
  have he2 : e * e = 0 := by
    dsimp [e]
    simpa [pow_two] using radicalGenerator_sq_zero 0 0 2 0 (by decide)
  refine ⟨1 + e, 1 - e, ?_, ?_⟩ <;> noncomm_ring [he2]

/-- This odd unit is not in the checked `Ǎ^{03}` carrier: its reversion norm
is `1 + 2e`, which is not fixed by grade involution. This proves the
`Cl_{0,0,2}` carrier is a proper subset of the full unit group. -/
theorem radicalPlane_oddUnit_not_PaperACheck03 :
    radicalPlaneOddUnit ∉ PaperACheck03 (degenerateSignatureForm 0 0 2) := by
  let e : RadicalPlaneClifford := CliffordAlgebra.ι
    (degenerateSignatureForm 0 0 2) (radicalCoordinate 0 0 2 0)
  have he2 : e * e = 0 := by
    dsimp [e]
    simpa [pow_two] using radicalGenerator_sq_zero 0 0 2 0 (by decide)
  have he0 : e ≠ 0 := by
    intro he
    have hι : CliffordAlgebra.ι (degenerateSignatureForm 0 0 2)
        (radicalCoordinate 0 0 2 0) = CliffordAlgebra.ι _ 0 := by
      simpa [e] using he
    have hi := InfoGeometry.Clifford.GradedGraceContraction.clifford_ι_injective
      (degenerateSignatureForm 0 0 2) hι
    have hz := congrFun hi 0
    simp [radicalCoordinate] at hz
  have hnorm : reversionNorm (degenerateSignatureForm 0 0 2)
      radicalPlaneOddUnit = 1 + (2 : ℝ) • e := by
    rw [reversionNorm]
    change CliffordAlgebra.reverse ((1 : RadicalPlaneClifford) + e) *
      ((1 : RadicalPlaneClifford) + e) = _
    have hrev : CliffordAlgebra.reverse e = e := by
      dsimp [e]
      exact CliffordAlgebra.reverse_ι _
    simp [hrev]
    noncomm_ring [he2]
    rfl
  rw [radicalPlane_PaperACheck03_eq_evenNormCarrier]
  change CliffordAlgebra.involute
      (reversionNorm (degenerateSignatureForm 0 0 2) radicalPlaneOddUnit) ≠ _
  rw [hnorm]
  intro h
  simp only [map_add, map_one, map_smul] at h
  simp only [e, CliffordAlgebra.involute_ι, smul_neg] at h
  have h' : 1 + (-2 : ℝ) • e = 1 + (2 : ℝ) • e := by
    simpa only [neg_smul] using h
  have hcancel : (-2 : ℝ) • e = (2 : ℝ) • e := add_left_cancel h'
  have hcancel' : -((2 : ℝ) • e) = (2 : ℝ) • e := by
    simpa only [neg_smul] using hcancel
  have hfour : (4 : ℝ) • e = 0 := by
    calc
      (4 : ℝ) • e = (2 : ℝ) • e + (2 : ℝ) • e := by module
      _ = 0 := by
        nth_rewrite 1 [← hcancel']
        exact neg_add_cancel _
  exact he0 ((smul_eq_zero.mp hfour).resolve_left (by norm_num))

/-- The checked `Ǎ^{03}` carrier is a strict subgroup carrier of the full
unit group in `Cl_{0,0,2}`. The exhibited odd unit is the explicit witness
that the carrier is not universal. -/
theorem radicalPlane_PaperACheck03_ne_univ :
    PaperACheck03 (degenerateSignatureForm 0 0 2) ≠ Set.univ := by
  intro h
  have hmem : radicalPlaneOddUnit ∈ PaperACheck03 (degenerateSignatureForm 0 0 2) := by
    rw [h]
    simp
  exact radicalPlane_oddUnit_not_PaperACheck03 hmem

/-- In `Cl_{0,0,2}`, the homogeneous grade-three carrier is zero, so the
paper's ordinary-adjoint norm carrier `B^{03}` is the full unit group. This
is a carrier classification; identifying the joint-type stabilizer with it
still requires a separate action-level proof. -/
theorem radicalPlane_PaperB03_eq_univ :
    PaperB03 (degenerateSignatureForm 0 0 2) = Set.univ := by
  ext g
  simp [PaperB03, fixedGradeCentralizer, centralizerSet,
    radicalPlane_fixedGradeCarrier3_eq_bot]

/-- In the two-generator radical Clifford algebra, Clifford-star-fixed
elements are scalars. The grade projections of degrees one and two vanish by
their negative star sign; the finite grade resolution stops at degree two. -/
theorem radicalPlane_starFixed_eq_scalarRange :
    {x : RadicalPlaneClifford | star x = x} =
      Set.range (algebraMap ℝ RadicalPlaneClifford) := by
  ext x
  constructor
  · intro hx
    let P : ℕ → RadicalPlaneClifford →ₗ[ℝ] RadicalPlaneClifford :=
      InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj
        (degenerateSignatureForm 0 0 2)
    have hproj1 := congrArg (P 1) hx
    rw [InfoGeometry.Clifford.LipschitzWittRieszPrimary.cliffordGradeProj_star_input,
      show (-1 : ℝ) ^ (1 * (1 + 1) / 2) = -1 by norm_num] at hproj1
    have hneg1 : -(P 1 x) = P 1 x := by simpa using hproj1
    have hproj1zero : P 1 x = 0 := by
      have htwo : (2 : ℝ) • P 1 x = 0 := by
        calc
          (2 : ℝ) • P 1 x = P 1 x + P 1 x := by module
          _ = 0 := by
            calc
              P 1 x + P 1 x = P 1 x + -(P 1 x) :=
                congrArg (fun z => P 1 x + z) hneg1.symm
              _ = 0 := add_neg_cancel _
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    have hproj2 := congrArg (P 2) hx
    rw [InfoGeometry.Clifford.LipschitzWittRieszPrimary.cliffordGradeProj_star_input,
      show (-1 : ℝ) ^ (2 * (2 + 1) / 2) = -1 by norm_num] at hproj2
    have hneg2 : -(P 2 x) = P 2 x := by simpa using hproj2
    have hproj2zero : P 2 x = 0 := by
      have htwo : (2 : ℝ) • P 2 x = 0 := by
        calc
          (2 : ℝ) • P 2 x = P 2 x + P 2 x := by module
          _ = 0 := by
            calc
              P 2 x + P 2 x = P 2 x + -(P 2 x) :=
                congrArg (fun z => P 2 x + z) hneg2.symm
              _ = 0 := add_neg_cancel _
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    have hdim : Module.finrank ℝ (Fin (0 + 0 + 2) → ℝ) = 2 := by simp
    have hsum :=
      InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj_sum_range_apply
        (degenerateSignatureForm 0 0 2) x
    change (∑ k ∈ Finset.range (Module.finrank ℝ (Fin 2 → ℝ) + 1), P k x) = x at hsum
    rw [hdim] at hsum
    simp only [Finset.sum_range_succ] at hsum
    simp [hproj1zero, hproj2zero] at hsum
    have hmem0 : P 0 x ∈
        fixedGradeCarrier (degenerateSignatureForm 0 0 2) 0 := by
      rw [fixedGradeCarrier,
        InfoGeometry.Clifford.GradedGraceContraction.mem_cliffordGradeSubmodule_iff]
      exact InfoGeometry.Clifford.GradedGraceContraction.cliffordGradeProj_idem
        (degenerateSignatureForm 0 0 2) 0 x
    have hmem0' : P 0 x ∈
        (Set.range (algebraMap ℝ RadicalPlaneClifford) : Set RadicalPlaneClifford) := by
      rw [← fixedGradeCarrier_zero_eq_scalarRange]
      exact hmem0
    rcases hmem0' with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← hsum, hc]
  · rintro ⟨c, rfl⟩
    simp

/-- The ordinary-adjoint stabilizer of joint types `0⊕3` in `Cl_{0,0,2}` is
the full unit group: the star-fixed sector is scalar, hence every Clifford norm
centralizes it. This closes the action-level `B^{03}` row for this signature. -/
theorem radicalPlane_adjointPairStabilizer_03_eq_univ :
    adjointPairStabilizer (degenerateSignatureForm 0 0 2) 0 3 = Set.univ := by
  rw [adjointPairStabilizer_03_eq_StarFixedNormCarrier]
  unfold StarFixedNormCarrier
  rw [radicalPlane_starFixed_eq_scalarRange]
  ext g
  constructor
  · intro _
    simp
  · intro _
    intro x hx
    rcases hx with ⟨c, rfl⟩
    change cliffordNorm (degenerateSignatureForm 0 0 2) g *
        (algebraMap ℝ RadicalPlaneClifford c) =
      (algebraMap ℝ RadicalPlaneClifford c) *
        cliffordNorm (degenerateSignatureForm 0 0 2) g
    exact (Algebra.commutes c _).symm

/-- In `Cl_{0,0,2}`, the paper's ordinary-adjoint `B^{03}` classification is
an equality of the geometric stabilizer and its homogeneous-grade norm
carrier; both are the full unit group in this degenerate example. -/
theorem radicalPlane_adjointPairStabilizer_03_eq_PaperB03 :
    adjointPairStabilizer (degenerateSignatureForm 0 0 2) 0 3 =
      PaperB03 (degenerateSignatureForm 0 0 2) := by
  rw [radicalPlane_adjointPairStabilizer_03_eq_univ,
    radicalPlane_PaperB03_eq_univ]

end InfoGeometry.Clifford.GeneralizedDegenerateLipschitzArchetypes
