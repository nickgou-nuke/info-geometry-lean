/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.HilbertSchmidt
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Linarith

/-!
# Four orthogonal sectors of a full bipartite matrix algebra

The scalar, traceless-left, and traceless-right sectors are explicit submodules
of the full complex matrix algebra. Their Hilbert–Schmidt orthogonal complement
is the mixed sector. These are linear sectors, not multiplicative factors.
The construction works for arbitrary nonempty finite index types and proves
the dimension of the mixed sector. It makes no entanglement-generation claim.
-/

noncomputable section

namespace InfoGeometry.Quantum.BipartiteOperatorSectors

open Matrix
open scoped Kronecker ComplexOrder
open InfoGeometry.OperatorAlgebra.PeirceSuperoperators

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

local instance {ι : Type*} [Fintype ι] [DecidableEq ι] :
    NormedAddCommGroup (Matrix ι ι ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance {ι : Type*} [Fintype ι] [DecidableEq ι] :
    InnerProductSpace ℂ (Matrix ι ι ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

/-- The trace-zero linear subspace of the full matrix algebra. -/
def traceZero (ι : Type*) [Fintype ι] : Submodule ℂ (Matrix ι ι ℂ) :=
  LinearMap.ker (Matrix.traceLinearMap ι ℂ ℂ)

omit [DecidableEq m] in
@[simp] theorem mem_traceZero (A : Matrix m m ℂ) :
    A ∈ traceZero m ↔ Matrix.trace A = 0 := Iff.rfl

/-- The left tensor-factor embedding, retaining every matrix entry. -/
def leftLift : Matrix m m ℂ →ₗ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix n n ℂ)
  map_add' A B := Matrix.add_kronecker A B 1
  map_smul' c A := Matrix.smul_kronecker c A 1

/-- The right tensor-factor embedding. -/
def rightLift : Matrix n n ℂ →ₗ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun B := (1 : Matrix m m ℂ) ⊗ₖ B
  map_add' A B := Matrix.kronecker_add 1 A B
  map_smul' c A := Matrix.kronecker_smul c 1 A

omit [Fintype m] [DecidableEq m] [Fintype n] in
@[simp] theorem leftLift_apply (A : Matrix m m ℂ) :
    leftLift (n := n) A = A ⊗ₖ (1 : Matrix n n ℂ) := rfl

omit [Fintype m] [Fintype n] [DecidableEq n] in
@[simp] theorem rightLift_apply (B : Matrix n n ℂ) :
    rightLift (m := m) B = (1 : Matrix m m ℂ) ⊗ₖ B := rfl

/-- The scalar identity sector. -/
def scalarSector : Submodule ℂ (Matrix (m × n) (m × n) ℂ) :=
  ℂ ∙ (1 : Matrix (m × n) (m × n) ℂ)

/-- Local left operators with their scalar part removed. -/
def leftSector : Submodule ℂ (Matrix (m × n) (m × n) ℂ) :=
  (traceZero m).map leftLift

/-- Local right operators with their scalar part removed. -/
def rightSector : Submodule ℂ (Matrix (m × n) (m × n) ℂ) :=
  (traceZero n).map rightLift

/-- The complete sum of scalar and local operator directions. -/
def localSector : Submodule ℂ (Matrix (m × n) (m × n) ℂ) :=
  scalarSector ⊔ leftSector ⊔ rightSector

/-- The mixed sector is a Hilbert–Schmidt orthogonal complement. -/
def mixedSector : Submodule ℂ (Matrix (m × n) (m × n) ℂ) :=
  (localSector (m := m) (n := n))ᗮ

/-- Hilbert–Schmidt pairing factorizes on Kronecker products. -/
theorem inner_kronecker (A C : Matrix m m ℂ) (B D : Matrix n n ℂ) :
    inner ℂ (A ⊗ₖ B) (C ⊗ₖ D) = inner ℂ A C * inner ℂ B D := by
  simp only [hs_inner_eq_trace, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

omit [DecidableEq m] [DecidableEq n] in
/-- Row-major vectorization preserves both ordered matrix actions. The
transpose on the right factor is essential. -/
theorem kronecker_bimodule_action (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (X : Matrix m n ℂ) :
    (A ⊗ₖ Bᵀ) *ᵥ Matrix.vec Xᵀ = Matrix.vec (A * X * B)ᵀ := by
  simp only [Matrix.kronecker_mulVec_vec, Matrix.transpose_mul, Matrix.mul_assoc]

/-- The whole bipartite matrix algebra represents all linear superoperators
on rectangular matrices, via native currying and matrix representation. -/
def operatorEquiv : Matrix (m × n) (m × n) ℂ ≃ₗ[ℂ]
    Module.End ℂ (Matrix m n ℂ) :=
  Matrix.toLinAlgEquiv'.toLinearEquiv.trans (LinearEquiv.curry ℂ ℂ m n).conj

theorem operatorEquiv_apply (T : Matrix (m × n) (m × n) ℂ) (X : Matrix m n ℂ) :
    operatorEquiv T X = fun i j => (T *ᵥ Matrix.vec Xᵀ) (i, j) := rfl

/-- The representation respects the noncommutative product of arbitrary operators. -/
theorem operatorEquiv_mul (T U : Matrix (m × n) (m × n) ℂ) :
    operatorEquiv (T * U) = operatorEquiv T * operatorEquiv U := by
  change (LinearEquiv.curry ℂ ℂ m n).conj (Matrix.toLinAlgEquiv' (T * U)) = _
  rw [map_mul]
  exact (LinearEquiv.curry ℂ ℂ m n).conj_comp
    (Matrix.toLinAlgEquiv' U) (Matrix.toLinAlgEquiv' T)

/-- The represented pure product is the actual ordered bimodule operation. -/
theorem operatorEquiv_kronecker_apply (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (X : Matrix m n ℂ) :
    operatorEquiv (A ⊗ₖ Bᵀ) X = A * X * B := by
  rw [operatorEquiv_apply, kronecker_bimodule_action]
  rfl

theorem scalar_orthogonal_left :
    (scalarSector (m := m) (n := n)).IsOrtho leftSector := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro X hX Y hY
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hX
  obtain ⟨A, hA, rfl⟩ := hY
  simp [inner_smul_left, hs_inner_eq_trace, Matrix.trace_kronecker,
    (mem_traceZero A).mp hA]

theorem scalar_orthogonal_right :
    (scalarSector (m := m) (n := n)).IsOrtho rightSector := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro X hX Y hY
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hX
  obtain ⟨B, hB, rfl⟩ := hY
  simp [inner_smul_left, hs_inner_eq_trace, Matrix.trace_kronecker,
    (mem_traceZero B).mp hB]

theorem left_orthogonal_right :
    (leftSector (m := m) (n := n)).IsOrtho rightSector := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro X hX Y hY
  obtain ⟨A, hA, rfl⟩ := hX
  obtain ⟨B, hB, rfl⟩ := hY
  change inner ℂ (A ⊗ₖ (1 : Matrix n n ℂ)) ((1 : Matrix m m ℂ) ⊗ₖ B) = 0
  rw [inner_kronecker]
  simp [hs_inner_eq_trace, (mem_traceZero B).mp hB]

/-- All three local sectors are orthogonal to the mixed sector. -/
theorem local_orthogonal_mixed :
    (localSector (m := m) (n := n)).IsOrtho mixedSector :=
  Submodule.isOrtho_orthogonal_right _

/-- Both traceless factors place a product in the mixed sector. -/
theorem kronecker_mem_mixed {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : Matrix.trace A = 0) (hB : Matrix.trace B = 0) :
    A ⊗ₖ B ∈ mixedSector := by
  change A ⊗ₖ B ∈
    (scalarSector (m := m) (n := n) ⊔ leftSector (m := m) (n := n) ⊔
      rightSector (m := m) (n := n))ᗮ
  rw [← Submodule.inf_orthogonal, ← Submodule.inf_orthogonal]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro X hX
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hX
    simp [inner_smul_left, hs_inner_eq_trace, Matrix.trace_kronecker, hA]
  · intro X hX
    obtain ⟨C, hC, rfl⟩ := hX
    change inner ℂ (C ⊗ₖ (1 : Matrix n n ℂ)) (A ⊗ₖ B) = 0
    rw [inner_kronecker]
    simp [hs_inner_eq_trace, hB]
  · intro X hX
    obtain ⟨D, hD, rfl⟩ := hX
    change inner ℂ ((1 : Matrix m m ℂ) ⊗ₖ D) (A ⊗ₖ B) = 0
    rw [inner_kronecker]
    simp [hs_inner_eq_trace, hA]

/-- The four sectors exhaust the full bipartite operator space. -/
theorem four_sector_sup :
    scalarSector (m := m) (n := n) ⊔ leftSector ⊔ rightSector ⊔ mixedSector = ⊤ :=
  (localSector (m := m) (n := n)).isCompl_orthogonal.sup_eq_top

/-- Adding four actual sector elements as a native linear map. -/
def sectorSum :
    ((scalarSector (m := m) (n := n) × leftSector (m := m) (n := n)) ×
      (rightSector (m := m) (n := n) × mixedSector (m := m) (n := n))) →ₗ[ℂ]
      Matrix (m × n) (m × n) ℂ :=
  ((scalarSector (m := m) (n := n)).subtype.coprod
    (leftSector (m := m) (n := n)).subtype).coprod
    ((rightSector (m := m) (n := n)).subtype.coprod
      (mixedSector (m := m) (n := n)).subtype)

private theorem sectorSum_injective :
    Function.Injective (sectorSum (m := m) (n := n)) := by
  have hsm : (scalarSector (m := m) (n := n)).IsOrtho mixedSector :=
    local_orthogonal_mixed.mono_left (le_sup_of_le_left le_sup_left)
  have hlm : (leftSector (m := m) (n := n)).IsOrtho mixedSector :=
    local_orthogonal_mixed.mono_left (le_sup_of_le_left le_sup_right)
  have hrm : (rightSector (m := m) (n := n)).IsOrtho mixedSector :=
    local_orthogonal_mixed.mono_left le_sup_right
  have hpair : (scalarSector (m := m) (n := n) ⊔ leftSector).IsOrtho
      (rightSector ⊔ mixedSector) := by
    exact Submodule.isOrtho_sup_left.mpr
      ⟨Submodule.isOrtho_sup_right.mpr ⟨scalar_orthogonal_right, hsm⟩,
       Submodule.isOrtho_sup_right.mpr ⟨left_orthogonal_right, hlm⟩⟩
  have hleft : Disjoint
      (LinearMap.range (scalarSector (m := m) (n := n)).subtype)
      (LinearMap.range (leftSector (m := m) (n := n)).subtype) := by
    simpa only [Submodule.range_subtype] using
      (scalar_orthogonal_left (m := m) (n := n)).disjoint
  have hright : Disjoint
      (LinearMap.range (rightSector (m := m) (n := n)).subtype)
      (LinearMap.range (mixedSector (m := m) (n := n)).subtype) := by
    simpa only [Submodule.range_subtype] using hrm.disjoint
  have houter : Disjoint
      (LinearMap.range
        ((scalarSector (m := m) (n := n)).subtype.coprod
          (leftSector (m := m) (n := n)).subtype))
      (LinearMap.range
        ((rightSector (m := m) (n := n)).subtype.coprod
          (mixedSector (m := m) (n := n)).subtype)) := by
    simpa only [LinearMap.range_coprod, Submodule.range_subtype] using hpair.disjoint
  rw [← LinearMap.ker_eq_bot]
  unfold sectorSum
  rw [LinearMap.ker_coprod_of_disjoint_range _ _ houter,
    LinearMap.ker_coprod_of_disjoint_range _ _ hleft,
    LinearMap.ker_coprod_of_disjoint_range _ _ hright]
  simp

private theorem sectorSum_surjective :
    Function.Surjective (sectorSum (m := m) (n := n)) := by
  rw [← LinearMap.range_eq_top]
  simp only [sectorSum, LinearMap.range_coprod, Submodule.range_subtype]
  simpa only [sup_assoc] using four_sector_sup (m := m) (n := n)

/-- A constructed linear equivalence, with inverse giving the unique four components. -/
def sectorEquiv :
    ((scalarSector (m := m) (n := n) × leftSector (m := m) (n := n)) ×
      (rightSector (m := m) (n := n) × mixedSector (m := m) (n := n))) ≃ₗ[ℂ]
      Matrix (m × n) (m × n) ℂ :=
  LinearEquiv.ofBijective (sectorSum (m := m) (n := n))
    ⟨sectorSum_injective, sectorSum_surjective⟩

/-- Existence and uniqueness refer to actual submodule elements, not supplied projectors. -/
theorem existsUnique_four_components (X : Matrix (m × n) (m × n) ℂ) :
    ∃! q : ((scalarSector (m := m) (n := n) × leftSector (m := m) (n := n)) ×
        (rightSector (m := m) (n := n) × mixedSector (m := m) (n := n))),
      (q.1.1 : Matrix (m × n) (m × n) ℂ) +
        (q.1.2 : Matrix (m × n) (m × n) ℂ) +
        ((q.2.1 : Matrix (m × n) (m × n) ℂ) +
          (q.2.2 : Matrix (m × n) (m × n) ℂ)) = X :=
  (sectorEquiv (m := m) (n := n)).bijective.existsUnique X

section Dimensions

variable [Nonempty m] [Nonempty n]

omit [Fintype m] [DecidableEq m] [Fintype n] [Nonempty m] in
theorem leftLift_injective : Function.Injective (leftLift (m := m) (n := n)) := by
  intro A B h
  let j : n := Classical.arbitrary n
  ext i k
  have hentry := congrArg (fun X => X (i, j) (k, j)) h
  simpa [leftLift] using hentry

omit [Fintype m] [Fintype n] [DecidableEq n] [Nonempty n] in
theorem rightLift_injective : Function.Injective (rightLift (m := m) (n := n)) := by
  intro A B h
  let i : m := Classical.arbitrary m
  ext j k
  have hentry := congrArg (fun X => X (i, j) (i, k)) h
  simpa [rightLift] using hentry

omit [Fintype m] [Fintype n] [Nonempty m] in
/-- The full tensor-factor ranges intersect in precisely their common
scalar sector. The center is not a disjoint third algebra. -/
theorem local_ranges_inf_eq_scalarSector :
    LinearMap.range (leftLift (m := m) (n := n)) ⊓
      LinearMap.range (rightLift (m := m) (n := n)) = scalarSector := by
  ext X
  constructor
  · rintro ⟨⟨A, rfl⟩, ⟨B, hB⟩⟩
    let j : n := Classical.arbitrary n
    have hA : A = B j j • (1 : Matrix m m ℂ) := by
      ext i k
      have he := congrArg (fun T => T (i, j) (k, j)) hB
      simpa [leftLift, rightLift, mul_comm] using he.symm
    apply Submodule.mem_span_singleton.mpr
    refine ⟨B j j, ?_⟩
    simp [hA, leftLift]
  · intro hX
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hX
    constructor
    · refine ⟨c • (1 : Matrix m m ℂ), ?_⟩
      simp [leftLift]
    · refine ⟨c • (1 : Matrix n n ℂ), ?_⟩
      simp [rightLift]

omit [Fintype n] in
/-- Removing the scalar trace part exhausts the left local range. -/
theorem range_leftLift_eq :
    LinearMap.range (leftLift (m := m) (n := n)) = scalarSector ⊔ leftSector := by
  apply le_antisymm
  · rintro X ⟨A, rfl⟩
    let c : ℂ := Matrix.trace A / Fintype.card m
    have hm : (Fintype.card m : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have htr : A - c • (1 : Matrix m m ℂ) ∈ traceZero m := by
      simp [mem_traceZero, c, hm]
    apply Submodule.mem_sup.mpr
    refine ⟨c • 1, Submodule.mem_span_singleton.mpr ⟨c, rfl⟩,
      leftLift (n := n) (A - c • 1), ⟨A - c • 1, htr, rfl⟩, ?_⟩
    rw [map_sub, map_smul]
    have hone : leftLift (n := n) (1 : Matrix m m ℂ) = 1 := by simp [leftLift]
    rw [hone]
    abel
  · apply sup_le
    · rw [← local_ranges_inf_eq_scalarSector]
      exact inf_le_left
    · exact LinearMap.map_le_range

omit [Fintype m] [Nonempty m] in
/-- Removing the scalar trace part exhausts the right local range. -/
theorem range_rightLift_eq :
    LinearMap.range (rightLift (m := m) (n := n)) = scalarSector ⊔ rightSector := by
  apply le_antisymm
  · rintro X ⟨B, rfl⟩
    let c : ℂ := Matrix.trace B / Fintype.card n
    have hn : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have htr : B - c • (1 : Matrix n n ℂ) ∈ traceZero n := by
      simp [mem_traceZero, c, hn]
    apply Submodule.mem_sup.mpr
    refine ⟨c • 1, Submodule.mem_span_singleton.mpr ⟨c, rfl⟩,
      rightLift (m := m) (B - c • 1), ⟨B - c • 1, htr, rfl⟩, ?_⟩
    rw [map_sub, map_smul]
    have hone : rightLift (m := m) (1 : Matrix n n ℂ) = 1 := by simp [rightLift]
    rw [hone]
    abel
  · apply sup_le
    · rw [← local_ranges_inf_eq_scalarSector]
      exact inf_le_right
    · exact LinearMap.map_le_range

/-- The mixed sector is precisely the complement of both full local ranges. -/
theorem mixedSector_eq_local_ranges_orthogonal :
    mixedSector (m := m) (n := n) =
      (LinearMap.range (leftLift (m := m) (n := n)) ⊔
        LinearMap.range (rightLift (m := m) (n := n)))ᗮ := by
  rw [range_leftLift_eq, range_rightLift_eq]
  unfold mixedSector localSector
  rw [sup_sup_sup_comm, sup_idem, sup_assoc]

theorem finrank_traceZero :
    Module.finrank ℂ (traceZero m) = Fintype.card m ^ 2 - 1 := by
  have hsurj : Function.Surjective (Matrix.traceLinearMap m ℂ ℂ) := by
    intro z
    refine ⟨(z / Fintype.card m) • (1 : Matrix m m ℂ), ?_⟩
    have hn : (Fintype.card m : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [Matrix.trace_one, hn]
  have hdim := (Matrix.traceLinearMap m ℂ ℂ).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj] at hdim
  simp only [finrank_top, Module.finrank_self, Module.finrank_matrix,
    mul_one] at hdim
  change Module.finrank ℂ (LinearMap.ker (Matrix.traceLinearMap m ℂ ℂ)) = _
  rw [pow_two]
  omega

theorem finrank_scalarSector :
    Module.finrank ℂ (scalarSector (m := m) (n := n)) = 1 :=
  finrank_span_singleton (one_ne_zero : (1 : Matrix (m × n) (m × n) ℂ) ≠ 0)

omit [Fintype n] in
theorem finrank_leftSector :
    Module.finrank ℂ (leftSector (m := m) (n := n)) = Fintype.card m ^ 2 - 1 := by
  change Module.finrank ℂ ((traceZero m).map (leftLift (m := m) (n := n))) = _
  rw [← (Submodule.equivMapOfInjective (leftLift (m := m) (n := n))
    leftLift_injective (traceZero m)).finrank_eq]
  exact finrank_traceZero

omit [Fintype m] in
theorem finrank_rightSector :
    Module.finrank ℂ (rightSector (m := m) (n := n)) = Fintype.card n ^ 2 - 1 := by
  change Module.finrank ℂ ((traceZero n).map (rightLift (m := m) (n := n))) = _
  rw [← (Submodule.equivMapOfInjective (rightLift (m := m) (n := n))
    rightLift_injective (traceZero n)).finrank_eq]
  exact finrank_traceZero

/-- The omitted mixed dimension is the product of the two traceless dimensions. -/
theorem finrank_mixedSector :
    Module.finrank ℂ (mixedSector (m := m) (n := n)) =
      (Fintype.card m ^ 2 - 1) * (Fintype.card n ^ 2 - 1) := by
  have hdim := (sectorEquiv (m := m) (n := n)).finrank_eq
  simp only [Module.finrank_prod, finrank_scalarSector, finrank_leftSector,
    finrank_rightSector, Module.finrank_matrix, Module.finrank_self,
    Fintype.card_prod, mul_one] at hdim
  have hm : 1 ≤ Fintype.card m ^ 2 := by
    have := Fintype.card_pos (α := m)
    nlinarith
  have hn : 1 ≤ Fintype.card n ^ 2 := by
    have := Fintype.card_pos (α := n)
    nlinarith
  have hcalc :
      1 + (Fintype.card m ^ 2 - 1) +
        ((Fintype.card n ^ 2 - 1) +
          (Fintype.card m ^ 2 - 1) * (Fintype.card n ^ 2 - 1)) =
        (Fintype.card m * Fintype.card n) *
          (Fintype.card m * Fintype.card n) := by
    calc
      _ = ((Fintype.card m ^ 2 - 1) + 1) *
          ((Fintype.card n ^ 2 - 1) + 1) := by
        simp only [add_mul, mul_add, mul_one, one_mul]
        omega
      _ = Fintype.card m ^ 2 * Fintype.card n ^ 2 := by
        rw [Nat.sub_add_cancel hm, Nat.sub_add_cancel hn]
      _ = _ := by rw [← mul_pow, pow_two]
  omega

/-- Both factors of dimension at least two leave a nonzero mixed sector. -/
theorem mixedSector_ne_bot (hm : 2 ≤ Fintype.card m) (hn : 2 ≤ Fintype.card n) :
    mixedSector (m := m) (n := n) ≠ ⊥ := by
  intro hzero
  have hdim := finrank_mixedSector (m := m) (n := n)
  rw [hzero, finrank_bot] at hdim
  have hmsq : 1 < Fintype.card m ^ 2 := by nlinarith [hm]
  have hnsq : 1 < Fintype.card n ^ 2 := by nlinarith [hn]
  have hmpos : 0 < Fintype.card m ^ 2 - 1 := Nat.sub_pos_of_lt hmsq
  have hnpos : 0 < Fintype.card n ^ 2 - 1 := Nat.sub_pos_of_lt hnsq
  have := Nat.mul_pos hmpos hnpos
  omega

end Dimensions

end InfoGeometry.Quantum.BipartiteOperatorSectors
