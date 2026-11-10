/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import Mathlib.LinearAlgebra.Matrix.Bilinear
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.A2QutritTransitionRootBridge

/-!
# The finite `A₂` root-space decomposition of the qutrit matrix algebra

The six ordered transition matrices span exactly the off-diagonal part of
`M₃(ℂ)`.  This is a concrete decomposition theorem, not an interface or a
supplied representation contract.

#### BUCKET 1: CLOSED FINITE THEOREMS
The diagonal Cartan adjoint action on each transition root and its induced
diagonal action on the complete six-root expansion of an off-diagonal qutrit
matrix.

#### BUCKET 2: CONDITIONAL THEOREMS
None; these are unconditional statements for the concrete `M₃(ℂ)` carrier.

#### BUCKET 3: UNCLAIMED GENERALIZATIONS
No arbitrary noncommutative-ring representation, infinite-dimensional root
space, or Lie-group integration is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.A2QutritCartanDecomposition

open Matrix
open InfoGeometry.Canonical.A2InsideD5RootSubsystem
open InfoGeometry.Canonical.A2QutritTransitionRootBridge

/-- Remove the diagonal Cartan component of a qutrit matrix. -/
def offDiagonalPart (M : InfoGeometry.Algebra.FiniteSpin.QutritMatrix) : InfoGeometry.Algebra.FiniteSpin.QutritMatrix :=
  M - Matrix.diagonal (fun i => M i i)

/-- The linear subspace of qutrit matrices with vanishing diagonal. -/
def offDiagonalSubmodule : Submodule ℂ InfoGeometry.Algebra.FiniteSpin.QutritMatrix where
  carrier := {M | ∀ i, M i i = 0}
  zero_mem' := by
    intro i
    simp
  add_mem' := by
    intro A B hA hB i
    simp [hA i, hB i]
  smul_mem' := by
    intro c A hA i
    simp [hA i]

/-- The diagonal Cartan submodule of the qutrit matrix algebra. -/
def diagonalSubmodule : Submodule ℂ InfoGeometry.Algebra.FiniteSpin.QutritMatrix where
  carrier := {M | ∀ i j, i ≠ j → M i j = 0}
  zero_mem' := by
    intro i j hij
    simp
  add_mem' := by
    intro A B hA hB i j hij
    simp [hA i j hij, hB i j hij]
  smul_mem' := by
    intro c A hA i j hij
    simp [hA i j hij]

/-- The diagonal submodule is linearly equivalent to the three diagonal
coordinate functions. -/
noncomputable def diagonalSubmoduleEquiv :
    diagonalSubmodule ≃ₗ[ℂ] (Fin 3 → ℂ) :=
  { toFun := fun M i => M.1 i i
    invFun := fun v =>
      ⟨Matrix.diagonal v, by
        intro i j hij
        simp [Matrix.diagonal, hij]⟩
    left_inv := by
      intro M
      ext i j
      by_cases h : i = j
      · subst j
        simp [Matrix.diagonal]
      · have hm : M.1 i j = 0 := M.2 i j h
        simp [Matrix.diagonal, h, hm]
    right_inv := by
      intro v
      funext i
      simp [Matrix.diagonal]
    map_add' := by
      intro M N
      funext i
      simp
    map_smul' := by
      intro c M
      funext i
      simp }

/-- The diagonal qutrit subspace has complex dimension three. -/
theorem diagonalSubmodule_finrank :
    Module.finrank ℂ diagonalSubmodule = 3 := by
  calc
    Module.finrank ℂ diagonalSubmodule = Module.finrank ℂ (Fin 3 → ℂ) :=
      diagonalSubmoduleEquiv.finrank_eq
    _ = 3 := by simp

/-- The diagonal projection complementary to `offDiagonalPart`. -/
def diagonalPart (M : InfoGeometry.Algebra.FiniteSpin.QutritMatrix) : InfoGeometry.Algebra.FiniteSpin.QutritMatrix :=
  Matrix.diagonal (fun i => M i i)

/-- Diagonal extraction lands in the diagonal submodule. -/
theorem diagonalPart_mem_diagonalSubmodule (M : InfoGeometry.Algebra.FiniteSpin.QutritMatrix) :
    diagonalPart M ∈ diagonalSubmodule ∧
      ∀ i j, diagonalPart M i j = if i = j then M i i else 0 := by
  constructor
  · intro i j hij
    simp [diagonalPart, Matrix.diagonal, hij]
  · intro i j
    by_cases h : i = j
    · subst j
      simp [diagonalPart, Matrix.diagonal]
    · simp [diagonalPart, Matrix.diagonal, h]

/-- The diagonal extraction is a genuine linear projection. -/
def diagonalPartLinear : InfoGeometry.Algebra.FiniteSpin.QutritMatrix →ₗ[ℂ] InfoGeometry.Algebra.FiniteSpin.QutritMatrix :=
  { toFun := diagonalPart
    map_add' := by
      intro M N
      ext i j
      by_cases h : i = j <;>
        simp [diagonalPart, Matrix.diagonal, h]
    map_smul' := by
      intro (c : ℂ) M
      ext i j
      simp [diagonalPart, Matrix.diagonal] }

@[simp] theorem diagonalPartLinear_apply (M : InfoGeometry.Algebra.FiniteSpin.QutritMatrix) :
    diagonalPartLinear M = diagonalPart M ∧
      ∀ i j, diagonalPartLinear M i j = if i = j then M i i else 0 := by
  constructor
  · rfl
  · intro i j
    by_cases h : i = j
    · subst j
      simp [diagonalPartLinear, diagonalPart, Matrix.diagonal]
    · simp [diagonalPartLinear, diagonalPart, Matrix.diagonal, h]

/-- Applying the diagonal projection twice is the same as applying it once. -/
theorem diagonalPartLinear_idempotent :
    LinearMap.comp (σ₁₂ := RingHom.id ℂ) (σ₂₃ := RingHom.id ℂ)
        (σ₁₃ := RingHom.id ℂ) diagonalPartLinear diagonalPartLinear =
      diagonalPartLinear := by
  apply LinearMap.ext
  intro M
  change diagonalPart (diagonalPart M) = diagonalPart M
  ext i j
  by_cases h : i = j
  · subst j
    simp [diagonalPart, Matrix.diagonal]
  · simp [diagonalPart, Matrix.diagonal, h]

/-- The range of diagonal extraction is exactly the diagonal submodule. -/
theorem diagonalPartLinear_range :
    LinearMap.range diagonalPartLinear = diagonalSubmodule := by
  apply le_antisymm
  · rintro _ ⟨M, rfl⟩
    exact (diagonalPart_mem_diagonalSubmodule M).1
  · intro M hM
    exact ⟨M, by
      ext i j
      by_cases h : i = j
      · subst j
        simp
      · simp [h, hM i j h]
      ⟩

/-- The kernel of diagonal extraction is the off-diagonal submodule. -/
theorem diagonalPartLinear_ker :
    LinearMap.ker diagonalPartLinear = offDiagonalSubmodule := by
  apply le_antisymm
  · intro M hM i
    have hzero : diagonalPart M = 0 := hM
    have hentry := congrArg (fun N : InfoGeometry.Algebra.FiniteSpin.QutritMatrix => N i i) hzero
    simpa [diagonalPart, Matrix.diagonal] using hentry
  · intro M hM
    apply LinearMap.mem_ker.mpr
    ext i j
    by_cases h : i = j
    · subst j
      simp [hM i]
    · simp [h]

/-- Every qutrit matrix is the sum of its diagonal and off-diagonal parts. -/
theorem diagonalPart_add_offDiagonalPart (M : InfoGeometry.Algebra.FiniteSpin.QutritMatrix) :
    diagonalPart M + offDiagonalPart M = M := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [diagonalPart, offDiagonalPart, Matrix.diagonal]
  · simp [diagonalPart, offDiagonalPart, Matrix.diagonal, h]

/-- The diagonal and off-diagonal subspaces together span all qutrit matrices. -/
theorem diagonal_sup_offDiagonal_eq_top :
    diagonalSubmodule ⊔ offDiagonalSubmodule = ⊤ := by
  apply top_unique
  intro M hM
  have hsum : diagonalPart M + offDiagonalPart M ∈
      diagonalSubmodule ⊔ offDiagonalSubmodule := by
    apply add_mem
    · exact (le_sup_left : diagonalSubmodule ≤
        diagonalSubmodule ⊔ offDiagonalSubmodule)
        (diagonalPart_mem_diagonalSubmodule M).1
    · exact (le_sup_right : offDiagonalSubmodule ≤
        diagonalSubmodule ⊔ offDiagonalSubmodule) (by
          intro i
          simp [offDiagonalPart, Matrix.diagonal])
  rw [diagonalPart_add_offDiagonalPart] at hsum
  exact hsum

/-- A matrix that is both diagonal and off-diagonal is zero. -/
theorem diagonal_offDiagonal_disjoint :
    Disjoint diagonalSubmodule offDiagonalSubmodule := by
  refine Submodule.disjoint_def.2 ?_
  intro M hD hO
  ext i j
  by_cases h : i = j
  · subst j
    exact hO i
  · exact hD i j h

/-- A diagonal-plus-off-diagonal decomposition has unique components. -/
theorem diagonal_offDiagonal_decomposition_unique
    {D D' O O' : InfoGeometry.Algebra.FiniteSpin.QutritMatrix}
    (hD : D ∈ diagonalSubmodule)
    (hD' : D' ∈ diagonalSubmodule)
    (hO : O ∈ offDiagonalSubmodule)
    (hO' : O' ∈ offDiagonalSubmodule)
    (hEq : D + O = D' + O') :
    D = D' ∧ O = O' := by
  have hDD : D = D' := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hentry := congrArg (fun M : InfoGeometry.Algebra.FiniteSpin.QutritMatrix => M i i) hEq
      simpa [hO i, hO' i] using hentry
    · have hentry := congrArg (fun M : InfoGeometry.Algebra.FiniteSpin.QutritMatrix => M i j) hEq
      simp [hD i j hij, hD' i j hij] at hentry ⊢
  have hOO : O = O' := by
    rw [hDD] at hEq
    exact add_left_cancel hEq
  exact ⟨hDD, hOO⟩

/-- Every ordered-root transition matrix is off-diagonal. -/
theorem transitionMatrix_mem_offDiagonalSubmodule (r : A2Root) :
    transitionMatrix r ∈ offDiagonalSubmodule := by
  intro i
  simp only [transitionMatrix, Matrix.single]
  by_cases h : r.1.1 = i
  · have hne : r.1.2 ≠ i := by
      intro hi
      exact r.property (h.trans hi.symm)
    simp [h, hne]
  · simp [h]

/-- Off-diagonal extraction lands in the off-diagonal submodule. -/
theorem offDiagonalPart_mem_offDiagonalSubmodule (M : InfoGeometry.Algebra.FiniteSpin.QutritMatrix) :
    offDiagonalPart M ∈ offDiagonalSubmodule ∧
      ∀ i j, offDiagonalPart M i j = if i = j then 0 else M i j := by
  constructor
  · intro i
    simp [offDiagonalPart, Matrix.diagonal]
  · intro i j
    by_cases h : i = j
    · subst j
      simp [offDiagonalPart, Matrix.diagonal]
    · simp [offDiagonalPart, Matrix.diagonal, h]

/-- Extraction fixes matrices whose diagonal entries already vanish. -/
theorem offDiagonalPart_eq_self_of_mem {M : InfoGeometry.Algebra.FiniteSpin.QutritMatrix}
    (hM : M ∈ offDiagonalSubmodule) :
    offDiagonalPart M = M := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [offDiagonalPart, Matrix.diagonal, hM i]
  · simp [offDiagonalPart, Matrix.diagonal, h]

/-- Off-diagonal extraction is idempotent. -/
theorem offDiagonalPart_idempotent (M : InfoGeometry.Algebra.FiniteSpin.QutritMatrix) :
    offDiagonalPart (offDiagonalPart M) = offDiagonalPart M := by
  exact offDiagonalPart_eq_self_of_mem
    (offDiagonalPart_mem_offDiagonalSubmodule M).1

/-- The off-diagonal extraction is a genuine linear projection. -/
def offDiagonalPartLinear : InfoGeometry.Algebra.FiniteSpin.QutritMatrix →ₗ[ℂ] InfoGeometry.Algebra.FiniteSpin.QutritMatrix :=
  { toFun := offDiagonalPart
    map_add' := by
      intro M N
      ext i j
      by_cases h : i = j <;>
        simp [offDiagonalPart, Matrix.diagonal, sub_eq_add_neg, h]
    map_smul' := by
      intro (c : ℂ) M
      ext i j
      by_cases h : i = j <;>
        simp [offDiagonalPart, Matrix.diagonal, sub_eq_add_neg, h] }

@[simp] theorem offDiagonalPartLinear_apply (M : InfoGeometry.Algebra.FiniteSpin.QutritMatrix) :
    offDiagonalPartLinear M = offDiagonalPart M ∧
      ∀ i j, offDiagonalPartLinear M i j = if i = j then 0 else M i j := by
  constructor
  · rfl
  · intro i j
    by_cases h : i = j
    · subst j
      simp [offDiagonalPartLinear, offDiagonalPart, Matrix.diagonal]
    · simp [offDiagonalPartLinear, offDiagonalPart, Matrix.diagonal, h]

/-- The off-diagonal linear projection is idempotent. -/
theorem offDiagonalPartLinear_idempotent :
    offDiagonalPartLinear.comp offDiagonalPartLinear = offDiagonalPartLinear := by
  apply LinearMap.ext
  intro M
  change offDiagonalPart (offDiagonalPart M) = offDiagonalPart M
  exact offDiagonalPart_idempotent M

/-- The range of the off-diagonal projection is exactly its submodule. -/
theorem offDiagonalPartLinear_range :
    LinearMap.range offDiagonalPartLinear = offDiagonalSubmodule := by
  apply le_antisymm
  · rintro _ ⟨M, rfl⟩
    exact (offDiagonalPart_mem_offDiagonalSubmodule M).1
  · intro M hM
    exact ⟨M, offDiagonalPart_eq_self_of_mem hM⟩

/-- The kernel of off-diagonal extraction is the diagonal submodule. -/
theorem offDiagonalPartLinear_ker :
    LinearMap.ker offDiagonalPartLinear = diagonalSubmodule := by
  apply le_antisymm
  · intro M hM i j hij
    have hzero : offDiagonalPart M = 0 := hM
    have hentry := congrArg (fun N : InfoGeometry.Algebra.FiniteSpin.QutritMatrix => N i j) hzero
    simpa [offDiagonalPart, Matrix.diagonal, hij] using hentry
  · intro M hM
    apply LinearMap.mem_ker.mpr
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, hM i j hij]

/-- The two complementary projections sum to the identity map. -/
theorem diagonalPartLinear_add_offDiagonalPartLinear :
    diagonalPartLinear + offDiagonalPartLinear =
      (LinearMap.id : InfoGeometry.Algebra.FiniteSpin.QutritMatrix →ₗ[ℂ] InfoGeometry.Algebra.FiniteSpin.QutritMatrix) := by
  apply LinearMap.ext
  intro M
  simpa [diagonalPartLinear, offDiagonalPartLinear] using
    diagonalPart_add_offDiagonalPart M

/-- Extracting a diagonal part after an off-diagonal part gives zero. -/
theorem diagonalPartLinear_comp_offDiagonalPartLinear :
    diagonalPartLinear.comp offDiagonalPartLinear =
      (0 : InfoGeometry.Algebra.FiniteSpin.QutritMatrix →ₗ[ℂ] InfoGeometry.Algebra.FiniteSpin.QutritMatrix) := by
  apply LinearMap.ext
  intro M
  change diagonalPartLinear (offDiagonalPartLinear M) = 0
  change diagonalPart (offDiagonalPart M) = 0
  ext i j
  by_cases h : i = j
  · subst j
    simp [diagonalPart, offDiagonalPart, Matrix.diagonal]
  · simp [diagonalPart, Matrix.diagonal, h]

/-- Extracting an off-diagonal part after a diagonal part gives zero. -/
theorem offDiagonalPartLinear_comp_diagonalPartLinear :
    offDiagonalPartLinear.comp diagonalPartLinear =
      (0 : InfoGeometry.Algebra.FiniteSpin.QutritMatrix →ₗ[ℂ] InfoGeometry.Algebra.FiniteSpin.QutritMatrix) := by
  apply LinearMap.ext
  intro M
  change offDiagonalPartLinear (diagonalPartLinear M) = 0
  change offDiagonalPart (diagonalPart M) = 0
  ext i j
  by_cases h : i = j
  · subst j
    simp [offDiagonalPart, diagonalPart, Matrix.diagonal]
  · simp [offDiagonalPart, diagonalPart, Matrix.diagonal, h]

/-- The three cyclic forward transitions and their three opposite transitions
give the complete off-diagonal matrix part. -/
theorem transition_root_decomposition (M : InfoGeometry.Algebra.FiniteSpin.QutritMatrix) :
    (∑ i : Fin 3,
        M (rootFromIndex i).1.1 (rootFromIndex i).1.2 •
          transitionMatrix (rootFromIndex i)) +
      (∑ i : Fin 3,
        M (oppositeRoot (rootFromIndex i)).1.1
            (oppositeRoot (rootFromIndex i)).1.2 •
          transitionMatrix (oppositeRoot (rootFromIndex i))) =
      offDiagonalPart M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiagonalPart, transitionMatrix, oppositeRoot, rootFromIndex,
      next3, Fin.sum_univ_three, Matrix.single, Matrix.diagonal]

/-- The Cartan diagonal plus the six `A₂` transition directions reconstruct
every qutrit matrix. -/
theorem cartan_plus_transition_decomposition (M : InfoGeometry.Algebra.FiniteSpin.QutritMatrix) :
    Matrix.diagonal (fun i => M i i) +
        ((∑ i : Fin 3,
            M (rootFromIndex i).1.1 (rootFromIndex i).1.2 •
              transitionMatrix (rootFromIndex i)) +
          (∑ i : Fin 3,
            M (oppositeRoot (rootFromIndex i)).1.1
                (oppositeRoot (rootFromIndex i)).1.2 •
              transitionMatrix (oppositeRoot (rootFromIndex i)))) = M := by
  rw [transition_root_decomposition]
  ext i j
  by_cases h : i = j
  · subst j
    simp [offDiagonalPart, Matrix.diagonal]
  · simp [offDiagonalPart, Matrix.diagonal, h]

/-- The six ordered `A₂` transitions are linearly independent over `ℂ`. -/
theorem transitionMatrix_linearIndependent :
    LinearIndependent ℂ (transitionMatrix : A2Root → InfoGeometry.Algebra.FiniteSpin.QutritMatrix) := by
  rw [Fintype.linearIndependent_iff]
  intro c h r
  have hentry := congrArg (fun M : InfoGeometry.Algebra.FiniteSpin.QutritMatrix => M r.1.1 r.1.2) h
  change (∑ s : A2Root, c s • transitionMatrix s r.1.1 r.1.2) = 0 at hentry
  have hzero : ∀ s : A2Root, s ≠ r →
      c s • transitionMatrix s r.1.1 r.1.2 = 0 := by
    intro s hsr
    by_cases h₁ : s.1.1 = r.1.1
    · by_cases h₂ : s.1.2 = r.1.2
      · exact False.elim (hsr (Subtype.ext (Prod.ext h₁ h₂)))
      · simp [transitionMatrix, Matrix.single, h₁, h₂]
    · simp [transitionMatrix, Matrix.single, h₁]
  rw [Finset.sum_eq_single_of_mem r (Finset.mem_univ r)
    (fun s _ hsr => hzero s hsr)] at hentry
  simpa [transitionMatrix] using hentry

/-- The six transition matrices span precisely the off-diagonal submodule. -/
theorem span_transitionMatrix_eq_offDiagonalSubmodule :
    Submodule.span ℂ (Set.range transitionMatrix) = offDiagonalSubmodule := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨r, rfl⟩
    exact transitionMatrix_mem_offDiagonalSubmodule r
  · intro M hM
    have hsum :
        (∑ i : Fin 3,
            M (rootFromIndex i).1.1 (rootFromIndex i).1.2 •
              transitionMatrix (rootFromIndex i)) +
          (∑ i : Fin 3,
            M (oppositeRoot (rootFromIndex i)).1.1
                (oppositeRoot (rootFromIndex i)).1.2 •
              transitionMatrix (oppositeRoot (rootFromIndex i))) ∈
        Submodule.span ℂ (Set.range transitionMatrix) := by
      apply add_mem
      · apply Submodule.sum_mem
        intro i hi
        apply Submodule.smul_mem
        exact Submodule.subset_span ⟨rootFromIndex i, rfl⟩
      · apply Submodule.sum_mem
        intro i hi
        apply Submodule.smul_mem
        exact Submodule.subset_span
          ⟨oppositeRoot (rootFromIndex i), rfl⟩
    rw [transition_root_decomposition] at hsum
    rw [show offDiagonalPart M = M by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [offDiagonalPart, Matrix.diagonal, hM i]
      · simp [offDiagonalPart, Matrix.diagonal, hij]] at hsum
    exact hsum

/-- The off-diagonal qutrit subspace has complex dimension six. -/
theorem offDiagonalSubmodule_finrank :
    Module.finrank ℂ offDiagonalSubmodule = 6 := by
  rw [← span_transitionMatrix_eq_offDiagonalSubmodule]
  rw [finrank_span_eq_card transitionMatrix_linearIndependent]
  have hcard : Fintype.card {x : Fin 3 × Fin 3 // x.1 = x.2} = 3 := by
    decide
  simp [hcard]

/-- The full qutrit matrix space has complex dimension nine, obtained as the
sum of the three diagonal and six off-diagonal dimensions in its direct
decomposition. -/
theorem qutritMatrix_finrank :
    Module.finrank ℂ InfoGeometry.Algebra.FiniteSpin.QutritMatrix = 9 := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    diagonalSubmodule offDiagonalSubmodule
  rw [diagonal_offDiagonal_disjoint.eq_bot, finrank_bot,
    diagonalSubmodule_finrank, offDiagonalSubmodule_finrank, add_zero] at hdim
  rw [← finrank_top ℂ InfoGeometry.Algebra.FiniteSpin.QutritMatrix, ← diagonal_sup_offDiagonal_eq_top]
  exact hdim

/-- The root transition matrix, viewed as an element of the off-diagonal
submodule. -/
def offDiagonalTransition (r : A2Root) : offDiagonalSubmodule :=
  ⟨transitionMatrix r, transitionMatrix_mem_offDiagonalSubmodule r⟩

/-- The six root transitions are linearly independent in the off-diagonal
submodule. -/
theorem offDiagonalTransition_linearIndependent :
    LinearIndependent ℂ offDiagonalTransition := by
  rw [Fintype.linearIndependent_iff]
  intro c h r
  have hval := congrArg
    (fun M : offDiagonalSubmodule => (M : InfoGeometry.Algebra.FiniteSpin.QutritMatrix)) h
  change (∑ s : A2Root, c s • transitionMatrix s) = 0 at hval
  exact (Fintype.linearIndependent_iff.mp transitionMatrix_linearIndependent)
    c hval r

/-- The root transitions span the entire off-diagonal submodule. -/
theorem offDiagonalTransition_span_eq_top :
    Submodule.span ℂ (Set.range offDiagonalTransition) = ⊤ := by
  letI : Nonempty A2Root := ⟨rootFromIndex 0⟩
  apply offDiagonalTransition_linearIndependent.span_eq_top_of_card_eq_finrank
  rw [card_a2Root, offDiagonalSubmodule_finrank]

/-- The root transitions form a basis of the off-diagonal submodule. -/
noncomputable def offDiagonalBasis :
    Module.Basis A2Root ℂ offDiagonalSubmodule :=
  letI : Nonempty A2Root := ⟨rootFromIndex 0⟩
  basisOfLinearIndependentOfCardEqFinrank
    offDiagonalTransition_linearIndependent (by
      rw [card_a2Root, offDiagonalSubmodule_finrank])

/-- The coefficient of root direction `r` in the off-diagonal basis. -/
def offDiagonalCoefficient (M : offDiagonalSubmodule) (r : A2Root) : ℂ :=
  (offDiagonalBasis.repr M) r

/-- The basis vector at a root is the corresponding transition matrix, and its
coordinates are the Kronecker delta in the six-root basis. -/
@[simp] theorem offDiagonalBasis_apply (r : A2Root) :
    offDiagonalBasis r = offDiagonalTransition r ∧
      ∀ s : A2Root,
        offDiagonalCoefficient (offDiagonalTransition r) s = if r = s then 1 else 0 := by
  have hbasis : offDiagonalBasis r = offDiagonalTransition r := by
    simp [offDiagonalBasis]
  constructor
  · exact hbasis
  · intro s
    rw [← hbasis]
    simpa [offDiagonalCoefficient] using offDiagonalBasis.repr_self_apply r s

/-- The adjoint action of a diagonal Cartan matrix on qutrit matrices, bundled
as a linear map so that its action on the whole root basis can be stated. -/
def diagonalCartanAdjointLinear (h : Fin 3 → ℂ) :
    InfoGeometry.Algebra.FiniteSpin.QutritMatrix →ₗ[ℂ] InfoGeometry.Algebra.FiniteSpin.QutritMatrix :=
  mulLeftLinearMap (Fin 3) ℂ (diagonalCartan h) -
    mulRightLinearMap (Fin 3) ℂ (diagonalCartan h)

/-- Every off-diagonal matrix is the sum of its six root-basis components. -/
theorem offDiagonal_expansion (M : offDiagonalSubmodule) :
    ∑ r : A2Root,
        offDiagonalCoefficient M r • offDiagonalTransition r = M := by
  simpa [offDiagonalCoefficient] using
    Module.Basis.sum_repr offDiagonalBasis M

/-- The coefficients in the six-root expansion are unique. -/
theorem offDiagonal_expansion_unique (M : offDiagonalSubmodule)
    (c : A2Root → ℂ)
    (h : ∑ r : A2Root, c r • offDiagonalTransition r = M) :
    ∀ r, c r = offDiagonalCoefficient M r := by
  have hzero :
      ∑ r : A2Root,
          (c r - offDiagonalCoefficient M r) • offDiagonalTransition r = 0 := by
    calc
      ∑ r : A2Root,
          (c r - offDiagonalCoefficient M r) • offDiagonalTransition r =
          (∑ r : A2Root, c r • offDiagonalTransition r) -
            (∑ r : A2Root,
              offDiagonalCoefficient M r • offDiagonalTransition r) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        exact sub_smul (c r) (offDiagonalCoefficient M r)
          (offDiagonalTransition r)
      _ = M - M := by rw [h, offDiagonal_expansion]
      _ = 0 := sub_self M
  have hcoeff :=
    (Fintype.linearIndependent_iff.mp offDiagonalTransition_linearIndependent)
      (fun r => c r - offDiagonalCoefficient M r) hzero
  intro r
  exact sub_eq_zero.mp (hcoeff r)

/-- Root eigenvalues determine the full diagonal action of the Cartan
commutator on every off-diagonal matrix through its six-root expansion. -/
theorem diagonalCartan_root_eigenvalue
    (h : Fin 3 → ℂ) :
    (∀ r : A2Root,
      diagonalCartan h * transitionMatrix r -
          transitionMatrix r * diagonalCartan h =
        (h r.1.1 - h r.1.2) • transitionMatrix r) ∧
    (∀ M : offDiagonalSubmodule,
      diagonalCartanAdjointLinear h M.1 =
        ∑ r : A2Root,
          ((h r.1.1 - h r.1.2) * offDiagonalCoefficient M r) •
            transitionMatrix r) := by
  constructor
  · intro r
    exact diagonalCartan_comm_transitionMatrix h r
  · intro M
    have hM := congrArg (fun A : offDiagonalSubmodule => (A : InfoGeometry.Algebra.FiniteSpin.QutritMatrix))
      (offDiagonal_expansion M)
    rw [← hM]
    change diagonalCartanAdjointLinear h
      (∑ r : A2Root,
        offDiagonalCoefficient M r • transitionMatrix r) = _
    rw [map_sum]
    simp only [map_smul]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [diagonalCartanAdjointLinear, LinearMap.sub_apply,
      mulLeftLinearMap_apply, mulRightLinearMap_apply,
      diagonalCartan_comm_transitionMatrix]
    rw [smul_smul, mul_comm]

/-- The opposite root has the reversed Cartan weight and is the transpose
matrix unit of the original root. -/
theorem diagonalCartan_opposite_root_eigenvalue
    (h : Fin 3 → ℂ) (r : A2Root) :
    diagonalCartan h * transitionMatrix (oppositeRoot r) -
        transitionMatrix (oppositeRoot r) * diagonalCartan h =
      (h r.1.2 - h r.1.1) • transitionMatrix (oppositeRoot r) ∧
    transitionMatrix (oppositeRoot r) =
      Matrix.transpose (transitionMatrix r) := by
  constructor
  · simpa [oppositeRoot] using
      (diagonalCartan_comm_transitionMatrix h (oppositeRoot r))
  · ext i j
    simp [transitionMatrix, oppositeRoot, Matrix.transpose, Matrix.single,
      and_comm]

end InfoGeometry.Canonical.A2QutritCartanDecomposition

end noncomputable section
