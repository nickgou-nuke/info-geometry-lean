import Mathlib
import InfoGeometry.Canonical.A2QutritTransitionRootBridge

/-!
# The finite `A₂` root-space decomposition of the qutrit matrix algebra

The six ordered transition matrices span exactly the off-diagonal part of
`M₃(ℂ)`.  This is a concrete decomposition theorem, not an interface or a
supplied representation contract.
-/

noncomputable section

namespace InfoGeometry.Canonical.A2QutritCartanDecomposition

open Matrix
open InfoGeometry.Canonical.A2InsideD5RootSubsystem
open InfoGeometry.Canonical.A2QutritTransitionRootBridge

abbrev QutritMatrix := Matrix (Fin 3) (Fin 3) ℂ

/-- Remove the diagonal Cartan component of a qutrit matrix. -/
def offDiagonalPart (M : QutritMatrix) : QutritMatrix :=
  M - Matrix.diagonal (fun i => M i i)

/-- The linear subspace of qutrit matrices with vanishing diagonal. -/
def offDiagonalSubmodule : Submodule ℂ QutritMatrix where
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
def diagonalSubmodule : Submodule ℂ QutritMatrix where
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

theorem diagonalSubmodule_finrank :
    Module.finrank ℂ diagonalSubmodule = 3 := by
  calc
    Module.finrank ℂ diagonalSubmodule = Module.finrank ℂ (Fin 3 → ℂ) :=
      diagonalSubmoduleEquiv.finrank_eq
    _ = 3 := by simp

theorem qutritMatrix_finrank :
    Module.finrank ℂ QutritMatrix = 9 := by
  simp [QutritMatrix, Module.finrank_matrix, Fintype.card_fin]

/-- The diagonal projection complementary to `offDiagonalPart`. -/
def diagonalPart (M : QutritMatrix) : QutritMatrix :=
  Matrix.diagonal (fun i => M i i)

theorem diagonalPart_mem_diagonalSubmodule (M : QutritMatrix) :
    diagonalPart M ∈ diagonalSubmodule := by
  intro i j hij
  simp [diagonalPart, Matrix.diagonal, hij]

/-- The diagonal extraction is a genuine linear projection. -/
def diagonalPartLinear : QutritMatrix →ₗ[ℂ] QutritMatrix :=
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

@[simp] theorem diagonalPartLinear_apply (M : QutritMatrix) :
    diagonalPartLinear M = diagonalPart M := rfl

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

theorem diagonalPartLinear_range :
    LinearMap.range diagonalPartLinear = diagonalSubmodule := by
  apply le_antisymm
  · rintro _ ⟨M, rfl⟩
    exact diagonalPart_mem_diagonalSubmodule M
  · intro M hM
    exact ⟨M, by
      ext i j
      by_cases h : i = j
      · subst j
        simp [diagonalPart, Matrix.diagonal]
      · simp [diagonalPart, Matrix.diagonal, h, hM i j h]
      ⟩

theorem diagonalPartLinear_ker :
    LinearMap.ker diagonalPartLinear = offDiagonalSubmodule := by
  apply le_antisymm
  · intro M hM i
    have hzero : diagonalPart M = 0 := hM
    have hentry := congrArg (fun N : QutritMatrix => N i i) hzero
    simpa [diagonalPart, Matrix.diagonal] using hentry
  · intro M hM
    apply LinearMap.mem_ker.mpr
    ext i j
    by_cases h : i = j
    · subst j
      simp [diagonalPart, Matrix.diagonal, hM i]
    · simp [diagonalPart, Matrix.diagonal, h]

theorem diagonalPart_add_offDiagonalPart (M : QutritMatrix) :
    diagonalPart M + offDiagonalPart M = M := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [diagonalPart, offDiagonalPart, Matrix.diagonal]
  · simp [diagonalPart, offDiagonalPart, Matrix.diagonal, h]

theorem diagonal_sup_offDiagonal_eq_top :
    diagonalSubmodule ⊔ offDiagonalSubmodule = ⊤ := by
  apply top_unique
  intro M hM
  have hsum : diagonalPart M + offDiagonalPart M ∈
      diagonalSubmodule ⊔ offDiagonalSubmodule := by
    apply add_mem
    · exact (le_sup_left : diagonalSubmodule ≤
        diagonalSubmodule ⊔ offDiagonalSubmodule)
        (diagonalPart_mem_diagonalSubmodule M)
    · exact (le_sup_right : offDiagonalSubmodule ≤
        diagonalSubmodule ⊔ offDiagonalSubmodule) (by
          intro i
          simp [offDiagonalPart, Matrix.diagonal])
  rw [diagonalPart_add_offDiagonalPart] at hsum
  exact hsum

theorem diagonal_offDiagonal_disjoint :
    Disjoint diagonalSubmodule offDiagonalSubmodule := by
  refine Submodule.disjoint_def.2 ?_
  intro M hD hO
  ext i j
  by_cases h : i = j
  · subst j
    exact hO i
  · exact hD i j h

theorem diagonal_offDiagonal_decomposition_unique
    {D D' O O' : QutritMatrix}
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
      have hentry := congrArg (fun M : QutritMatrix => M i i) hEq
      simpa [hO i, hO' i] using hentry
    · have hentry := congrArg (fun M : QutritMatrix => M i j) hEq
      simpa [hD i j hij, hD' i j hij] using hentry
  have hOO : O = O' := by
    rw [hDD] at hEq
    exact add_left_cancel hEq
  exact ⟨hDD, hOO⟩

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

theorem offDiagonalPart_mem_offDiagonalSubmodule (M : QutritMatrix) :
    offDiagonalPart M ∈ offDiagonalSubmodule := by
  intro i
  simp [offDiagonalPart, Matrix.diagonal]

theorem offDiagonalPart_eq_self_of_mem {M : QutritMatrix}
    (hM : M ∈ offDiagonalSubmodule) :
    offDiagonalPart M = M := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [offDiagonalPart, Matrix.diagonal, hM i]
  · simp [offDiagonalPart, Matrix.diagonal, h]

theorem offDiagonalPart_idempotent (M : QutritMatrix) :
    offDiagonalPart (offDiagonalPart M) = offDiagonalPart M := by
  exact offDiagonalPart_eq_self_of_mem
    (offDiagonalPart_mem_offDiagonalSubmodule M)

/-- The off-diagonal extraction is a genuine linear projection. -/
def offDiagonalPartLinear : QutritMatrix →ₗ[ℂ] QutritMatrix :=
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

@[simp] theorem offDiagonalPartLinear_apply (M : QutritMatrix) :
    offDiagonalPartLinear M = offDiagonalPart M := rfl

theorem offDiagonalPartLinear_idempotent :
    offDiagonalPartLinear.comp offDiagonalPartLinear = offDiagonalPartLinear := by
  apply LinearMap.ext
  intro M
  change offDiagonalPart (offDiagonalPart M) = offDiagonalPart M
  exact offDiagonalPart_idempotent M

theorem offDiagonalPartLinear_range :
    LinearMap.range offDiagonalPartLinear = offDiagonalSubmodule := by
  apply le_antisymm
  · rintro _ ⟨M, rfl⟩
    exact offDiagonalPart_mem_offDiagonalSubmodule M
  · intro M hM
    exact ⟨M, offDiagonalPart_eq_self_of_mem hM⟩

theorem offDiagonalPartLinear_ker :
    LinearMap.ker offDiagonalPartLinear = diagonalSubmodule := by
  apply le_antisymm
  · intro M hM i j hij
    have hzero : offDiagonalPart M = 0 := hM
    have hentry := congrArg (fun N : QutritMatrix => N i j) hzero
    simpa [offDiagonalPart, Matrix.diagonal, hij] using hentry
  · intro M hM
    apply LinearMap.mem_ker.mpr
    ext i j
    by_cases hij : i = j
    · subst j
      simp [offDiagonalPart, Matrix.diagonal]
    · simp [offDiagonalPart, Matrix.diagonal, hij, hM i j hij]

theorem diagonalPartLinear_add_offDiagonalPartLinear :
    diagonalPartLinear + offDiagonalPartLinear =
      (LinearMap.id : QutritMatrix →ₗ[ℂ] QutritMatrix) := by
  apply LinearMap.ext
  intro M
  simpa [diagonalPartLinear_apply, offDiagonalPartLinear_apply] using
    diagonalPart_add_offDiagonalPart M

theorem diagonalPartLinear_comp_offDiagonalPartLinear :
    diagonalPartLinear.comp offDiagonalPartLinear =
      (0 : QutritMatrix →ₗ[ℂ] QutritMatrix) := by
  apply LinearMap.ext
  intro M
  change diagonalPartLinear (offDiagonalPartLinear M) = 0
  rw [diagonalPartLinear_apply, offDiagonalPartLinear_apply]
  ext i j
  by_cases h : i = j
  · subst j
    simp [diagonalPart, offDiagonalPart, Matrix.diagonal]
  · simp [diagonalPart, Matrix.diagonal, h]

theorem offDiagonalPartLinear_comp_diagonalPartLinear :
    offDiagonalPartLinear.comp diagonalPartLinear =
      (0 : QutritMatrix →ₗ[ℂ] QutritMatrix) := by
  apply LinearMap.ext
  intro M
  change offDiagonalPartLinear (diagonalPartLinear M) = 0
  rw [offDiagonalPartLinear_apply, diagonalPartLinear_apply]
  ext i j
  by_cases h : i = j
  · subst j
    simp [offDiagonalPart, diagonalPart, Matrix.diagonal]
  · simp [offDiagonalPart, diagonalPart, Matrix.diagonal, h]

/-- The three cyclic forward transitions and their three opposite transitions
give the complete off-diagonal matrix part. -/
theorem transition_root_decomposition (M : QutritMatrix) :
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
theorem cartan_plus_transition_decomposition (M : QutritMatrix) :
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
    LinearIndependent ℂ (transitionMatrix : A2Root → QutritMatrix) := by
  rw [Fintype.linearIndependent_iff]
  intro c h r
  have hentry := congrArg (fun M : QutritMatrix => M r.1.1 r.1.2) h
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

theorem offDiagonalSubmodule_finrank :
    Module.finrank ℂ offDiagonalSubmodule = 6 := by
  rw [← span_transitionMatrix_eq_offDiagonalSubmodule]
  rw [finrank_span_eq_card transitionMatrix_linearIndependent]
  have hcard : Fintype.card {x : Fin 3 × Fin 3 // x.1 = x.2} = 3 := by
    native_decide
  simp [hcard]

def offDiagonalTransition (r : A2Root) : offDiagonalSubmodule :=
  ⟨transitionMatrix r, transitionMatrix_mem_offDiagonalSubmodule r⟩

theorem offDiagonalTransition_linearIndependent :
    LinearIndependent ℂ offDiagonalTransition := by
  rw [Fintype.linearIndependent_iff]
  intro c h r
  have hval := congrArg
    (fun M : offDiagonalSubmodule => (M : QutritMatrix)) h
  change (∑ s : A2Root, c s • transitionMatrix s) = 0 at hval
  exact (Fintype.linearIndependent_iff.mp transitionMatrix_linearIndependent)
    c hval r

theorem offDiagonalTransition_span_eq_top :
    Submodule.span ℂ (Set.range offDiagonalTransition) = ⊤ := by
  letI : Nonempty A2Root := ⟨rootFromIndex 0⟩
  apply offDiagonalTransition_linearIndependent.span_eq_top_of_card_eq_finrank
  rw [card_a2Root, offDiagonalSubmodule_finrank]

noncomputable def offDiagonalBasis :
    Module.Basis A2Root ℂ offDiagonalSubmodule :=
  letI : Nonempty A2Root := ⟨rootFromIndex 0⟩
  basisOfLinearIndependentOfCardEqFinrank
    offDiagonalTransition_linearIndependent (by
      rw [card_a2Root, offDiagonalSubmodule_finrank])

@[simp] theorem offDiagonalBasis_apply (r : A2Root) :
    offDiagonalBasis r = offDiagonalTransition r := by
  simp [offDiagonalBasis]

def offDiagonalCoefficient (M : offDiagonalSubmodule) (r : A2Root) : ℂ :=
  (offDiagonalBasis.repr M) r

theorem offDiagonal_expansion (M : offDiagonalSubmodule) :
    ∑ r : A2Root,
        offDiagonalCoefficient M r • offDiagonalTransition r = M := by
  simpa [offDiagonalCoefficient] using
    Module.Basis.sum_repr offDiagonalBasis M

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

theorem diagonalCartan_root_eigenvalue
    (h : Fin 3 → ℂ) (r : A2Root) :
    diagonalCartan h * transitionMatrix r -
        transitionMatrix r * diagonalCartan h =
      (h r.1.1 - h r.1.2) • transitionMatrix r := by
  exact diagonalCartan_comm_transitionMatrix h r

theorem diagonalCartan_opposite_root_eigenvalue
    (h : Fin 3 → ℂ) (r : A2Root) :
    diagonalCartan h * transitionMatrix (oppositeRoot r) -
        transitionMatrix (oppositeRoot r) * diagonalCartan h =
      (h r.1.2 - h r.1.1) • transitionMatrix (oppositeRoot r) := by
  simpa [oppositeRoot] using
    (diagonalCartan_comm_transitionMatrix h (oppositeRoot r))

end InfoGeometry.Canonical.A2QutritCartanDecomposition

end noncomputable section
