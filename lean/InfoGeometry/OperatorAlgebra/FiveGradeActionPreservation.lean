import Mathlib.Algebra.Algebra.Equiv
import InfoGeometry.OperatorAlgebra.ChiralRetainedWordFiveGradeClosure
import InfoGeometry.OperatorAlgebra.GradeActionInterface

/-!
# Automorphisms of operator grades

An algebra equivalence which fixes the grading element preserves every
eigenspace grade.  This is the common algebraic interface for symmetry lanes;
it does not identify their different concrete carriers or labels.
-/

namespace InfoGeometry.OperatorAlgebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

theorem grade_zero_commutator_preserves
    {N K X : A} {k : ℤ}
    (hK : HasOperatorGrade N K 0)
    (hX : HasOperatorGrade N X k) :
    HasOperatorGrade N (K * X - X * K) k := by
  simpa using grade_commutator hK hX

theorem grade_zero_commutator_mapsToGrade
    (N : A) :
    MapsToGrade
      (fun k : ℤ => (gradeSubmodule N k : Set A))
      (fun K : {X : A // X ∈ gradeSubmodule N 0} =>
        fun X => operatorCommutator K.1 X)
      (fun _ k => k) := by
  intro K k X hX
  exact grade_zero_commutator_preserves
    (N := N) (K := K.1) (X := X) (k := k) K.2 hX

theorem algEquiv_map_mem_gradeSubmodule
    (e : AlgEquiv ℝ A A) (N X : A) (k : ℤ) (hN : e N = N) :
    X ∈ gradeSubmodule N k → e X ∈ gradeSubmodule N k := by
  intro h
  change HasOperatorGrade N X k at h
  change HasOperatorGrade N (e X) k
  unfold HasOperatorGrade at h ⊢
  have he := congrArg e h
  simpa [hN, map_sub, map_mul, map_smul] using he

/-! A grading-reversing equivalence is the canonical permutation case: it
 sends the `k`-eigenspace of `ad N` to the `(-k)`-eigenspace. -/
theorem algEquiv_map_mem_gradeSubmodule_neg
    (e : AlgEquiv ℝ A A) (N X : A) (k : ℤ) (hN : e N = -N) :
    X ∈ gradeSubmodule N k → e X ∈ gradeSubmodule N (-k) := by
  intro h
  change HasOperatorGrade N X k at h
  change HasOperatorGrade N (e X) (-k)
  unfold HasOperatorGrade at h ⊢
  have he := congrArg e h
  have he' := congrArg Neg.neg he
  simpa [hN, map_sub, map_mul, map_smul, neg_mul, mul_neg,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using he'

theorem algEquiv_map_gradeSubmodule_neg
    (e : AlgEquiv ℝ A A) (N : A) (k : ℤ) (hN : e N = -N) :
    Submodule.map e.toLinearMap (gradeSubmodule N k) =
      gradeSubmodule N (-k) := by
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    exact algEquiv_map_mem_gradeSubmodule_neg e N X k hN hX
  · rintro Y hY
    refine ⟨e.symm Y, ?_, ?_⟩
    · have hN' : e.symm N = -N := by
        apply e.injective
        simp [hN]
      have h := algEquiv_map_mem_gradeSubmodule_neg e.symm N Y (-k) hN' hY
      simpa using h
    · simp

theorem algEquiv_map_gradeSubmodule
    (e : AlgEquiv ℝ A A) (N : A) (k : ℤ) (hN : e N = N) :
    Submodule.map e.toLinearMap (gradeSubmodule N k) = gradeSubmodule N k := by
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    exact algEquiv_map_mem_gradeSubmodule e N X k hN hX
  · rintro Y hY
    refine ⟨e.symm Y, ?_, ?_⟩
    · have hN' : e.symm N = N := by
        calc
          e.symm N = e.symm (e N) := by rw [hN]
          _ = N := e.symm_apply_apply N
      exact algEquiv_map_mem_gradeSubmodule e.symm N Y k hN' hY
    · simp

theorem algEquiv_preserves_gradeSubmodule
    (e : AlgEquiv ℝ A A) (N : A) (hN : e N = N) :
    PreservesGrade
      (fun k : ℤ => (gradeSubmodule N k : Set A))
      (fun _ : Unit => fun X => e X) := by
  intro _ k X hX
  exact algEquiv_map_mem_gradeSubmodule e N X k hN hX

/-! The corresponding reflection action is expressed in the same generic
`MapsToGrade` interface.  This is the permutation form used by involutions
which reverse the grading element. -/
theorem algEquiv_mapsTo_gradeSubmodule_neg
    (e : AlgEquiv ℝ A A) (N : A) (hN : e N = -N) :
    MapsToGrade
      (fun k : ℤ => (gradeSubmodule N k : Set A))
      (fun _ : Unit => fun X => e X)
      (fun _ k => -k) := by
  intro _ k X hX
  exact algEquiv_map_mem_gradeSubmodule_neg e N X k hN hX

theorem algEquiv_map_gradeSubmodule_transport
    (e : AlgEquiv ℝ A A) (N : A) (k : ℤ) :
    Submodule.map e.toLinearMap (gradeSubmodule N k) =
      gradeSubmodule (e N) k := by
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    change HasOperatorGrade N X k at hX
    change HasOperatorGrade (e N) (e X) k
    unfold HasOperatorGrade at hX ⊢
    have he := congrArg e hX
    simpa [map_sub, map_mul, map_smul] using he
  · rintro Y hY
    change HasOperatorGrade (e N) Y k at hY
    refine ⟨e.symm Y, ?_, ?_⟩
    · change HasOperatorGrade N (e.symm Y) k
      unfold HasOperatorGrade at hY ⊢
      have he := congrArg e.symm hY
      simpa [map_sub, map_mul, map_smul] using he
    · simp

theorem algEquiv_map_gradeSubmodule_of
    {B : Type*} [Ring B] [Algebra ℝ B]
    (e : A ≃ₐ[ℝ] B) (N : A) (k : ℤ) :
    Submodule.map e.toLinearMap (gradeSubmodule N k) =
      gradeSubmodule (e N) k := by
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    change HasOperatorGrade (e N) (e X) k
    change HasOperatorGrade N X k at hX
    unfold HasOperatorGrade at hX ⊢
    have he := congrArg e hX
    simpa [map_sub, map_mul, map_smul] using he
  · rintro Y hY
    refine ⟨e.symm Y, ?_, ?_⟩
    · change HasOperatorGrade N (e.symm Y) k
      change HasOperatorGrade (e N) Y k at hY
      unfold HasOperatorGrade at hY ⊢
      have he := congrArg e.symm hY
      simpa [map_sub, map_mul, map_smul] using he
    · exact e.apply_symm_apply Y

theorem algEquiv_mapsToGradeSubmoduleBetween
    {B : Type*} [Ring B] [Algebra ℝ B]
    (e : A ≃ₐ[ℝ] B) (N : A) :
    MapsToGradeBetween (α := A) (γ := B)
      (fun k : ℤ => (gradeSubmodule N k : Set A))
      (fun k : ℤ => (gradeSubmodule (e N) k : Set B))
      (fun _ : Unit => e)
      (fun _ k => k) := by
  intro _ k X hX
  change e X ∈ gradeSubmodule (e N) k
  change X ∈ gradeSubmodule N k at hX
  rw [← algEquiv_map_gradeSubmodule_of e N k]
  exact ⟨X, hX, rfl⟩

theorem ringEquiv_map_gradeSubmodule_transport
    (e : A ≃+* A) (N : A) (k : ℤ)
    (hsmul : ∀ c : ℝ, ∀ X : A, e (c • X) = c • e X) :
    ∀ X : A, e X ∈ gradeSubmodule (e N) k ↔
      X ∈ gradeSubmodule N k := by
  intro X
  have hsmul_symm : ∀ c : ℝ, ∀ Y : A,
      e.symm (c • Y) = c • e.symm Y := by
    intro c Y
    apply e.injective
    simp [hsmul]
  constructor
  · intro hX
    change HasOperatorGrade (e N) (e X) k at hX
    change HasOperatorGrade N X k
    unfold HasOperatorGrade at hX ⊢
    have he := congrArg e.symm hX
    simpa [map_sub, map_mul, hsmul, hsmul_symm] using he
  · intro hX
    change HasOperatorGrade N X k at hX
    change HasOperatorGrade (e N) (e X) k
    unfold HasOperatorGrade at hX ⊢
    have he := congrArg e hX
    simpa [map_sub, map_mul, hsmul, hsmul_symm] using he

/-- The additive equivalence underlying a scalar-compatible ring equivalence.

This is deliberately constructed with an explicit scalar-compatibility
hypothesis: a ring equivalence is not definitionally an `ℝ`-linear map.
-/
noncomputable def ringEquivLinearEquiv
    (e : A ≃+* A)
    (hsmul : ∀ c : ℝ, ∀ X : A, e (c • X) = c • e X) : A ≃ₗ[ℝ] A where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' := hsmul

theorem ringEquiv_preserves_gradeSubmodule
    (e : A ≃+* A) (N : A)
    (hsmul : ∀ c : ℝ, ∀ X : A, e (c • X) = c • e X)
    (hN : e N = N) :
    PreservesGrade
      (fun k : ℤ => (gradeSubmodule N k : Set A))
      (fun _ : Unit => fun X => e X) := by
  intro _ k X hX
  simpa [hN] using
    (ringEquiv_map_gradeSubmodule_transport e N k hsmul X).2 hX

theorem ringEquiv_mapsToGradeSubmoduleBetween
    (e : A ≃+* A) (N : A)
    (hsmul : ∀ c : ℝ, ∀ X : A, e (c • X) = c • e X) :
    MapsToGradeBetween
      (fun k : ℤ => (gradeSubmodule N k : Set A))
      (fun k : ℤ => (gradeSubmodule (e N) k : Set A))
      (fun _ : Unit => fun X => e X)
      (fun _ k => k) := by
  intro _ k X hX
  exact (ringEquiv_map_gradeSubmodule_transport e N k hsmul X).2 hX

theorem ringEquiv_symm_mapsToGradeSubmoduleBetween
    (e : A ≃+* A) (N : A)
    (hsmul : ∀ c : ℝ, ∀ X : A, e (c • X) = c • e X) :
    MapsToGradeBetween
      (fun k : ℤ => (gradeSubmodule (e N) k : Set A))
      (fun k : ℤ => (gradeSubmodule N k : Set A))
      (fun _ : Unit => fun X => e.symm X)
      (fun _ k => k) := by
  intro _ k X hX
  have h := (ringEquiv_map_gradeSubmodule_transport e N k hsmul
    (e.symm X)).1 (by simpa using hX)
  simpa using h

theorem ringEquivLinearEquiv_map_gradeSubmodule
    (e : A ≃+* A) (N : A) (k : ℤ)
    (hsmul : ∀ c : ℝ, ∀ X : A, e (c • X) = c • e X) :
    Submodule.map (ringEquivLinearEquiv e hsmul).toLinearMap
        (gradeSubmodule N k) = gradeSubmodule (e N) k := by
  have hsmul_symm : ∀ c : ℝ, ∀ Y : A,
      e.symm (c • Y) = c • e.symm Y := by
    intro c Y
    apply e.injective
    simp [hsmul]
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    exact (ringEquiv_map_gradeSubmodule_transport e N k hsmul X).2 hX
  · rintro Y hY
    refine ⟨e.symm Y, ?_, ?_⟩
    · have htransport := (ringEquiv_map_gradeSubmodule_transport e.symm (e N) k
        hsmul_symm Y).2 hY
      simpa using htransport
    · exact e.apply_symm_apply Y

theorem algEquiv_mem_gradeSubmodule_iff
    (e : AlgEquiv ℝ A A) (N X : A) (k : ℤ) :
    e X ∈ gradeSubmodule (e N) k ↔ X ∈ gradeSubmodule N k := by
  constructor
  · intro h
    change HasOperatorGrade (e N) (e X) k at h
    change HasOperatorGrade N X k
    unfold HasOperatorGrade at h ⊢
    have he := congrArg e.symm h
    simpa [map_sub, map_mul, map_smul] using he
  · intro h
    change HasOperatorGrade N X k at h
    change HasOperatorGrade (e N) (e X) k
    unfold HasOperatorGrade at h ⊢
    have he := congrArg e h
    simpa [map_sub, map_mul, map_smul] using he

theorem algEquiv_map_mem_gradeSubmodule_between_iff
    {B : Type*} [Ring B] [Algebra ℝ B]
    (e : A ≃ₐ[ℝ] B) (N X : A) (k : ℤ) :
    e X ∈ gradeSubmodule (e N) k ↔ X ∈ gradeSubmodule N k := by
  constructor
  · intro h
    change HasOperatorGrade (e N) (e X) k at h
    change HasOperatorGrade N X k
    unfold HasOperatorGrade at h ⊢
    have he := congrArg e.symm h
    simpa [map_sub, map_mul, map_smul] using he
  · intro h
    change HasOperatorGrade N X k at h
    change HasOperatorGrade (e N) (e X) k
    unfold HasOperatorGrade at h ⊢
    have he := congrArg e h
    simpa [map_sub, map_mul, map_smul] using he

theorem algEquiv_symm_mapsGradeSubmoduleBetween
    {B : Type*} [Ring B] [Algebra ℝ B]
    (e : A ≃ₐ[ℝ] B) (N : A) :
    MapsToGradeBetween
      (fun k : ℤ => (gradeSubmodule (e N) k : Set B))
      (fun k : ℤ => (gradeSubmodule N k : Set A))
      (fun _ : Unit => e.symm)
      (fun _ k => k) := by
  intro _ k Y hY
  exact (algEquiv_map_mem_gradeSubmodule_between_iff e N (e.symm Y) k).1 (by
    simpa using hY)

theorem algEquiv_map_commutator_grade
    (e : AlgEquiv ℝ A A) (N X Y : A) (k l : ℤ)
    (hX : HasOperatorGrade N X k) (hY : HasOperatorGrade N Y l) :
    HasOperatorGrade (e N) (e (operatorCommutator X Y)) (k + l) := by
  unfold HasOperatorGrade at hX hY ⊢
  have h := grade_commutator hX hY
  have he := congrArg e h
  simpa [map_sub, map_mul, map_smul] using he

end InfoGeometry.OperatorAlgebra
