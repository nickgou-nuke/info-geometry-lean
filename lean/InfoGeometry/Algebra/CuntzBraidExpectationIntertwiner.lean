import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge

/-!
# Cuntz permutation/expectation bridge

This file constructs the genuine algebraic action of finite label permutations
on the Cuntz quotient.  It records the action on arbitrary Cuntz words and its
global compatibility with the algebraic expectation.  The permutation action
is a symmetric-group reference sector: involutive generators have trivial
monodromy.  No Spin-space intertwiner, Yang--Baxter operator,
C*-completion, localized endomorphism, or Jones-type structure is asserted.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzBraidExpectationIntertwiner

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzConditionalExpectation
open InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge

variable {n : ℕ}

/-! ## The genuine finite permutation algebra map -/

def permGen (σ : Equiv.Perm (Fin n)) : CuntzGen n → CuntzGen n :=
  fun g => (σ g.1, g.2)

def permFree (σ : Equiv.Perm (Fin n)) : CuntzFree n →ₗ[ℂ] CuntzFree n where
  toFun v := Finsupp.mapDomain (permGen σ) v
  map_add' _ _ := Finsupp.mapDomain_add
  map_smul' c v := by
    simpa using (Finsupp.mapDomain_smul (f := permGen σ) c v)

def permFreeToCuntz (σ : Equiv.Perm (Fin n)) :
    CuntzFree n →ₗ[ℂ] CuntzAlg n :=
  (cuntzMk n).toLinearMap.comp
    ((TensorAlgebra.ι ℂ).comp (permFree σ))

def permTensorAlgHom (σ : Equiv.Perm (Fin n)) :
    CuntzTensor n →ₐ[ℂ] CuntzAlg n :=
  TensorAlgebra.lift ℂ (permFreeToCuntz σ)

@[simp] theorem permTensorAlgHom_S (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permTensorAlgHom σ (S n i) = cuntzS n (σ i) := by
  simp [permTensorAlgHom, permFreeToCuntz, permFree, permGen, S, gen,
    cuntzS, TensorAlgebra.lift_ι_apply]

@[simp] theorem permTensorAlgHom_Sdag (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permTensorAlgHom σ (Sdag n i) = cuntzSdag n (σ i) := by
  simp [permTensorAlgHom, permFreeToCuntz, permFree, permGen, Sdag, gen,
    cuntzSdag, TensorAlgebra.lift_ι_apply]

theorem permTensorAlgHom_rel (σ : Equiv.Perm (Fin n))
    {x y : CuntzTensor n} (h : CuntzRel n x y) :
    permTensorAlgHom σ x = permTensorAlgHom σ y := by
  rcases h with (⟨i, j⟩ | hsum)
  · by_cases hij : i = j
    · subst j
      simp [cuntz_orthogonality]
    · have hσ : σ i ≠ σ j := σ.injective.ne hij
      simp only [map_mul, permTensorAlgHom_Sdag, permTensorAlgHom_S]
      rw [cuntz_distinct_orthogonal n hσ]
      rw [if_neg hij]
      simp
  · simp only [map_sum, map_mul, permTensorAlgHom_S, permTensorAlgHom_Sdag]
    calc
      (∑ i : Fin n, cuntzS n (σ i) * cuntzSdag n (σ i)) =
          ∑ i : Fin n, cuntzS n i * cuntzSdag n i := by
            exact Equiv.sum_comp σ
              (fun i : Fin n => cuntzS n i * cuntzSdag n i)
      _ = 1 := cuntz_ranges_sum_one n
      _ = permTensorAlgHom σ 1 := by simp

def permCuntzAlgHom (σ : Equiv.Perm (Fin n)) :
    CuntzAlg n →ₐ[ℂ] CuntzAlg n :=
  RingQuot.liftAlgHom ℂ ⟨permTensorAlgHom σ, by
    intro x y h
    exact permTensorAlgHom_rel σ h⟩

@[simp] theorem permCuntzAlgHom_mk
    (σ : Equiv.Perm (Fin n)) (x : CuntzTensor n) :
    permCuntzAlgHom σ (cuntzMk n x) = permTensorAlgHom σ x := by
  simp [permCuntzAlgHom, cuntzMk]

theorem permFree_comp (σ τ : Equiv.Perm (Fin n)) (v : CuntzFree n) :
    permFree σ (permFree τ v) = permFree (σ * τ) v := by
  change Finsupp.mapDomain (permGen σ)
      (Finsupp.mapDomain (permGen τ) v) =
    Finsupp.mapDomain (permGen (σ * τ)) v
  rw [← Finsupp.mapDomain_comp]
  congr 1

theorem permCuntzAlgHom_permTensor (σ τ : Equiv.Perm (Fin n))
    (x : CuntzTensor n) :
    permCuntzAlgHom σ (permTensorAlgHom τ x) =
      permTensorAlgHom (σ * τ) x := by
  induction x using TensorAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
      simp only [permTensorAlgHom, TensorAlgebra.lift_ι_apply,
        permFreeToCuntz, LinearMap.comp_apply]
      change permCuntzAlgHom σ
          (cuntzMk n (TensorAlgebra.ι ℂ (permFree τ v))) = _
      rw [permCuntzAlgHom_mk]
      simp only [permTensorAlgHom, TensorAlgebra.lift_ι_apply,
        permFreeToCuntz, LinearMap.comp_apply]
      change cuntzMk n (TensorAlgebra.ι ℂ
          (permFree σ (permFree τ v))) = _
      rw [permFree_comp]
      rfl
  | mul x y hx hy => simp [hx, hy]
  | add x y hx hy => simp [hx, hy]

theorem permCuntzAlgHom_comp (σ τ : Equiv.Perm (Fin n)) :
    (permCuntzAlgHom σ).comp (permCuntzAlgHom τ) =
      permCuntzAlgHom (σ * τ) := by
  apply AlgHom.ext
  intro z
  rcases RingQuot.mkAlgHom_surjective ℂ (CuntzRel n) z with ⟨x, rfl⟩
  change permCuntzAlgHom σ (permCuntzAlgHom τ (cuntzMk n x)) =
    permCuntzAlgHom (σ * τ) (cuntzMk n x)
  rw [permCuntzAlgHom_mk, permCuntzAlgHom_mk]
  exact permCuntzAlgHom_permTensor σ τ x

theorem permCuntzAlgHom_one :
    permCuntzAlgHom (1 : Equiv.Perm (Fin n)) = AlgHom.id ℂ (CuntzAlg n) := by
  apply AlgHom.ext
  intro z
  rcases RingQuot.mkAlgHom_surjective ℂ (CuntzRel n) z with ⟨x, rfl⟩
  change permCuntzAlgHom 1 (cuntzMk n x) = cuntzMk n x
  rw [permCuntzAlgHom_mk]
  induction x using TensorAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
      have hfree : permFree (1 : Equiv.Perm (Fin n)) v = v := by
        change Finsupp.mapDomain (permGen (1 : Equiv.Perm (Fin n))) v = v
        rw [show permGen (1 : Equiv.Perm (Fin n)) = id by
          funext g; rfl, Finsupp.mapDomain_id]
      simp [permTensorAlgHom, permFreeToCuntz, hfree]
  | mul x y hx hy => simp [hx, hy]
  | add x y hx hy => simp [hx, hy]

theorem permCuntzAlgHom_comp_symm (σ : Equiv.Perm (Fin n)) :
    (permCuntzAlgHom σ).comp (permCuntzAlgHom σ.symm) =
      AlgHom.id ℂ (CuntzAlg n) := by
  rw [← permCuntzAlgHom_one (n := n), ← Equiv.Perm.mul_symm]
  exact permCuntzAlgHom_comp σ σ.symm

theorem permCuntzAlgHom_symm_comp (σ : Equiv.Perm (Fin n)) :
    (permCuntzAlgHom σ.symm).comp (permCuntzAlgHom σ) =
      AlgHom.id ℂ (CuntzAlg n) := by
  rw [← permCuntzAlgHom_one (n := n), ← Equiv.Perm.symm_mul]
  exact permCuntzAlgHom_comp σ.symm σ

/-- The finite label permutation is an actual algebra automorphism. -/
def permCuntzAlgEquiv (σ : Equiv.Perm (Fin n)) :
    CuntzAlg n ≃ₐ[ℂ] CuntzAlg n :=
  AlgEquiv.ofAlgHom (permCuntzAlgHom σ) (permCuntzAlgHom σ.symm)
    (permCuntzAlgHom_comp_symm σ) (permCuntzAlgHom_symm_comp σ)

@[simp] theorem permCuntzAlgEquiv_apply
    (σ : Equiv.Perm (Fin n)) (x : CuntzAlg n) :
    permCuntzAlgEquiv σ x = permCuntzAlgHom σ x := rfl

theorem permCuntzAlgEquiv_trans
    (σ τ : Equiv.Perm (Fin n)) :
    (permCuntzAlgEquiv σ).trans (permCuntzAlgEquiv τ) =
      permCuntzAlgEquiv (τ * σ) := by
  apply AlgEquiv.ext
  intro z
  change permCuntzAlgHom τ (permCuntzAlgHom σ z) =
    permCuntzAlgHom (τ * σ) z
  rw [← AlgHom.comp_apply, permCuntzAlgHom_comp]

/-! ## The concrete finite braid shadow on three Cuntz labels -/

def braidPerm : Fin 2 → Equiv.Perm (Fin 3)
  | 0 => Equiv.swap 0 1
  | 1 => Equiv.swap 1 2

def cuntzBraidGenerator (i : Fin 2) : CuntzAlg 3 ≃ₐ[ℂ] CuntzAlg 3 :=
  permCuntzAlgEquiv (braidPerm i)

theorem braidPerm_artin :
    braidPerm 0 * braidPerm 1 * braidPerm 0 =
      braidPerm 1 * braidPerm 0 * braidPerm 1 := by
  native_decide

theorem cuntzBraidGenerator_artin :
    (cuntzBraidGenerator 0).trans
        ((cuntzBraidGenerator 1).trans (cuntzBraidGenerator 0)) =
      (cuntzBraidGenerator 1).trans
        ((cuntzBraidGenerator 0).trans (cuntzBraidGenerator 1)) := by
  simp only [cuntzBraidGenerator, permCuntzAlgEquiv_trans]
  congr 1
  exact braidPerm_artin

/-- The finite label permutation action packaged as a monoid representation. -/
def permCuntzAction : Equiv.Perm (Fin n) →*
    (CuntzAlg n ≃ₐ[ℂ] CuntzAlg n) where
  toFun σ := permCuntzAlgEquiv σ
  map_one' := by
    ext x
    simpa [permCuntzAlgEquiv_apply] using
      congrArg (fun f : CuntzAlg n →ₐ[ℂ] CuntzAlg n => f x)
        (permCuntzAlgHom_one (n := n))
  map_mul' := by
    intro σ τ
    ext x
    rw [AlgEquiv.mul_apply]
    simpa [permCuntzAlgEquiv_apply] using
      (congrArg (fun f : CuntzAlg n →ₐ[ℂ] CuntzAlg n => f x)
        (permCuntzAlgHom_comp σ τ)).symm

@[simp] theorem permCuntzAction_apply
    (σ : Equiv.Perm (Fin n)) (x : CuntzAlg n) :
    permCuntzAction σ x = permCuntzAlgEquiv σ x := rfl

theorem permCuntzAlgEquiv_sq_of_perm_sq
    (σ : Equiv.Perm (Fin n)) (hσ : σ * σ = 1) (x : CuntzAlg n) :
    permCuntzAlgEquiv σ (permCuntzAlgEquiv σ x) = x := by
  have h := permCuntzAlgHom_comp σ σ (n := n)
  have hx := congrArg (fun f : CuntzAlg n →ₐ[ℂ] CuntzAlg n => f x) h
  rw [hσ] at hx
  simpa [permCuntzAlgEquiv_apply, permCuntzAlgHom_one] using hx

/-- The permutation reference sector has trivial monodromy. -/
theorem permutationMonodromy_eq_id
    (σ : Equiv.Perm (Fin n)) (hσ : σ * σ = 1) :
    ∀ x : CuntzAlg n,
      permCuntzAlgEquiv σ (permCuntzAlgEquiv σ x) = x := by
  intro x
  exact permCuntzAlgEquiv_sq_of_perm_sq σ hσ x

@[simp] theorem permCuntzAlgHom_generator (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permCuntzAlgHom σ (cuntzS n i) = cuntzS n (σ i) := by
  simp [permCuntzAlgHom, cuntzS, cuntzMk, permTensorAlgHom,
    permFreeToCuntz, permFree, permGen, S, gen,
    TensorAlgebra.lift_ι_apply]

@[simp] theorem permCuntzAlgHom_generator_dag (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permCuntzAlgHom σ (cuntzSdag n i) = cuntzSdag n (σ i) := by
  simp [permCuntzAlgHom, cuntzSdag, cuntzMk, permTensorAlgHom,
    permFreeToCuntz, permFree, permGen, Sdag, gen,
    TensorAlgebra.lift_ι_apply]

theorem permCuntzAlgEquiv_wordShift
    (σ : Equiv.Perm (Fin n)) (w : List (Fin n)) :
    permCuntzAlgEquiv σ (cuntzWordShift w) =
      cuntzWordShift (w.map σ) := by
  induction w with
  | nil => simp [cuntzWordShift]
  | cons i w ih =>
      have ih' : permCuntzAlgHom σ (cuntzWordShift w) =
          cuntzWordShift (w.map σ) := by
        simpa [permCuntzAlgEquiv_apply] using ih
      change permCuntzAlgHom σ
          (cuntzS n i * cuntzWordShift w) = _
      rw [map_mul, permCuntzAlgHom_generator, ih']
      simp [cuntzWordShift]

theorem permCuntzAlgEquiv_wordShiftDag
    (σ : Equiv.Perm (Fin n)) (w : List (Fin n)) :
    permCuntzAlgEquiv σ (cuntzWordShiftDag w) =
      cuntzWordShiftDag (w.map σ) := by
  induction w with
  | nil => simp [cuntzWordShiftDag]
  | cons i w ih =>
      have ih' : permCuntzAlgHom σ (cuntzWordShiftDag w) =
          cuntzWordShiftDag (w.map σ) := by
        simpa [permCuntzAlgEquiv_apply] using ih
      change permCuntzAlgHom σ
          (cuntzWordShiftDag w * cuntzSdag n i) = _
      rw [map_mul, ih', permCuntzAlgHom_generator_dag]
      simp [cuntzWordShiftDag]

theorem permCuntzAlgEquiv_cylinderProjection
    (σ : Equiv.Perm (Fin n)) (w : List (Fin n)) :
    permCuntzAlgEquiv σ (cylinderProjection w) =
      cylinderProjection (w.map σ) := by
  change permCuntzAlgHom σ
      (cuntzWordShift w * cuntzWordShiftDag w) = _
  rw [map_mul]
  have h₁ := permCuntzAlgEquiv_wordShift σ w
  have h₂ := permCuntzAlgEquiv_wordShiftDag σ w
  simp only [permCuntzAlgEquiv_apply] at h₁ h₂
  rw [h₁, h₂]
  rfl

theorem expectation_permCuntzAlgEquiv_cylinderProjection
    (σ : Equiv.Perm (Fin n)) (w : List (Fin n)) :
    expectation n (permCuntzAlgEquiv σ (cylinderProjection w)) =
      permCuntzAlgEquiv σ (cylinderProjection w) := by
  rw [permCuntzAlgEquiv_cylinderProjection,
    expectation_cylinderProjection_fixed]

theorem expectation_permCuntzAlgEquiv_commute
    (σ : Equiv.Perm (Fin n)) (x : CuntzAlg n) :
    expectation n (permCuntzAlgEquiv σ x) =
      permCuntzAlgEquiv σ (expectation n x) := by
  unfold expectation
  change (∑ i : Fin n,
      (cuntzS n i * cuntzSdag n i) *
        permCuntzAlgHom σ x * (cuntzS n i * cuntzSdag n i)) =
      permCuntzAlgHom σ (∑ i : Fin n,
        (cuntzS n i * cuntzSdag n i) * x *
          (cuntzS n i * cuntzSdag n i))
  calc
    (∑ i : Fin n,
        (cuntzS n i * cuntzSdag n i) *
          permCuntzAlgHom σ x * (cuntzS n i * cuntzSdag n i)) =
        ∑ i : Fin n,
          (cuntzS n (σ i) * cuntzSdag n (σ i)) *
            permCuntzAlgHom σ x *
              (cuntzS n (σ i) * cuntzSdag n (σ i)) := by
      exact (Equiv.sum_comp σ (fun i : Fin n =>
        (cuntzS n i * cuntzSdag n i) *
          permCuntzAlgHom σ x * (cuntzS n i * cuntzSdag n i))).symm
    _ = permCuntzAlgHom σ
        (∑ i : Fin n,
          (cuntzS n i * cuntzSdag n i) * x *
            (cuntzS n i * cuntzSdag n i)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [map_mul, permCuntzAlgHom_generator,
        permCuntzAlgHom_generator_dag]

theorem expectation_cuntzBraidGenerator_cylinderProjection
    (i : Fin 2) (w : List (Fin 3)) :
    expectation 3 (cuntzBraidGenerator i (cylinderProjection w)) =
      cuntzBraidGenerator i (cylinderProjection w) := by
  exact expectation_permCuntzAlgEquiv_cylinderProjection
    (braidPerm i) w

/-- The range projector attached to a permuted Cuntz label. -/
def permutedRangeProjector (σ : Equiv.Perm (Fin n)) (i : Fin n) : CuntzAlg n :=
  cuntzS n (σ i) * cuntzSdag n (σ i)

@[simp] theorem permutedRangeProjector_apply
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permutedRangeProjector σ i =
      cuntzS n (σ i) * cuntzSdag n (σ i) := rfl

theorem permCuntzAlgHom_rangeProjector (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permCuntzAlgHom σ (cuntzS n i * cuntzSdag n i) =
      permutedRangeProjector σ i := by
  unfold permutedRangeProjector
  rw [map_mul, permCuntzAlgHom_generator, permCuntzAlgHom_generator_dag]

theorem permCuntzAlgHom_partition (σ : Equiv.Perm (Fin n)) :
    permCuntzAlgHom σ (∑ i : Fin n,
      cuntzS n i * cuntzSdag n i) = 1 := by
  rw [cuntz_ranges_sum_one, map_one]

theorem expectation_partition_after_permutation (σ : Equiv.Perm (Fin n)) :
    expectation n (permCuntzAlgHom σ (∑ i : Fin n,
      cuntzS n i * cuntzSdag n i)) = 1 := by
  rw [permCuntzAlgHom_partition, expectation_one]

theorem permutedRangeProjector_orthogonal
    (σ : Equiv.Perm (Fin n)) {i j : Fin n} (hij : i ≠ j) :
    permutedRangeProjector σ i * permutedRangeProjector σ j = 0 := by
  unfold permutedRangeProjector
  exact cuntz_range_projectors_orthogonal n (σ.injective.ne hij)

theorem permutedRangeProjector_idempotent
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permutedRangeProjector σ i * permutedRangeProjector σ i =
      permutedRangeProjector σ i := by
  unfold permutedRangeProjector
  exact cuntz_range_projector n (σ i)

/-- A label permutation preserves the finite Cuntz partition of unity. -/
theorem permutedRangeProjector_sum_one (σ : Equiv.Perm (Fin n)) :
    (∑ i : Fin n, permutedRangeProjector σ i) = 1 := by
  calc
    (∑ i : Fin n, permutedRangeProjector σ i) =
        ∑ i : Fin n, (cuntzS n (σ i) * cuntzSdag n (σ i)) := by
          rfl
    _ = ∑ i : Fin n, (cuntzS n i * cuntzSdag n i) := by
          exact Equiv.sum_comp σ (fun i : Fin n => cuntzS n i * cuntzSdag n i)
    _ = 1 := cuntz_ranges_sum_one n

/-- The permuted diagonal partition is fixed by the finite conditional expectation. -/
theorem expectation_permutedRangeProjector_sum (σ : Equiv.Perm (Fin n)) :
    expectation n (∑ i : Fin n, permutedRangeProjector σ i) =
      ∑ i : Fin n, permutedRangeProjector σ i := by
  rw [permutedRangeProjector_sum_one σ]
  exact expectation_one n

/-- The finite permutation action preserves the conditional expectation on
every element of the algebraic Cuntz quotient; the length-one projector
statement below is a concrete corollary. -/
theorem expectation_fixes_permutedRangeProjector
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    expectation n (permutedRangeProjector σ i) =
      permutedRangeProjector σ i := by
  unfold permutedRangeProjector
  exact expectation_projector n (σ i)

end InfoGeometry.Algebra.CuntzBraidExpectationIntertwiner
