import Mathlib
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.Algebra.Star.Order

/-!
# Cuntz algebras as tensor-algebra quotients

This file gives the algebraic owner for finite Cuntz/Cuntz--Toeplitz
relations as noncommutative tensor-algebra quotients.  Concrete operator or
matrix models should map out of these quotients; they are not the definition.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzTensorQuotient

/-- Formal Cuntz generators: `false` is `Sᵢ`, `true` is `Sᵢ†`. -/
abbrev CuntzGen (n : ℕ) := Fin n × Bool

/-- Free complex vector space on the formal Cuntz generators. -/
abbrev CuntzFree (n : ℕ) := CuntzGen n →₀ ℂ

/-- The free noncommutative algebra of words in `Sᵢ,Sᵢ†`. -/
abbrev CuntzTensor (n : ℕ) := TensorAlgebra ℂ (CuntzFree n)

/-- Tensor-algebra generator. -/
def gen (n : ℕ) (i : Fin n) (adjoint : Bool) : CuntzTensor n :=
  TensorAlgebra.ι ℂ (Finsupp.single (i, adjoint) (1 : ℂ))

/-- Formal isometry generator `Sᵢ`. -/
def S (n : ℕ) (i : Fin n) : CuntzTensor n := gen n i false

/-- Formal adjoint generator `Sᵢ†`. -/
def Sdag (n : ℕ) (i : Fin n) : CuntzTensor n := gen n i true

/-! ## Dagger anti-involution on the free tensor algebra

The formal dagger `†` is an anti-multiplicative, scalar-conjugate-linear
involution on `CuntzTensor n`.  On generators: `†(Sᵢ) = Sᵢ†`, `†(Sᵢ†) = Sᵢ`.
-/

/-- Swap generator parity: `false ↔ true`. -/
def daggerSwap (n : ℕ) (g : CuntzGen n) : CuntzGen n := (g.1, !g.2)

/-- Dagger as an antilinear map on the free vector space of generators.
    Sends `single (i,b)` to `single (i,¬b)`, extended conjugate-linearly. -/
noncomputable def daggerFree (n : ℕ) : CuntzFree n → CuntzFree n :=
  Finsupp.mapRange (Finsupp.domCongr (daggerSwap n)) (λ r => star r) (λ _ => by simp)

/-- Lift of the dagger to the tensor algebra as an anti-homomorphism into `MulOpposite`.
    This is the canonical way to define an anti-involution on a free algebra:
    `daggerAlgHom x = (daggerAlg x).unop` where `daggerAlg` is the unique algebra
    homomorphism extending `daggerFree` into the opposite algebra. -/
noncomputable def daggerAlgHom (n : ℕ) : CuntzTensor n →ₐ[ℂ] (CuntzTensor n)ᵐᵒᵖ :=
  TensorAlgebra.lift ℂ (MulOpposite.op ∘ (TensorAlgebra.ι ℂ) ∘ daggerFree n)

/-- Dagger as an anti-multiplicative, conjugate-linear involution. -/
noncomputable def dagger (n : ℕ) (x : CuntzTensor n) : CuntzTensor n :=
  MulOpposite.unop (daggerAlgHom n x)

@[simp] theorem dagger_gen (n : ℕ) (i : Fin n) (b : Bool) :
    dagger n (gen n i b) = gen n i !b := by
  unfold dagger daggerAlgHom gen
  simp [daggerFree, daggerSwap, TensorAlgebra.lift_ι_apply, MulOpposite.unop_op]

@[simp] theorem dagger_S (n : ℕ) (i : Fin n) : dagger n (S n i) = Sdag n i := by
  unfold S Sdag; simp

@[simp] theorem dagger_Sdag (n : ℕ) (i : Fin n) : dagger n (Sdag n i) = S n i := by
  unfold S Sdag; simp

/-- Dagger is additive. -/
theorem dagger_add (n : ℕ) (x y : CuntzTensor n) :
    dagger n (x + y) = dagger n x + dagger n y := by
  unfold dagger
  simp

/-- Dagger is anti-multiplicative: `†(x·y) = †y · †x`. -/
theorem dagger_mul (n : ℕ) (x y : CuntzTensor n) :
    dagger n (x * y) = dagger n y * dagger n x := by
  unfold dagger
  simp [← MulOpposite.unop_mul]

/-- Dagger is conjugate-linear: `†(c·x) = c̄ · †x`. -/
theorem dagger_smul (n : ℕ) (c : ℂ) (x : CuntzTensor n) :
    dagger n (c • x) = star c • dagger n x := by
  unfold dagger daggerAlgHom
  simp [TensorAlgebra.lift_algebraMap_smul]

/-- Dagger is involutive: `†(†x) = x`. -/
theorem dagger_dagger (n : ℕ) (x : CuntzTensor n) :
    dagger n (dagger n x) = x := by
  apply TensorAlgebra.induction (motive := λ x => dagger n (dagger n x) = x) x
  · intro r; simp [dagger_smul, dagger_add]
  · intro v
    -- v : CuntzFree n is a finite ℂ-linear combination of generators
    -- daggerFree swaps (i,b) ↔ (i,¬b) and conjugates scalars; applying twice gives identity
    refine Finsupp.induction v ?_ ?_
    · simp
    · intro g c h
      simp [dagger_gen, dagger_smul, dagger_add, h]
  · intro x y hx hy; rw [dagger_add, dagger_add, hx, hy]
  · intro x y hx hy; rw [dagger_mul, dagger_mul, hx, hy]

/-- Dagger of 1 is 1. -/
@[simp] theorem dagger_one (n : ℕ) : dagger n (1 : CuntzTensor n) = 1 := by
  unfold dagger daggerAlgHom; simp

/-- Dagger of a sum is the sum of daggers. -/
@[simp] theorem dagger_sum (n : ℕ) {ι : Type*} (s : Finset ι) (f : ι → CuntzTensor n) :
    dagger n (∑ i ∈ s, f i) = ∑ i ∈ s, dagger n (f i) := by
  simp [dagger_add]

/-! ## Cuntz--Toeplitz relation: `Sᵢ† Sⱼ = δᵢⱼ`. -/
inductive CuntzToeplitzRel (n : ℕ) : CuntzTensor n → CuntzTensor n → Prop
  | orth (i j : Fin n) :
      CuntzToeplitzRel n (Sdag n i * S n j) (if i = j then 1 else 0)

/-! ## Cuntz relation: Cuntz--Toeplitz plus `Σᵢ Sᵢ Sᵢ† = 1`. -/
inductive CuntzRel (n : ℕ) : CuntzTensor n → CuntzTensor n → Prop
  | orth (i j : Fin n) :
      CuntzRel n (Sdag n i * S n j) (if i = j then 1 else 0)
  | ranges_sum_one :
      CuntzRel n (∑ i : Fin n, S n i * Sdag n i) 1

/-- Algebraic Cuntz--Toeplitz algebra as a tensor-algebra quotient. -/
abbrev CuntzToeplitzAlg (n : ℕ) := RingQuot (CuntzToeplitzRel n)

/-- Algebraic finite Cuntz algebra as a tensor-algebra quotient. -/
abbrev CuntzAlg (n : ℕ) := RingQuot (CuntzRel n)

/-- Quotient map for the Cuntz--Toeplitz algebra. -/
def toeplitzMk (n : ℕ) : CuntzTensor n →ₐ[ℂ] CuntzToeplitzAlg n :=
  RingQuot.mkAlgHom ℂ (CuntzToeplitzRel n)

/-- Quotient map for the Cuntz algebra. -/
def cuntzMk (n : ℕ) : CuntzTensor n →ₐ[ℂ] CuntzAlg n :=
  RingQuot.mkAlgHom ℂ (CuntzRel n)

/-- Image of `Sᵢ` in the Cuntz--Toeplitz quotient. -/
def toeplitzS (n : ℕ) (i : Fin n) : CuntzToeplitzAlg n := toeplitzMk n (S n i)

/-- Image of `Sᵢ†` in the Cuntz--Toeplitz quotient. -/
def toeplitzSdag (n : ℕ) (i : Fin n) : CuntzToeplitzAlg n := toeplitzMk n (Sdag n i)

/-- Image of `Sᵢ` in the Cuntz quotient. -/
def cuntzS (n : ℕ) (i : Fin n) : CuntzAlg n := cuntzMk n (S n i)

/-- Image of `Sᵢ†` in the Cuntz quotient. -/
def cuntzSdag (n : ℕ) (i : Fin n) : CuntzAlg n := cuntzMk n (Sdag n i)

/-- The Cuntz--Toeplitz quotient satisfies `Sᵢ† Sⱼ = δᵢⱼ`. -/
theorem toeplitz_orthogonality (n : ℕ) (i j : Fin n) :
    toeplitzSdag n i * toeplitzS n j = if i = j then 1 else 0 := by
  change toeplitzMk n (Sdag n i) * toeplitzMk n (S n j) = _
  rw [← map_mul]
  simpa using RingQuot.mkAlgHom_rel ℂ (CuntzToeplitzRel.orth i j)

/-- The Cuntz quotient satisfies `Sᵢ† Sⱼ = δᵢⱼ`. -/
theorem cuntz_orthogonality (n : ℕ) (i j : Fin n) :
    cuntzSdag n i * cuntzS n j = if i = j then 1 else 0 := by
  change cuntzMk n (Sdag n i) * cuntzMk n (S n j) = _
  rw [← map_mul]
  simpa using RingQuot.mkAlgHom_rel ℂ (CuntzRel.orth i j)

/-- The finite Cuntz quotient satisfies `Σᵢ Sᵢ Sᵢ† = 1`. -/
theorem cuntz_ranges_sum_one (n : ℕ) :
    (∑ i : Fin n, cuntzS n i * cuntzSdag n i) = 1 := by
  change (∑ i : Fin n, cuntzMk n (S n i) * cuntzMk n (Sdag n i)) = 1
  simp_rw [← map_mul]
  rw [← map_sum]
  simpa using RingQuot.mkAlgHom_rel ℂ (CuntzRel.ranges_sum_one (n := n))

/-- Each Cuntz generator is an algebraic isometry in the quotient. -/
theorem cuntz_isometry (n : ℕ) (i : Fin n) :
    cuntzSdag n i * cuntzS n i = 1 := by
  simpa using cuntz_orthogonality n i i

/-- Distinct Cuntz generators have orthogonal initial spaces. -/
theorem cuntz_distinct_orthogonal (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    cuntzSdag n i * cuntzS n j = 0 := by
  simpa [hij] using cuntz_orthogonality n i j

/-- The quotient construction packages exactly the finite algebraic Cuntz relations. -/
theorem finite_cuntz_tensor_quotient_packet (n : ℕ) :
    (∀ i j : Fin n, cuntzSdag n i * cuntzS n j = if i = j then 1 else 0) ∧
    (∑ i : Fin n, cuntzS n i * cuntzSdag n i) = 1 := by
  exact ⟨cuntz_orthogonality n, cuntz_ranges_sum_one n⟩

/-! ## Dagger descends through the Cuntz relations

The key theorem: the relation `CuntzRel` is compatible with the dagger.
If `x ~ y` modulo `CuntzRel`, then `†x ~ †y` also.  This makes the
quotient `CuntzAlg n` a `StarRing`.
-/

/-- Dagger maps each defining relation to itself (modulo the relation):
    `†(Sdag n i * S n j) = Sdag n j * S n i` which is `= δᵢⱼ` iff the original is `= δⱼᵢ`.
    But `δᵢⱼ` is symmetric, so the relation is dagger-invariant. -/
theorem dagger_CuntzRel {n : ℕ} {x y : CuntzTensor n} (h : CuntzRel n x y) :
    CuntzRel n (dagger n x) (dagger n y) := by
  rcases h with (⟨i, j⟩ | _)
  · -- orth: x = Sdag n i * S n j, y = (if i = j then 1 else 0)
    rw [dagger_mul, dagger_Sdag, dagger_S]
    -- †(Sdagᵢ * Sⱼ) = †(Sⱼ) * †(Sdagᵢ) = Sdagⱼ * Sᵢ
    -- Now: is (Sdagⱼ * Sᵢ) related to δᵢⱼ (= δⱼᵢ)?
    by_cases hij : i = j
    · subst hij; simpa [dagger_one] using CuntzRel.orth i i
    · have hji : j ≠ i := by intro h; exact hij h.symm
      -- Sdagⱼ * Sᵢ ~ 0 by CuntzRel.orth j i
      -- while (if i = j then 1 else 0) ~ 0 = (if j = i then 1 else 0)
      -- So we need: CuntzRel n (Sdag n j * S n i) (if i = j then 1 else 0)
      simpa [hij, dagger_one] using CuntzRel.orth j i
  · -- ranges_sum_one: x = Σ Sᵢ * Sdagᵢ, y = 1
    -- dagger of Σ Sᵢ·Sdagᵢ = Σ (dagger Sdagᵢ)·(dagger Sᵢ) = Σ Sᵢ·Sdagᵢ = x again
    -- and dagger(1) = 1
    simp [dagger_sum, dagger_mul, dagger_S, dagger_Sdag, dagger_one, dagger_add]

/-- The Cuntz algebra carries a `StarRing` structure descended from the dagger. -/
instance (n : ℕ) : StarRing (CuntzAlg n) :=
  RingQuot.starRing (dagger_CuntzRel (n := n))

@[simp] theorem star_cuntzS (n : ℕ) (i : Fin n) :
    star (cuntzS n i) = cuntzSdag n i := by
  unfold cuntzS cuntzSdag
  simp [RingQuot.star_mk, dagger_S]

@[simp] theorem star_cuntzSdag (n : ℕ) (i : Fin n) :
    star (cuntzSdag n i) = cuntzS n i := by
  unfold cuntzS cuntzSdag
  simp [RingQuot.star_mk, dagger_Sdag]

end InfoGeometry.Algebra.CuntzTensorQuotient