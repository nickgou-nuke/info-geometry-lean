import Mathlib
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.Algebra.Star.RingQuot
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Data.Finsupp.SMul

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

The formal dagger is built by the same pattern as Clifford reversion:
construct an algebra homomorphism into the opposite algebra, then `unop`.
It reverses word order and swaps the formal generators `Sᵢ ↔ Sᵢ†`.
-/

/-- Swap generator parity: `false ↔ true`. -/
def daggerSwap {n : ℕ} : CuntzGen n → CuntzGen n := fun g => (g.1, !g.2)

@[simp] theorem daggerSwap_involutive {n : ℕ} (g : CuntzGen n) :
    daggerSwap (daggerSwap g) = g := by
  cases g with
  | mk i b => cases b <;> rfl

/-- Linear swap on the free vector space of generators. -/
def daggerFree (n : ℕ) : CuntzFree n →ₗ[ℂ] CuntzFree n where
  toFun v := Finsupp.mapDomain (@daggerSwap n) v
  map_add' _ _ := Finsupp.mapDomain_add
  map_smul' c v := Finsupp.mapDomain_smul c v

@[simp] theorem daggerFree_single (n : ℕ) (i : Fin n) (b : Bool) :
    daggerFree n (Finsupp.single (i, b) (1 : ℂ)) = Finsupp.single (i, !b) (1 : ℂ) := by
  simp [daggerFree, Finsupp.mapDomain_single, daggerSwap]

@[simp] theorem daggerFree_involutive (n : ℕ) (v : CuntzFree n) :
    daggerFree n (daggerFree n v) = v := by
  change Finsupp.mapDomain (@daggerSwap n) (Finsupp.mapDomain (@daggerSwap n) v) = v
  rw [← Finsupp.mapDomain_comp]
  have hfun : (@daggerSwap n) ∘ (@daggerSwap n) = id := by
    funext g
    exact daggerSwap_involutive g
  rw [hfun, Finsupp.mapDomain_id]

/-- Dagger as an algebra homomorphism into the opposite algebra. -/
def daggerAlgHom (n : ℕ) : CuntzTensor n →ₐ[ℂ] (CuntzTensor n)ᵐᵒᵖ :=
  TensorAlgebra.lift ℂ <|
    ((MulOpposite.opLinearEquiv ℂ : CuntzTensor n ≃ₗ[ℂ] (CuntzTensor n)ᵐᵒᵖ) :
        CuntzTensor n →ₗ[ℂ] (CuntzTensor n)ᵐᵒᵖ).comp
      ((TensorAlgebra.ι ℂ).comp (daggerFree n))

/-- Dagger as an anti-multiplicative involution on the tensor algebra. -/
def dagger (n : ℕ) (x : CuntzTensor n) : CuntzTensor n :=
  MulOpposite.unop (daggerAlgHom n x)

@[simp] theorem dagger_gen (n : ℕ) (i : Fin n) (b : Bool) :
    dagger n (gen n i b) = gen n i !b := by
  simp [dagger, daggerAlgHom, gen]

@[simp] theorem dagger_S (n : ℕ) (i : Fin n) : dagger n (S n i) = Sdag n i := by
  simp [S, Sdag]

@[simp] theorem dagger_Sdag (n : ℕ) (i : Fin n) : dagger n (Sdag n i) = S n i := by
  simp [S, Sdag]

@[simp] theorem dagger_mul (n : ℕ) (x y : CuntzTensor n) :
    dagger n (x * y) = dagger n y * dagger n x := by
  simp [dagger, map_mul]

@[simp] theorem dagger_add (n : ℕ) (x y : CuntzTensor n) :
    dagger n (x + y) = dagger n x + dagger n y := by
  simp [dagger, map_add]

@[simp] theorem dagger_algebraMap (n : ℕ) (c : ℂ) :
    dagger n (algebraMap ℂ (CuntzTensor n) c) = algebraMap ℂ (CuntzTensor n) c := by
  simp [dagger, daggerAlgHom]

@[simp] theorem dagger_zero (n : ℕ) : dagger n (0 : CuntzTensor n) = 0 := by
  simpa using dagger_algebraMap n 0

@[simp] theorem dagger_one (n : ℕ) : dagger n (1 : CuntzTensor n) = 1 := by
  simpa using dagger_algebraMap n 1

@[simp] theorem dagger_ι (n : ℕ) (v : CuntzFree n) :
    dagger n (TensorAlgebra.ι ℂ v) = TensorAlgebra.ι ℂ (daggerFree n v) := by
  simp [dagger, daggerAlgHom]

@[simp] theorem dagger_dagger (n : ℕ) (x : CuntzTensor n) :
    dagger n (dagger n x) = x := by
  induction x using TensorAlgebra.induction with
  | algebraMap r => simp
  | ι v => simp
  | mul x y hx hy => simp [hx, hy]
  | add x y hx hy => simp [hx, hy]

@[simp] theorem dagger_sum (n : ℕ) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → CuntzTensor n) :
    dagger n (∑ i ∈ s, f i) = ∑ i ∈ s, dagger n (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

instance (n : ℕ) : StarRing (CuntzTensor n) where
  star := dagger n
  star_involutive := dagger_dagger n
  star_mul := dagger_mul n
  star_add := dagger_add n

@[simp] theorem star_S (n : ℕ) (i : Fin n) : star (S n i) = Sdag n i := by
  change dagger n (S n i) = Sdag n i
  simp

@[simp] theorem star_Sdag (n : ℕ) (i : Fin n) : star (Sdag n i) = S n i := by
  change dagger n (Sdag n i) = S n i
  simp

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

/-! ## Dagger descends through the Cuntz relations -/

theorem dagger_CuntzRel {n : ℕ} : ∀ {x y : CuntzTensor n},
    CuntzRel n x y → CuntzRel n (star x) (star y) := by
  intro x y h
  rcases h with (⟨i, j⟩ | _)
  · change CuntzRel n (dagger n (Sdag n i * S n j)) (dagger n (if i = j then 1 else 0))
    by_cases hij : i = j
    · subst j
      simpa using CuntzRel.orth (n := n) i i
    · have hji : j ≠ i := fun h => hij h.symm
      simpa [hij, hji] using CuntzRel.orth (n := n) j i
  · change CuntzRel n (dagger n (∑ i : Fin n, S n i * Sdag n i)) (dagger n 1)
    simpa using CuntzRel.ranges_sum_one (n := n)

/-- The Cuntz algebra carries the star structure descended from formal dagger. -/
instance (n : ℕ) : StarRing (CuntzAlg n) :=
  RingQuot.starRing (CuntzRel n) (fun _ _ h => dagger_CuntzRel h)

theorem star_cuntzMk (n : ℕ) (x : CuntzTensor n) :
    star (cuntzMk n x) = cuntzMk n (star x) := by
  change star ((RingQuot.mkAlgHom ℂ (CuntzRel n)) x) =
    (RingQuot.mkAlgHom ℂ (CuntzRel n)) (star x)
  simp [RingQuot.mkAlgHom_def, RingQuot.mkRingHom_def]
  rfl

/-- Star swaps the quotient generator `Sᵢ` with its formal adjoint. -/
theorem star_cuntzS (n : ℕ) (i : Fin n) :
    star (cuntzS n i) = cuntzSdag n i := by
  rw [cuntzS, cuntzSdag, star_cuntzMk]
  change cuntzMk n (dagger n (S n i)) = cuntzMk n (Sdag n i)
  simp

/-- Star swaps the quotient formal adjoint back to `Sᵢ`. -/
theorem star_cuntzSdag (n : ℕ) (i : Fin n) :
    star (cuntzSdag n i) = cuntzS n i := by
  rw [cuntzSdag, cuntzS, star_cuntzMk]
  change cuntzMk n (dagger n (Sdag n i)) = cuntzMk n (S n i)
  simp

/-! ## Range projectors are orthogonal and idempotent -/

/-- Each `Sᵢ Sᵢ†` is a projector: `(Sᵢ Sᵢ†)² = Sᵢ Sᵢ†`.
    Follows from `cuntz_isometry`: `Sdag_i * S_i = 1`. -/
theorem cuntz_range_projector (n : ℕ) (i : Fin n) :
    (cuntzS n i * cuntzSdag n i) * (cuntzS n i * cuntzSdag n i) =
      cuntzS n i * cuntzSdag n i := by
  calc
    (cuntzS n i * cuntzSdag n i) * (cuntzS n i * cuntzSdag n i)
        = cuntzS n i * (cuntzSdag n i * cuntzS n i) * cuntzSdag n i := by
      calc
        (cuntzS n i * cuntzSdag n i) * (cuntzS n i * cuntzSdag n i)
            = cuntzS n i * (cuntzSdag n i * (cuntzS n i * cuntzSdag n i)) := by simp [mul_assoc]
        _ = cuntzS n i * ((cuntzSdag n i * cuntzS n i) * cuntzSdag n i) := by simp [mul_assoc]
        _ = cuntzS n i * (cuntzSdag n i * cuntzS n i) * cuntzSdag n i := by simp [mul_assoc]
    _ = cuntzS n i * 1 * cuntzSdag n i := by rw [cuntz_isometry n i]
    _ = cuntzS n i * cuntzSdag n i := by simp

/-- Distinct range projectors are orthogonal: `(Sᵢ Sᵢ†)(Sⱼ Sⱼ†) = 0` for `i ≠ j`.
    Follows from `cuntz_distinct_orthogonal`: `Sdag_i * S_j = 0` for `i ≠ j`. -/
theorem cuntz_range_projectors_orthogonal (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    (cuntzS n i * cuntzSdag n i) * (cuntzS n j * cuntzSdag n j) = 0 := by
  calc
    (cuntzS n i * cuntzSdag n i) * (cuntzS n j * cuntzSdag n j)
        = cuntzS n i * (cuntzSdag n i * cuntzS n j) * cuntzSdag n j := by
      calc
        (cuntzS n i * cuntzSdag n i) * (cuntzS n j * cuntzSdag n j)
            = cuntzS n i * (cuntzSdag n i * (cuntzS n j * cuntzSdag n j)) := by simp [mul_assoc]
        _ = cuntzS n i * ((cuntzSdag n i * cuntzS n j) * cuntzSdag n j) := by simp [mul_assoc]
        _ = cuntzS n i * (cuntzSdag n i * cuntzS n j) * cuntzSdag n j := by simp [mul_assoc]
    _ = cuntzS n i * 0 * cuntzSdag n j := by rw [cuntz_distinct_orthogonal n hij]
    _ = 0 := by simp

/-- Range projectors are self-adjoint: `(Sᵢ Sᵢ†)† = Sᵢ Sᵢ†`. -/
theorem cuntz_range_projector_star (n : ℕ) (i : Fin n) :
    star (cuntzS n i * cuntzSdag n i) = cuntzS n i * cuntzSdag n i := by
  simp [star_mul, star_cuntzS, star_cuntzSdag]

/-- Range projectors commute: `(Sᵢ Sᵢ†)(Sⱼ Sⱼ†) = (Sⱼ Sⱼ†)(Sᵢ Sᵢ†)`.
    For i=j this is trivial. For i≠j both products equal 0 by orthogonality. -/
theorem cuntz_range_projectors_commute (n : ℕ) (i j : Fin n) :
    (cuntzS n i * cuntzSdag n i) * (cuntzS n j * cuntzSdag n j) =
    (cuntzS n j * cuntzSdag n j) * (cuntzS n i * cuntzSdag n i) := by
  by_cases hij : i = j
  · subst j; rfl
  · rw [cuntz_range_projectors_orthogonal n hij,
      cuntz_range_projectors_orthogonal n (Ne.symm hij)]

/-- Complete set of orthogonal projectors: idempotent, orthogonal, commuting,
    self-adjoint, sum to 1. This is the Cuntz partition of unity. -/
theorem cuntz_complete_projector_system (n : ℕ) :
    (∀ i, (cuntzS n i * cuntzSdag n i) * (cuntzS n i * cuntzSdag n i) =
      cuntzS n i * cuntzSdag n i) ∧
    (∀ i j, i ≠ j → (cuntzS n i * cuntzSdag n i) * (cuntzS n j * cuntzSdag n j) = 0) ∧
    (∀ i j, (cuntzS n i * cuntzSdag n i) * (cuntzS n j * cuntzSdag n j) =
      (cuntzS n j * cuntzSdag n j) * (cuntzS n i * cuntzSdag n i)) ∧
    (∀ i, star (cuntzS n i * cuntzSdag n i) = cuntzS n i * cuntzSdag n i) ∧
    (∑ i : Fin n, cuntzS n i * cuntzSdag n i) = 1 := by
  exact ⟨cuntz_range_projector n,
    λ i j hij => cuntz_range_projectors_orthogonal n hij,
    cuntz_range_projectors_commute n, cuntz_range_projector_star n,
    cuntz_ranges_sum_one n⟩

end InfoGeometry.Algebra.CuntzTensorQuotient
