import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-!
# Associative Peirce four-block decomposition

For an associative unital ring `A` and an idempotent `f : A`, put
`e = 1 - f`.  Then `e` is idempotent, `f * e = e * f = 0`, and every
`x : A` admits the canonical four-block expansion

`x = f*x*f + f*x*e + e*x*f + e*x*e`.

The four Peirce sectors are represented elementwise as

* `A₁₁ = f A f`,
* `A₁₀ = f A e`,
* `A₀₁ = e A f`,
* `A₀₀ = e A e`.

This file proves the complete associative routing table
`Aᵢⱼ Aₖₗ ⊆ Aᵢₗ` when `j = k`, and zero multiplication when `j ≠ k`.
No Jordan-specific Peirce eigenvalue claims are made here.
-/

namespace InfoGeometry.Core.PeirceDecomposition

section AssociativePeirce

variable {A : Type*} [Ring A]

/-- The complementary idempotent candidate `1 - f`. -/
def complementIdempotent (f : A) : A :=
  1 - f

@[simp]
theorem add_complementIdempotent (f : A) :
    f + complementIdempotent f = 1 := by
  simp [complementIdempotent]

@[simp]
theorem complementIdempotent_add (f : A) :
    complementIdempotent f + f = 1 := by
  simp [complementIdempotent]

/-- The complement of an idempotent is idempotent. -/
@[simp]
theorem complementIdempotent_sq
    (f : A) (hf : f * f = f) :
    complementIdempotent f * complementIdempotent f =
      complementIdempotent f := by
  simp [complementIdempotent, mul_sub, sub_mul, hf]

/-- An idempotent is left-orthogonal to its complement. -/
@[simp]
theorem idempotent_mul_complement
    (f : A) (hf : f * f = f) :
    f * complementIdempotent f = 0 := by
  simp [complementIdempotent, mul_sub, hf]

/-- An idempotent is right-orthogonal to its complement. -/
@[simp]
theorem complement_mul_idempotent
    (f : A) (hf : f * f = f) :
    complementIdempotent f * f = 0 := by
  simp [complementIdempotent, sub_mul, hf]

/-- The `11` Peirce sector `f A f`. -/
def peirce11 (f : A) : Set A :=
  {x | ∃ a : A, x = f * a * f}

/-- The `10` Peirce sector `f A (1-f)`. -/
def peirce10 (f : A) : Set A :=
  {x | ∃ a : A, x = f * a * complementIdempotent f}

/-- The `01` Peirce sector `(1-f) A f`. -/
def peirce01 (f : A) : Set A :=
  {x | ∃ a : A, x = complementIdempotent f * a * f}

/-- The `00` Peirce sector `(1-f) A (1-f)`. -/
def peirce00 (f : A) : Set A :=
  {x | ∃ a : A,
    x = complementIdempotent f * a * complementIdempotent f}

/-- Canonical `11` component. -/
def component11 (f x : A) : A :=
  f * x * f

/-- Canonical `10` component. -/
def component10 (f x : A) : A :=
  f * x * complementIdempotent f

/-- Canonical `01` component. -/
def component01 (f x : A) : A :=
  complementIdempotent f * x * f

/-- Canonical `00` component. -/
def component00 (f x : A) : A :=
  complementIdempotent f * x * complementIdempotent f

@[simp]
theorem component11_mem (f x : A) :
    component11 f x ∈ peirce11 f := by
  exact ⟨x, rfl⟩

@[simp]
theorem component10_mem (f x : A) :
    component10 f x ∈ peirce10 f := by
  exact ⟨x, rfl⟩

@[simp]
theorem component01_mem (f x : A) :
    component01 f x ∈ peirce01 f := by
  exact ⟨x, rfl⟩

@[simp]
theorem component00_mem (f x : A) :
    component00 f x ∈ peirce00 f := by
  exact ⟨x, rfl⟩

/-- Every element is the sum of its four associative Peirce blocks.

This identity is purely distributive and does not require idempotency. -/
theorem peirce_decomposition (f x : A) :
    x =
      component11 f x + component10 f x +
      component01 f x + component00 f x := by
  simp only [component11, component10, component01, component00,
    complementIdempotent]
  noncomm_ring

/-! ## Nonzero routing laws -/

/-- `A₁₁ A₁₁ ⊆ A₁₁`. -/
theorem peirce11_mul_peirce11
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce11 f) (hy : y ∈ peirce11 f) :
    x * y ∈ peirce11 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * f * b, ?_⟩
  simp [mul_assoc, hf]

/-- `A₁₁ A₁₀ ⊆ A₁₀`. -/
theorem peirce11_mul_peirce10
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce11 f) (hy : y ∈ peirce10 f) :
    x * y ∈ peirce10 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * f * b, ?_⟩
  simp [mul_assoc, hf]

/-- `A₁₀ A₀₁ ⊆ A₁₁`. -/
theorem peirce10_mul_peirce01
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce10 f) (hy : y ∈ peirce01 f) :
    x * y ∈ peirce11 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * complementIdempotent f * b, ?_⟩
  simp [mul_assoc, complementIdempotent_sq f hf]

/-- `A₁₀ A₀₀ ⊆ A₁₀`. -/
theorem peirce10_mul_peirce00
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce10 f) (hy : y ∈ peirce00 f) :
    x * y ∈ peirce10 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * complementIdempotent f * b, ?_⟩
  simp [mul_assoc, complementIdempotent_sq f hf]

/-- `A₀₁ A₁₁ ⊆ A₀₁`. -/
theorem peirce01_mul_peirce11
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce01 f) (hy : y ∈ peirce11 f) :
    x * y ∈ peirce01 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * f * b, ?_⟩
  simp [mul_assoc, hf]

/-- `A₀₁ A₁₀ ⊆ A₀₀`. -/
theorem peirce01_mul_peirce10
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce01 f) (hy : y ∈ peirce10 f) :
    x * y ∈ peirce00 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * f * b, ?_⟩
  simp [mul_assoc, hf]

/-- `A₀₀ A₀₁ ⊆ A₀₁`. -/
theorem peirce00_mul_peirce01
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce00 f) (hy : y ∈ peirce01 f) :
    x * y ∈ peirce01 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * complementIdempotent f * b, ?_⟩
  simp [mul_assoc, complementIdempotent_sq f hf]

/-- `A₀₀ A₀₀ ⊆ A₀₀`. -/
theorem peirce00_mul_peirce00
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce00 f) (hy : y ∈ peirce00 f) :
    x * y ∈ peirce00 f := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * complementIdempotent f * b, ?_⟩
  simp [mul_assoc, complementIdempotent_sq f hf]

/-! ## Zero routing laws -/

/-- `A₁₁ A₀₁ = 0`. -/
theorem peirce11_mul_peirce01_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce11 f) (hy : y ∈ peirce01 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simp [mul_assoc, idempotent_mul_complement f hf]

/-- `A₁₁ A₀₀ = 0`. -/
theorem peirce11_mul_peirce00_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce11 f) (hy : y ∈ peirce00 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simp [mul_assoc, idempotent_mul_complement f hf]

/-- `A₁₀ A₁₁ = 0`. -/
theorem peirce10_mul_peirce11_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce10 f) (hy : y ∈ peirce11 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simp [mul_assoc, complement_mul_idempotent f hf]

/-- `A₁₀ A₁₀ = 0`. -/
theorem peirce10_mul_peirce10_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce10 f) (hy : y ∈ peirce10 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simp [mul_assoc, complement_mul_idempotent f hf]

/-- `A₀₁ A₀₁ = 0`. -/
theorem peirce01_mul_peirce01_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce01 f) (hy : y ∈ peirce01 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simp [mul_assoc, idempotent_mul_complement f hf]

/-- `A₀₁ A₀₀ = 0`. -/
theorem peirce01_mul_peirce00_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce01 f) (hy : y ∈ peirce00 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simp [mul_assoc, idempotent_mul_complement f hf]

/-- `A₀₀ A₁₁ = 0`. -/
theorem peirce00_mul_peirce11_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce00 f) (hy : y ∈ peirce11 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simp [mul_assoc, complement_mul_idempotent f hf]

/-- `A₀₀ A₁₀ = 0`. -/
theorem peirce00_mul_peirce10_eq_zero
    (f : A) (hf : f * f = f)
    {x y : A} (hx : x ∈ peirce00 f) (hy : y ∈ peirce10 f) :
    x * y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  simp [mul_assoc, complement_mul_idempotent f hf]

/-! ## Corner units -/

/-- `f` acts as a left identity on `A₁₁`. -/
theorem peirce11_absorb_left
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce11 f) :
    f * x = x := by
  rcases hx with ⟨a, rfl⟩
  simp [mul_assoc, hf]

/-- `f` acts as a right identity on `A₁₁`. -/
theorem peirce11_absorb_right
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce11 f) :
    x * f = x := by
  rcases hx with ⟨a, rfl⟩
  simp [mul_assoc, hf]

/-- `1-f` acts as a left identity on `A₀₀`. -/
theorem peirce00_absorb_left
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce00 f) :
    complementIdempotent f * x = x := by
  rcases hx with ⟨a, rfl⟩
  simp [mul_assoc, complementIdempotent_sq f hf]

/-- `1-f` acts as a right identity on `A₀₀`. -/
theorem peirce00_absorb_right
    (f : A) (hf : f * f = f)
    {x : A} (hx : x ∈ peirce00 f) :
    x * complementIdempotent f = x := by
  rcases hx with ⟨a, rfl⟩
  simp [mul_assoc, complementIdempotent_sq f hf]

end AssociativePeirce

end InfoGeometry.Core.PeirceDecomposition
