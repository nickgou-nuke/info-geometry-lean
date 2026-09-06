-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic

/-- The arithmetic weight `1 / (n log n)`, extended by `0` on `n ≤ 1`. -/
def primitiveWeight (n : ℕ) : ℝ :=
  if 1 < n then 1 / ((n : ℝ) * Real.log n) else 0

/--
Mellin/Laplace kernel for the primitive weight.

For `n > 1` this is `exp (-s log n) = n^(-s)`. We keep the kernel at `0` on
`n ≤ 1` so that the integral bridge matches `primitiveWeight` without side
conditions.
-/
def primitiveMellinKernel (n : ℕ) (s : ℝ) : ℝ :=
  if 1 < n then Real.exp (-s * Real.log n) else 0

/-- Inverted spectral base attached to `n`, viewed as `a ↦ a⁻¹`. -/
def primitiveInverseBase (n : ℕ) : ℝ :=
  ((n : ℝ) : ℝ)⁻¹

/--
Shifted modular-time kernel.

This is the same Mellin kernel after the translation `s = τ + 1`, so the
improper integral runs over `τ ∈ (0, ∞)`.
-/
def primitiveModularKernel (n : ℕ) (τ : ℝ) : ℝ :=
  primitiveMellinKernel n (τ + 1)

/--
A primitive subset of the natural numbers: inside the set, divisibility only
occurs on equal elements.
-/
def PrimitiveSet (A : Set ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∈ A → b ∈ A → a ∣ b → a = b