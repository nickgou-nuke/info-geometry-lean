import Mathlib

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic

/-- The arithmetic weight `1 / (n log n)`, extended by `0` on `n ≤ 1`. -/
def primitiveWeight (n : ℕ) : ℝ :=
  if 1 < n then 1 / ((n : ℝ) * Real.log n) else 0

/-- Mellin/Laplace kernel for the primitive weight. -/
def primitiveMellinKernel (n : ℕ) (s : ℝ) : ℝ :=
  if 1 < n then Real.exp (-s * Real.log n) else 0

/-- Inverted spectral base attached to `n`, viewed as `a ↦ a⁻¹`. -/
def primitiveInverseBase (n : ℕ) : ℝ :=
  ((n : ℝ) : ℝ)⁻¹

/-- Shifted modular-time kernel. -/
def primitiveModularKernel (n : ℕ) (τ : ℝ) : ℝ :=
  primitiveMellinKernel n (τ + 1)

/-- A primitive subset of the natural numbers: divisibility only occurs on equal elements. -/
def PrimitiveSet (A : Set ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∈ A → b ∈ A → a ∣ b → a = b

/-- Finite primitive-set specialization. -/
def PrimitiveFinset (A : Finset ℕ) : Prop :=
  PrimitiveSet (A : Set ℕ)

/-- A set is supported above `x` if every member is at least `x`. -/
def SupportedAbove (x : ℕ) (A : Set ℕ) : Prop :=
  ∀ ⦃n : ℕ⦄, n ∈ A → x ≤ n

/-- Finite support-above-`x` specialization. -/
def SupportedAboveFinset (x : ℕ) (A : Finset ℕ) : Prop :=
  SupportedAbove x (A : Set ℕ)

/-- Finite primitive-set weighted sum. -/
def primitiveWeightSum (A : Finset ℕ) : ℝ :=
  Finset.sum A primitiveWeight

/-- Primitive-weight sum after scaling the support by a fixed divisor `d`. -/
def primitiveScaledWeightSum (A : Finset ℕ) (d : ℕ) : ℝ :=
  Finset.sum A (fun m => primitiveWeight (d * m))

/-- Unnormalized arithmetic weight attached to a finite count profile. -/
def arithmeticCountWeight (counts : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  counts n * primitiveMellinKernel n s

/-- Total mass of a finite count profile over a chosen support. -/
def arithmeticTotalMass (A : Finset ℕ) (counts : ℕ → ℝ) : ℝ :=
  Finset.sum A counts

end InfoGeometry.Arithmetic
