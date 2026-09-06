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

/--
Primitive-weight sum after scaling the support by a fixed divisor `d`.

This is the quotient-side readout that naturally appears after rewriting a
divisor fiber `a = d * m`.
-/
def primitiveScaledWeightSum (A : Finset ℕ) (d : ℕ) : ℝ :=
  Finset.sum A (fun m => primitiveWeight (d * m))

/--
Unnormalized arithmetic weight attached to a finite count profile.

This is the commutative arithmetic shadow of an unnormalized modular weight:
the raw count at `n` multiplied by the Mellin/modular kernel `e^{-s log n}`.
-/
def arithmeticCountWeight (counts : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  counts n * primitiveMellinKernel n s

/-- Total mass of a finite count profile over a chosen support. -/
def arithmeticTotalMass (A : Finset ℕ) (counts : ℕ → ℝ) : ℝ :=
  Finset.sum A counts

/--