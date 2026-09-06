def realVonMangoldt (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n

/--
Prime-weighted Mellin/Dirichlet readout over a finite support.

This is the finite-support shadow of the logarithmic derivative lane associated
to `-ζ'/ζ`.
-/
def arithmeticPrimePartition (A : Finset ℕ) (s : ℝ) : ℝ :=
  Finset.sum A (fun n => realVonMangoldt n * primitiveMellinKernel n s)

/-- The indicator series used for infinite primitive sets. -/
def primitiveIndicatorSeries (A : Set ℕ) : ℕ → ℝ :=
  by
    classical
    exact fun n => if n ∈ A then primitiveWeight n else 0

/--
Finite formulation of the primitive-sets-above problem.
