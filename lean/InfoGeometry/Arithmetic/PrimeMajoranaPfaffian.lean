import InfoGeometry.Arithmetic.SplitMajoranaPrimon
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Arithmetic.PrimeMajoranaPfaffian

Finite block-Pfaffian carrier for the split-Majorana prime gas.

This file stays finite and algebraic:

* the Pfaffian readout is a finite alias of the finite Euler product.

No general matrix Pfaffian API, no infinite limit, and no analytic zeta
statement is asserted here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeMajoranaPfaffian

open scoped BigOperators

/-- Finite block-Pfaffian carrier. -/
def blockPfaffian
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (q : ℕ → ℝ) : ℝ :=
  InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q

/-- The block-Pfaffian readout is definitionally the finite Euler product. -/
theorem blockPfaffian_eq_finiteEulerProduct
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (q : ℕ → ℝ) :
    blockPfaffian P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q := by
  rfl

end InfoGeometry.Arithmetic.PrimeMajoranaPfaffian
