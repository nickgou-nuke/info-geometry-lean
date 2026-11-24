/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimonFinite
import InfoGeometry.Arithmetic.SplitMajoranaPrimon
import InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter

/-!
# InfoGeometry.Arithmetic.PrimeWittenCharacter

Finite Witten-character owner for the split-Majorana prime gas.

This module stays entirely in the finite/combinatorial layer:

* the Witten character is the finite signed supertrace over the prime cutoff;
* it agrees with the finite Euler product;
* it agrees with the finite Möbius-graded thermal character;
* it agrees with the finite Dirichlet Witten character.

The proof of the Euler-product identity is delegated directly to the existing
`PrimonFinite` finite supertrace theorem.

No infinite Euler product, analytic continuation, OPE/CFT carrier, or RH claim
is asserted here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeWittenCharacter

open scoped BigOperators

/-- Finite Witten character over a certified prime register. -/
def finiteWittenCharacter
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  InfoGeometry.Arithmetic.PrimonFinite.STrF P.primes q

/-- The finite Witten character equals the finite Euler product. -/
theorem finiteWittenCharacter_eq_eulerProduct
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q := by
  simpa [finiteWittenCharacter, InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct] using
    (InfoGeometry.Arithmetic.PrimonFinite.STrF_eq_prod (modes := P.primes) (q := q))

/-- The finite Witten character equals the finite Möbius-graded thermal character. -/
theorem finiteWittenCharacter_eq_mobiusGradedThermalCharacter
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.mobiusGradedThermalCharacter P q := by
  rfl

/-- The finite Witten character agrees with the finite Dirichlet Witten character. -/
theorem finiteWittenCharacter_eq_dirichletWittenCharacter
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.dirichletWittenCharacter P q := by
  calc
    finiteWittenCharacter P q = ∏ p ∈ P.primes, (1 - q p) := by
      simpa [finiteWittenCharacter] using
        (InfoGeometry.Arithmetic.PrimonFinite.STrF_eq_prod
          (modes := P.primes) (q := q))
    _ = InfoGeometry.Arithmetic.SplitMajoranaPrimon.dirichletWittenCharacter P q := by
      simpa [InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct] using
        (InfoGeometry.Arithmetic.SplitMajoranaPrimon.dirichletWittenCharacter_eq_eulerProduct P q).symm

theorem finiteWittenCharacter_eq_logarithmicMajoranaLocalProduct
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (s : ℝ) :
    finiteWittenCharacter P (fun p => Real.exp (-s * Real.log (p : ℝ))) =
      ∏ p ∈ P.primes,
        InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.localWittenCharacter p s := by
  rw [finiteWittenCharacter_eq_eulerProduct]
  refine Finset.prod_congr rfl ?_
  intro p _hp
  exact (
    InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.localWittenCharacter_eq_reciprocalEulerFactor
      p s).symm

end InfoGeometry.Arithmetic.PrimeWittenCharacter
