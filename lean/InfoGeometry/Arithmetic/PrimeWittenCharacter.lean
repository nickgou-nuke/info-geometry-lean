import Mathlib
import InfoGeometry.Arithmetic.PrimonFinite
import InfoGeometry.Arithmetic.SplitMajoranaPrimon
import InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter
import InfoGeometry.Meta.OwnerTarget

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
  simpa [finiteWittenCharacter] using
    (InfoGeometry.Arithmetic.PrimonFinite.STrF_eq_prod (modes := P.primes) (q := q))

/-- The finite Witten character equals the finite Möbius-graded thermal character. -/
theorem finiteWittenCharacter_eq_mobiusGradedThermalCharacter
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.mobiusGradedThermalCharacter P q := by
  calc
    finiteWittenCharacter P q = InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q :=
      finiteWittenCharacter_eq_eulerProduct P q
    _ = InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.mobiusGradedThermalCharacter P q := by
      simpa [InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.mobiusGradedThermalCharacter] using
        (InfoGeometry.Arithmetic.SplitMajoranaPrimon.dirichletWittenCharacter_eq_eulerProduct P q).symm

/-- The finite Witten character agrees with the finite Dirichlet Witten character. -/
theorem finiteWittenCharacter_eq_dirichletWittenCharacter
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.dirichletWittenCharacter P q := by
  calc
    finiteWittenCharacter P q = InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q :=
      finiteWittenCharacter_eq_eulerProduct P q
    _ = InfoGeometry.Arithmetic.SplitMajoranaPrimon.dirichletWittenCharacter P q := by
      symm
      exact InfoGeometry.Arithmetic.SplitMajoranaPrimon.dirichletWittenCharacter_eq_eulerProduct P q

/-- Owner target for the finite Witten character surface. -/
@[owner_target_tag]
def PrimeWittenCharacterOwnerTarget : Prop :=
  ∀ (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ),
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q ∧
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.mobiusGradedThermalCharacter P q ∧
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.dirichletWittenCharacter P q

/-- The finite Witten character owner target is proved. -/
theorem primeWittenCharacterOwnerTarget :
    PrimeWittenCharacterOwnerTarget := by
  intro P q
  exact ⟨finiteWittenCharacter_eq_eulerProduct P q,
    finiteWittenCharacter_eq_mobiusGradedThermalCharacter P q,
    finiteWittenCharacter_eq_dirichletWittenCharacter P q⟩

end InfoGeometry.Arithmetic.PrimeWittenCharacter
