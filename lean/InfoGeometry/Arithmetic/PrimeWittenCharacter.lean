import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimonFinite
import InfoGeometry.Arithmetic.SplitMajoranaPrimon
import InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter


noncomputable section

namespace InfoGeometry.Arithmetic.PrimeWittenCharacter

open scoped BigOperators

def finiteWittenCharacter
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  InfoGeometry.Arithmetic.PrimonFinite.STrF P.primes q

theorem finiteWittenCharacter_eq_eulerProduct
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q := by
  simpa [finiteWittenCharacter] using
        (InfoGeometry.Arithmetic.PrimonFinite.STrF_eq_prod (modes := P.primes) (q := q))

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

end InfoGeometry.Arithmetic.PrimeWittenCharacter
