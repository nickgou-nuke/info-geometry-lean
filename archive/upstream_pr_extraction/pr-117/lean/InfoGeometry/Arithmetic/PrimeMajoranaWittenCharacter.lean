import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimonFinite
import InfoGeometry.Arithmetic.SplitMajoranaPrimon
import InfoGeometry.Arithmetic.PrimeBitWittenIndex


noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter

open PrimeBitWittenIndex

inductive Occupancy where
  | empty
  | occupied
  deriving DecidableEq, Repr, Fintype

namespace Occupancy

def toBool : Occupancy → Bool
  | .empty => false
  | .occupied => true

def equivBool : Occupancy ≃ Bool where
  toFun := toBool
  invFun := fun b => if b then .occupied else .empty
  left_inv := by
    intro o
    cases o <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl

def sign : Occupancy → ℝ
  | .empty => 1
  | .occupied => -1

end Occupancy

lemma sum_prod_boolean (a b : ℝ) :
    ∑ o : Occupancy, (match o with
      | .empty => a
      | .occupied => b) = a + b := by
  classical
  have h : (Finset.univ : Finset Occupancy) = {Occupancy.empty, Occupancy.occupied} := by
    decide
  rw [h]
  simp

def localWittenCharacter (p : ℕ) (s : ℝ) : ℝ :=
  ∑ o : Occupancy, match o with
    | .empty => 1
    | .occupied => - Real.exp (-s * Real.log (p : ℝ))

theorem localWittenCharacter_eq_reciprocalEulerFactor
    (p : ℕ) (s : ℝ) :
    localWittenCharacter p s =
      1 - Real.exp (-s * Real.log (p : ℝ)) := by
  rw [localWittenCharacter, sum_prod_boolean]
  ring

def finiteWittenCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  PrimonFinite.STrF P.primes q

def mobiusGradedThermalCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  finiteWittenCharacter P q

theorem finiteWittenCharacter_eq_product
    (P : PrimeRegister) (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      ∏ p ∈ P.primes, (1 - q p) := by
  simpa [finiteWittenCharacter] using
    (PrimonFinite.STrF_eq_prod (modes := P.primes) (q := q))

theorem finiteWittenCharacter_eq_mobiusGradedThermalCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) :
    finiteWittenCharacter P q = mobiusGradedThermalCharacter P q := by
  rfl

theorem finiteWittenCharacter_eq_dirichletWittenCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      SplitMajoranaPrimon.dirichletWittenCharacter P q := by
  calc
    finiteWittenCharacter P q = ∏ p ∈ P.primes, (1 - q p) := by
      exact finiteWittenCharacter_eq_product P q
    _ = SplitMajoranaPrimon.dirichletWittenCharacter P q := by
      symm
      exact SplitMajoranaPrimon.dirichletWittenCharacter_eq_eulerProduct P q

end InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter
