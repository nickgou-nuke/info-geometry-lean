import Mathlib
import InfoGeometry.Arithmetic.PrimonFinite
import InfoGeometry.Arithmetic.SplitMajoranaPrimon
import InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-!
# InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter

Finite Möbius-graded thermal character over the certified prime register.

This module gives the clean finite arithmetic-supertrace anchor:

* a two-state occupancy model;
* a local Witten factor `1 - exp(-s log p)`;
* the finite supertrace product theorem;
* compatibility with the existing finite Dirichlet/Witten owner;
* an explicit infinite reciprocal-zeta bridge socket, kept witness-gated.

No infinite Euler product, analytic continuation, Pfaffian determinant, or RH
claim is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace PrimeMajoranaWittenCharacter

open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/-- Two-state finite occupancy of a prime mode. -/
inductive Occupancy where
  | empty
  | occupied
  deriving DecidableEq, Repr, Fintype

namespace Occupancy

/-- Boolean-to-occupancy conversion used by the finite anchor. -/
def toBool : Occupancy → Bool
  | .empty => false
  | .occupied => true

/-- The canonical equivalence between occupancy and Boolean states. -/
def equivBool : Occupancy ≃ Bool where
  toFun := toBool
  invFun := fun b => if b then .occupied else .empty
  left_inv := by
    intro o
    cases o <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl

/-- Occupancy readout as a sign. -/
def sign : Occupancy → ℝ
  | .empty => 1
  | .occupied => -1

end Occupancy

/--
The signed sum over a two-state occupancy variable.

This is the finite Boolean/Cantor anchor used to specialize the local Witten
factor cleanly.
-/
lemma sum_prod_boolean (a b : ℝ) :
    ∑ o : Occupancy, (match o with
      | .empty => a
      | .occupied => b) = a + b := by
  classical
  have h : (Finset.univ : Finset Occupancy) = {Occupancy.empty, Occupancy.occupied} := by
    decide
  rw [h]
  simp

/--
Local Witten factor for a single prime mode at inverse temperature `s`.

The two occupancy states contribute `1` and `-exp(-s log p)`.
-/
def localWittenCharacter (p : ℕ) (s : ℝ) : ℝ :=
  ∑ o : Occupancy, match o with
    | .empty => 1
    | .occupied => - Real.exp (-s * Real.log (p : ℝ))

/-- The local Witten factor is the reciprocal Euler factor. -/
theorem localWittenCharacter_eq_reciprocalEulerFactor
    (p : ℕ) (s : ℝ) :
    localWittenCharacter p s =
      1 - Real.exp (-s * Real.log (p : ℝ)) := by
  rw [localWittenCharacter, sum_prod_boolean]
  ring

/-- Finite Witten character over a certified prime register. -/
def finiteWittenCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  PrimonFinite.STrF P.primes q

/-- Finite Möbius-graded thermal character over a certified prime register. -/
def mobiusGradedThermalCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  finiteWittenCharacter P q

/-- The finite Witten character equals the finite Euler product. -/
theorem finiteWittenCharacter_eq_product
    (P : PrimeRegister) (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      ∏ p ∈ P.primes, (1 - q p) := by
  simpa [finiteWittenCharacter] using
    (PrimonFinite.STrF_eq_prod (modes := P.primes) (q := q))

/-- The finite Witten character equals the finite Möbius-graded thermal character. -/
theorem finiteWittenCharacter_eq_mobiusGradedThermalCharacter
    (P : PrimeRegister) (q : ℕ → ℝ) :
    finiteWittenCharacter P q = mobiusGradedThermalCharacter P q := by
  rfl

/-- The finite Witten character agrees with the finite Dirichlet Witten character. -/
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

end PrimeMajoranaWittenCharacter
