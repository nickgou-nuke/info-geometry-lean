import Mathlib

/-!
# Split Majorana finite character core

This module used to package split-Majorana CAR/OPE and Euclidean-lift laws as
model-supplied witness fields.  Those statements are not constructive theorem
surfaces by themselves, so this file now keeps only the finite scalar readouts
that are definitionally owned here.

The actual CAR, Wick/OPE, and Euclidean Clifford laws belong in dedicated Fock
or Clifford owner modules where the operators are constructed and the relations
are proved.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Algebraic.SplitMajoranaOPEBridge

variable {Mode : Type*}

/-! ## Finite Dirichlet/Witten character -/

/-- Finite Euler factor used by the Dirichlet/Witten character shadow. -/
def finiteDirichletWittenLocalFactor
    (s : ℝ)
    (primeWeight : Mode → ℕ)
    (p : Mode) : ℝ :=
  1 - Real.rpow (primeWeight p : ℝ) (-s)

/-- Finite Dirichlet/Witten character as a product of local factors. -/
def finiteDirichletWittenCharacter
    [Fintype Mode]
    (s : ℝ)
    (primeWeight : Mode → ℕ) : ℝ :=
  ∏ p : Mode, finiteDirichletWittenLocalFactor s primeWeight p

/-- The local factor formula is definitional in this finite core. -/
theorem finiteDirichletWittenLocalFactor_eq
    (s : ℝ)
    (primeWeight : Mode → ℕ)
    (p : Mode) :
    finiteDirichletWittenLocalFactor s primeWeight p =
      1 - Real.rpow (primeWeight p : ℝ) (-s) := by
  rfl

/-- The character is the finite product of its local factors. -/
theorem finiteDirichletWittenCharacter_eq_prod
    [Fintype Mode]
    (s : ℝ)
    (primeWeight : Mode → ℕ) :
    finiteDirichletWittenCharacter s primeWeight =
      ∏ p : Mode, finiteDirichletWittenLocalFactor s primeWeight p := by
  rfl

/-! ## Finite Pfaffian character alias -/

/--
Finite signed Pfaffian-character readout.

This is deliberately an alias of the finite Dirichlet/Witten character.  It is
not a theorem about a general matrix Pfaffian.
-/
def finitePfaffianCharacterReadout
    [Fintype Mode]
    (s : ℝ)
    (primeWeight : Mode → ℕ) : ℝ :=
  finiteDirichletWittenCharacter s primeWeight

/-- The finite Pfaffian-character readout is the finite Dirichlet/Witten character. -/
theorem finitePfaffianCharacterReadout_eq_character
    [Fintype Mode]
    (s : ℝ)
    (primeWeight : Mode → ℕ) :
    finitePfaffianCharacterReadout s primeWeight =
      finiteDirichletWittenCharacter s primeWeight := by
  rfl

/-- Expanded product form of the finite Pfaffian-character readout. -/
theorem finitePfaffianCharacterReadout_eq_prod
    [Fintype Mode]
    (s : ℝ)
    (primeWeight : Mode → ℕ) :
    finitePfaffianCharacterReadout s primeWeight =
      ∏ p : Mode, (1 - Real.rpow (primeWeight p : ℝ) (-s)) := by
  unfold finitePfaffianCharacterReadout
  unfold finiteDirichletWittenCharacter
  unfold finiteDirichletWittenLocalFactor
  rfl

end InfoGeometry.Algebraic.SplitMajoranaOPEBridge
