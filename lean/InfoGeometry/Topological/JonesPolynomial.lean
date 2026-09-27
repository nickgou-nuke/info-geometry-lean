import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.Tactic

/-!
# The finite algebraic core of the Jones polynomial

This module formalizes the algebraic interfaces appearing in the supplied
description of the Jones polynomial:

* the Temperley--Lieb braid generator `A · e + A⁻¹ · 1`;
* the Markov-trace closure factor `δ^(n-1) · tr(ρ(σ))`;
* writhe normalization by the Reidemeister-I factor;
* the normalized skein relation.

The module deliberately does not claim a construction of knot diagrams,
Reidemeister moves, the Markov trace, or the Reshetikhin--Turaev functor.  Those
objects enter as typed data, so every theorem below states exactly the algebraic
consequence of the supplied interface.
-/

namespace InfoGeometry.Topological.JonesPolynomial

/-! ## Temperley--Lieb braid generator -/

/-- The braid generator from the Kauffman--Temperley--Lieb presentation:
`σᵢ ↦ A · eᵢ + A⁻¹ · 1`.  In a scalar carrier the unit is implicit. -/
def temperleyLiebBraidGenerator {R : Type*} [Ring R]
    (A : Units R) (e : R) : R :=
  (A : R) * e + ((A⁻¹ : Units R) : R)

@[simp]
theorem temperleyLiebBraidGenerator_zero {R : Type*} [Ring R]
    (A : Units R) :
    temperleyLiebBraidGenerator A (0 : R) = ((A⁻¹ : Units R) : R) := by
  simp [temperleyLiebBraidGenerator]

theorem temperleyLiebBraidGenerator_def {R : Type*} [Ring R]
    (A : Units R) (e : R) :
    temperleyLiebBraidGenerator A e =
      (A : R) * e + ((A⁻¹ : Units R) : R) := by
  rfl

/-! ## Writhe normalization -/

/-- Integer powers of the Reidemeister-I factor cancel its bracket scaling. -/
theorem reidemeister_factor_cancel {R : Type*} [Group R]
    (c : R) (w : ℤ) :
    c ^ (-(w + 1)) * c = c ^ (-w) := by
  rw [show -(w + 1) = -w + (-1) by ring, zpow_add]
  simp

/-- The normalized bracket associated with a crossing factor `c`.

For the Kauffman bracket one instantiates `c` with the unit represented by
`-A^3`; keeping `c` abstract avoids introducing an unjustified square-root
choice for the Laurent variable. -/
def normalizedBracket {D R : Type*} [CommRing R]
    (c : Units R) (bracket : D → R) (writhe : D → ℤ) (d : D) : R :=
  ((c ^ (-writhe d) : Units R) : R) * bracket d

/-- A Reidemeister-I bracket law is exactly cancelled by writhe normalization. -/
theorem normalizedBracket_reidemeister_one
    {D R : Type*} [CommRing R]
    (c : Units R) (bracket : D → R) (writhe : D → ℤ)
    (move : D → D)
    (hbracket : ∀ d, bracket (move d) = (c : R) * bracket d)
    (hwrithe : ∀ d, writhe (move d) = writhe d + 1) (d : D) :
    normalizedBracket c bracket writhe (move d) =
      normalizedBracket c bracket writhe d := by
  unfold normalizedBracket
  rw [hbracket d, hwrithe d]
  have hpow : (c ^ (-(writhe d + 1)) : Units R) =
      c ^ (-writhe d) * c⁻¹ := by
    rw [show -(writhe d + 1) = -writhe d + (-1) by ring, zpow_add,
      zpow_neg, zpow_one]
  rw [hpow]
  simp [Units.val_mul, mul_assoc]

/-! ## Markov trace closure -/

/-- A typed family of braid words, indexed by strand number. -/
abbrev BraidWord := ℕ → Type

/-- The bracket readout of a braid through a Markov trace. -/
def bracketFromMarkovTrace {R : Type*} [Semiring R]
    (B : BraidWord) (δ : R)
    (markovTrace : ∀ n, B n → R)
    (n : ℕ) (σ : B n) : R :=
  δ ^ (n - 1) * markovTrace n σ

theorem bracketFromMarkovTrace_def {R : Type*} [Semiring R]
    (B : BraidWord) (δ : R)
    (markovTrace : ∀ n, B n → R)
    (n : ℕ) (σ : B n) :
    bracketFromMarkovTrace B δ markovTrace n σ =
      δ ^ (n - 1) * markovTrace n σ := by
  rfl

/-! ## Skein and invariant interfaces -/

structure SkeinTriple (D : Type*) where
  positive : D
  negative : D
  smoothing : D

/-- The Jones skein equation expressed through `q = t^(1/2)`. -/
def satisfiesJonesSkein {D R : Type*} [Ring R]
    (V : D → R) (q : Units R) (triple : SkeinTriple D) : Prop :=
  ((q : R) - ((q⁻¹ : Units R) : R)) * V triple.smoothing =
    (((q⁻¹ : Units R) : R) ^ 2) * V triple.positive -
      ((q : R) ^ 2) * V triple.negative

structure JonesPolynomialModel (D R : Type*) [CommRing R] where
  value : D → R
  unknot : D
  unknot_value : value unknot = 1
  skein_parameter : Units R
  skein_law : ∀ triple : SkeinTriple D, satisfiesJonesSkein value skein_parameter triple

theorem JonesPolynomialModel.unknot_normalized
    {D R : Type*} [CommRing R] (M : JonesPolynomialModel D R) :
    M.value M.unknot = 1 :=
  M.unknot_value

theorem JonesPolynomialModel.satisfies_skein
    {D R : Type*} [CommRing R] (M : JonesPolynomialModel D R)
    (triple : SkeinTriple D) :
    satisfiesJonesSkein M.value M.skein_parameter triple :=
  M.skein_law triple

end InfoGeometry.Topological.JonesPolynomial
