import Mathlib.Tactic

/-!
# Finite `O(5,5)` / V4 / Klein-bottle coordinate shadows

This module is deliberately finite and theorem-safe.  It proves exact coordinate
identities over `ℚ` for a split hyperbolic `(5,5)` pairing.

It does **not** construct the Lie group `O(5,5)`, `Pin(5,5)`, a Clifford
Pin double cover, a topological quotient by `{I,-I}`, CCC, full conformal
inversion, or full orbit classification.  The quotient and Klein-bottle layers
below are finite coordinate shadows only.
-/

namespace O55V4KleinBottleFinite

/-- Rational coordinate carrier for the split hyperbolic `5+5` model. -/
abbrev Vec55 := Fin 10 → ℚ

/-- Hyperbolic split pairing `Σ xᵢ yᵢ₊₅ + xᵢ₊₅ yᵢ`. -/
def splitPair55 (x y : Vec55) : ℚ :=
  x 0 * y 5 + x 5 * y 0 +
  x 1 * y 6 + x 6 * y 1 +
  x 2 * y 7 + x 7 * y 2 +
  x 3 * y 8 + x 8 * y 3 +
  x 4 * y 9 + x 9 * y 4

/-- Central sign `-I`. -/
def negAll (x : Vec55) : Vec55 := fun i => -x i

/-- Flip the first hyperbolic pair `(0,5)`. -/
def reflPair0 (x : Vec55) : Vec55 :=
  fun i => if i = 0 ∨ i = 5 then -x i else x i

/-- Flip the second hyperbolic pair `(1,6)`. -/
def reflPair1 (x : Vec55) : Vec55 :=
  fun i => if i = 1 ∨ i = 6 then -x i else x i

/-- Coordinate-preserving finite shadow of membership in `O(5,5)`. -/
def PreservesSplitPair (f : Vec55 → Vec55) : Prop :=
  ∀ x y, splitPair55 (f x) (f y) = splitPair55 x y

/-- The central sign preserves the split pairing. -/
theorem negAll_preserves_splitPair : PreservesSplitPair negAll := by
  intro x y
  simp [splitPair55, negAll]

/-- First pair reflection preserves the split pairing. -/
theorem reflPair0_preserves_splitPair : PreservesSplitPair reflPair0 := by
  intro x y
  simp [splitPair55, reflPair0]

/-- Second pair reflection preserves the split pairing. -/
theorem reflPair1_preserves_splitPair : PreservesSplitPair reflPair1 := by
  intro x y
  simp [splitPair55, reflPair1]

/-- The central sign is involutive. -/
theorem negAll_involutive : Function.Involutive negAll := by
  intro x
  ext i
  simp [negAll]

/-- First pair reflection is involutive. -/
theorem reflPair0_involutive : Function.Involutive reflPair0 := by
  intro x
  ext i
  fin_cases i <;> simp [reflPair0]

/-- Second pair reflection is involutive. -/
theorem reflPair1_involutive : Function.Involutive reflPair1 := by
  intro x
  ext i
  fin_cases i <;> simp [reflPair1]

/-- The two pair reflections commute. -/
theorem reflPair0_comm_reflPair1 (x : Vec55) :
    reflPair0 (reflPair1 x) = reflPair1 (reflPair0 x) := by
  ext i
  fin_cases i <;> simp [reflPair0, reflPair1]

/-- V4 composite of the two commuting pair reflections. -/
def reflPair01 (x : Vec55) : Vec55 := reflPair0 (reflPair1 x)

/-- The V4 composite is involutive. -/
theorem reflPair01_involutive : Function.Involutive reflPair01 := by
  intro x
  ext i
  fin_cases i <;> simp [reflPair01, reflPair0, reflPair1]

/-- The V4 composite preserves the split pairing. -/
theorem reflPair01_preserves_splitPair : PreservesSplitPair reflPair01 := by
  intro x y
  calc
    splitPair55 (reflPair01 x) (reflPair01 y)
        = splitPair55 (reflPair1 x) (reflPair1 y) := reflPair0_preserves_splitPair (reflPair1 x) (reflPair1 y)
    _ = splitPair55 x y := reflPair1_preserves_splitPair x y

/-- Finite projective equivalence modulo the central sign on vectors. -/
def ProjectiveSignEq (x y : Vec55) : Prop :=
  y = x ∨ y = negAll x

/-- Projective sign equivalence is reflexive. -/
theorem projectiveSignEq_refl (x : Vec55) : ProjectiveSignEq x x :=
  Or.inl rfl

/-- Applying the central sign is projectively invisible in this finite quotient shadow. -/
theorem projectiveSignEq_negAll (x : Vec55) : ProjectiveSignEq x (negAll x) :=
  Or.inr rfl

/-- Translation in coordinate `0`; affine, not an `O(5,5)` map. -/
def trans0 (a : ℚ) (x : Vec55) : Vec55 :=
  fun i => if i = 0 then x 0 + a else x i

/-- Reflection of coordinate `0`; affine Klein-bottle generator shadow. -/
def affineReflect0 (x : Vec55) : Vec55 :=
  fun i => if i = 0 then -x 0 else x i

/-- Coordinate-zero translation composition law. -/
theorem trans0_add (a b : ℚ) (x : Vec55) :
    trans0 a (trans0 b x) = trans0 (a + b) x := by
  ext i
  fin_cases i <;> simp [trans0]
  ring

/-- Coordinate-zero reflection is involutive. -/
theorem affineReflect0_involutive : Function.Involutive affineReflect0 := by
  intro x
  ext i
  fin_cases i <;> simp [affineReflect0]

/-- Finite affine Klein-bottle relation: `r t(a) r = t(-a)`. -/
theorem kleinBottle_affine_relation (a : ℚ) (x : Vec55) :
    affineReflect0 (trans0 a (affineReflect0 x)) = trans0 (-a) x := by
  ext i
  fin_cases i <;> simp [affineReflect0, trans0, add_comm]

/-- Closed finite packet for the theorem-safe `O(5,5)`/V4/Klein-bottle shadows. -/
theorem finite_o55_v4_klein_packet (x y : Vec55) :
    splitPair55 (negAll x) (negAll y) = splitPair55 x y ∧
    splitPair55 (reflPair0 x) (reflPair0 y) = splitPair55 x y ∧
    splitPair55 (reflPair1 x) (reflPair1 y) = splitPair55 x y ∧
    reflPair0 (reflPair0 x) = x ∧
    reflPair1 (reflPair1 x) = x ∧
    reflPair0 (reflPair1 x) = reflPair1 (reflPair0 x) ∧
    affineReflect0 (trans0 1 (affineReflect0 x)) = trans0 (-1) x := by
  exact ⟨negAll_preserves_splitPair x y,
    reflPair0_preserves_splitPair x y,
    reflPair1_preserves_splitPair x y,
    reflPair0_involutive x,
    reflPair1_involutive x,
    reflPair0_comm_reflPair1 x,
    kleinBottle_affine_relation 1 x⟩

end O55V4KleinBottleFinite
