import InfoGeometry.Algebra.JordanCayleyInversionOs
import InfoGeometry.Physics.Pin55Formal
import Mathlib.Tactic

/-!
# Determinant trichotomy for `J₂(𝕆_s)` coordinates

This file packages the finite determinant trichotomy
`isZero ∨ isNull ∨ isGeneric` for the 10-dimensional split octonionic Jordan
coordinate carrier `J₂(𝕆_s)`.

The determinant `det(X) = ξ₊·ξ₋ - ‖Z‖²` is recorded as a coordinate formula.
The file does **not** construct a `Pin(5,5)` action, does **not** prove any
invariance theorem under `Pin(5,5)` or `V4`, and does **not** identify the
Klein quadric with a conformal crossover surface.

The three labels are only case tags:
- `isZero`: `X = 0`
- `isNull`: `det(X) = 0` and `X ≠ 0`
- `isGeneric`: `det(X) ≠ 0`
-/

open InfoGeometry.Algebra.JordanCayleyInversionOs
open InfoGeometry.Physics.Pin55Formal
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

namespace InfoGeometry.Physics.OrbitClassification55

/-! ## 1. The 10D Jordan coordinate carrier and its determinant -/

/--
A J₂(𝕆_s) coordinate carrier in the finite 10D split-octonion packet.

    X = [[ξ₊, Z], [conj(Z), ξ₋]]

where `ξ₊, ξ₋ ∈ ℚ` are the light-cone coordinates and `Z ∈ 𝕆_s`
(Zorn 8-coordinate SplitOct cell).
-/
structure JordanMatrix10D where
  xp : ℚ    -- ξ₊
  xm : ℚ    -- ξ₋
  z : SplitOct  -- Z ∈ 𝕆_s
  deriving DecidableEq, Repr

namespace JordanMatrix10D

/-- Determinant: det(X) = ξ₊·ξ₋ - ‖Z‖².  This is the (5,5) quadratic form. -/
def det (X : JordanMatrix10D) : ℚ :=
  X.xp * X.xm - zornNormℚ X.z

/-- The zero matrix. -/
def zero : JordanMatrix10D := ⟨0, 0, zeroZ⟩

/-- A matrix is zero iff all components vanish. -/
def isZero (X : JordanMatrix10D) : Prop :=
  X = zero

/-! ## 2. Coordinate case-type inductive -/

/--
The three coordinate case types for `X ∈ J₂(𝕆_s)`.

* `isZero`: X = 0 — the singular crossover point.
* `isNull`: det(X) = 0, X ≠ 0 — the Klein quadric (scale-free lightrays).
* `isGeneric`: det(X) ≠ 0 — the interior of a cosmic aeon.
-/
inductive OrbitType (X : JordanMatrix10D) : Prop where
  | isZero : X = zero → OrbitType X
  | isNull : X ≠ zero → X.det = 0 → OrbitType X
  | isGeneric : X.det ≠ 0 → OrbitType X

/-! ## 3. Determinant trichotomy -/

/--
Every `X ∈ J₂(𝕆_s)` is assigned one of the coordinate case types by a
decidable case analysis on `X.det`.
-/
theorem orbit_classification (X : JordanMatrix10D) : OrbitType X := by
  by_cases hzero : X = zero
  · exact OrbitType.isZero hzero
  · by_cases hdet : X.det = 0
    · exact OrbitType.isNull hzero hdet
    · exact OrbitType.isGeneric hdet

/-! ## 4. Trivial readbacks -/

/-- A tautological determinant self-readback.  No group action is constructed here. -/
theorem determinant_self_eq (X : JordanMatrix10D) :
    X.det = X.det := rfl

/--
The trichotomy `X = 0 ∨ X.det = 0 ∨ X.det ≠ 0` is a pure case split.
It does not encode group invariance.
-/
theorem det_trichotomy (X : JordanMatrix10D) :
    (X = zero) ∨ (X.det = 0) ∨ (X.det ≠ 0) := by
  by_cases hzero : X = zero
  · exact Or.inl hzero
  · by_cases hdet : X.det = 0
    · exact Or.inr (Or.inl hdet)
    · exact Or.inr (Or.inr hdet)

end JordanMatrix10D

end InfoGeometry.Physics.OrbitClassification55
