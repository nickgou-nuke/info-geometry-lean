import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Split-octonion derivation property layer

This module is the Lean-native finite derivation layer for the explicit Zorn
split-octonion multiplication.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.DerivationData

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/-- Coordinatewise addition on the integer Zorn model. -/
def addZ (X Y : SplitOct) : SplitOct :=
  ⟨X.a + Y.a, X.b + Y.b, X.x0 + Y.x0, X.x1 + Y.x1, X.x2 + Y.x2,
    X.y0 + Y.y0, X.y1 + Y.y1, X.y2 + Y.y2⟩

/-- A map is a derivation for the explicit Zorn product. -/
def IsDerivation (D : SplitOct → SplitOct) : Prop :=
  ∀ X Y : SplitOct, D (mulZ X Y) = addZ (mulZ (D X) Y) (mulZ X (D Y))

/-- Infinitesimal rotation in the `0-1` vector-slot plane, applied to both Zorn vector slots. -/
def rot01Derivation (X : SplitOct) : SplitOct :=
  ⟨0, 0, X.x1, -X.x0, 0, X.y1, -X.y0, 0⟩

/-- The coordinate rotation is additive on the explicit Zorn carrier. -/
theorem rot01_preserves_add (X Y : SplitOct) :
    rot01Derivation (addZ X Y) = addZ (rot01Derivation X) (rot01Derivation Y) := by
  cases X
  cases Y
  unfold rot01Derivation addZ
  congr <;> ring

/-- The coordinate rotation `rot01Derivation` is a native split-octonion derivation. -/
theorem rot01_is_derivation : IsDerivation rot01Derivation := by
  intro X Y
  cases X
  cases Y
  unfold rot01Derivation addZ mulZ
  congr <;> ring

/-- The coordinate rotation kills the diagonal idempotent sum, as every derivation should. -/
theorem rot01_kills_diagonal_unit : rot01Derivation (addZ ePlus eMinus) = zeroZ := by
  simp [rot01Derivation, addZ, ePlus, eMinus, zeroZ]

/-- The coordinate rotation is nonzero on `up0`; this is not the zero derivation. -/
theorem rot01_nonzero_on_up0 : rot01Derivation up0 = negZ up1 := by
  simp [rot01Derivation, up0, up1, negZ]

end InfoGeometry.OperatorAlgebra.SplitOctonions.DerivationData
