import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

/-!
# Split-octonion derivation witness layer

This module is the Lean twin of the theorem-safe part of
`tools/sympy/split_octonion_derivation_classification.py`.

The external verifier computes the full rational linear system for derivations of
the Zorn split-octonion algebra and checks, with SymPy and Sage, that the
solution space has dimension `14`, matching the Lie algebra dimension of split
`G₂`.

This Lean file does **not** package that computational rank certificate as a
proof of the global real split classification `Aut(𝕆_s)=G_{2(2)}`.  Instead it
adds a native finite owner theorem: an explicit nonzero infinitesimal coordinate
rotation is a real derivation of the formalized split-octonion multiplication.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.DerivationWitness

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

/-- Closed finite packet for the native derivation witness layer. -/
theorem splitOctonion_derivationWitness_packet :
    IsDerivation rot01Derivation ∧
      rot01Derivation (addZ ePlus eMinus) = zeroZ ∧
      rot01Derivation up0 = negZ up1 := by
  exact ⟨rot01_is_derivation, rot01_kills_diagonal_unit, rot01_nonzero_on_up0⟩

end InfoGeometry.OperatorAlgebra.SplitOctonions.DerivationWitness
