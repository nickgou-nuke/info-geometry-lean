import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity

/-!
# Coordinate prefixes for admissible seven-bases

This owner records the coordinate data that are already present in the
admissible-basis carrier.  It deliberately does not assign geometric fiber
cardinalities: those require a separate semantic classification theorem.
-/

namespace InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

abbrev AdmissibleBasis7Carrier :=
  {v : Fin 7 → SplitOctF2 // admissibleBasis7 v}

def basisCoordinates (v : AdmissibleBasis7Carrier) : Fin 7 → SplitOctF2 :=
  v.1

def basisPrefix1 (v : AdmissibleBasis7Carrier) : SplitOctF2 :=
  basisCoordinates v 0

def basisPrefix2 (v : AdmissibleBasis7Carrier) : SplitOctF2 :=
  basisCoordinates v 1

def basisPrefix3 (v : AdmissibleBasis7Carrier) : SplitOctF2 :=
  basisCoordinates v 2

def basisPrefix4 (v : AdmissibleBasis7Carrier) : SplitOctF2 :=
  basisCoordinates v 3

def basisPrefix5 (v : AdmissibleBasis7Carrier) : SplitOctF2 :=
  basisCoordinates v 4

def basisPrefix6 (v : AdmissibleBasis7Carrier) : SplitOctF2 :=
  basisCoordinates v 5

def basisPrefix7 (v : AdmissibleBasis7Carrier) : SplitOctF2 :=
  basisCoordinates v 6

theorem basisCoordinates_reconstruct (v : AdmissibleBasis7Carrier) (i : Fin 7) :
    basisCoordinates v i = v.1 i := by
  rfl

theorem basisCoordinates_eq_basisRestriction7
    (f : SplitOctF2Aut) :
    basisCoordinates
        ⟨basisRestriction7 f, basisRestriction7_admissible f⟩ =
      basisRestriction7 f := by
  rfl

theorem basisCoordinates_injective :
    Function.Injective basisCoordinates := by
  intro v w h
  apply Subtype.ext
  exact h

theorem basisPrefixes_are_coordinates
    (v : AdmissibleBasis7Carrier) :
    (basisPrefix1 v, basisPrefix2 v, basisPrefix3 v) =
      (basisCoordinates v 0, basisCoordinates v 1, basisCoordinates v 2) := by
  rfl

end InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
