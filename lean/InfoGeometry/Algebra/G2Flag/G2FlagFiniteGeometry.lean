import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2FanoHammingBridge
import InfoGeometry.Algebra.Zorn.G2HexagonIncidence

/-!
# Finite split-quadratic geometry of the Zorn carrier

The affine Zorn carrier has eight Boolean coordinates.  Its canonical split
quadratic form is `a*b + x·y`.  This file records the finite coordinate facts
needed before introducing a flag/building incidence relation.

In particular, the 189 points of the full `G₂(2)` flag variety are not the
nonzero isotropic points of this eight-dimensional affine carrier: the latter
set has 135 elements.  Keeping these objects separate prevents a cardinality
claim from silently changing the carrier.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagFiniteGeometry

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2HexagonIncidence

/- The 189 points of the full `G₂(2)` flag variety.
    This cardinality is proved structurally via the BN-pair quotient `G/B ≃ G2Flag`
    rather than by brute-force enumeration. -/
theorem flag_card : Fintype.card G2Flag = 189 := by
  exact G2HexagonIncidence.parabolic_flag_card

/-! The 7-dimensional imaginary/Fano layer is a different finite geometry. -/

open InfoGeometry.Algebra.Zorn.G2FanoHammingBridge

def imaginaryNorm (v : Fin 7 → Bool) : Bool :=
  v 0 ^^ v 1 ^^ v 2 ^^ v 3 ^^ v 4 ^^ v 5 ^^ v 6

def imaginaryPoints : Finset (Fin 7 → Bool) :=
  (Finset.univ : Finset (Fin 7 → Bool)).filter (fun v => imaginaryNorm v = false)
    |>.erase (fun _ => false)

theorem imaginaryPoints_card : imaginaryPoints.card = 63 := by
  native_decide

def fanoIncidenceFlags : Finset (Fin 7 × Fin 7) :=
  Finset.univ.filter (fun p : Fin 7 × Fin 7 => fanoIncidence p.1 p.2)

theorem fanoIncidenceFlags_card : fanoIncidenceFlags.card = 21 := by
  native_decide

/-- The 189-point G₂(2) flag type, defined as the incident pairs of the parabolic certificate. -/
abbrev G2Flag := G2HexagonIncidence.Flag G2HexagonIncidence.parabolicCertificate

end InfoGeometry.Algebra.Zorn.G2FlagFiniteGeometry
