import InfoGeometry.Canonical.CayleyConjugationExteriorDualityBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Cayley middle grading versus Peirce and exterior parity

On the concrete `1 + 3 + 3 + 1` coordinate carrier, this owner records the
sign bookkeeping behind the old Witten/Möbius parity discussion.  The
standard degree parity has signs `(+,-,+,-)`, while the Peirce grading used
here has signs `(+,+,-,-)`.  Their product is the Cayley middle sign flip
`(+,-,-,+)`.

This is a finite coordinate identity.  It does not identify the Peirce
grading with the exterior-degree grading on a split-octonion algebra, nor
does it assert an analytic Witten index.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyWittenPeirceParityBridge

open InfoGeometry.Canonical.CayleyConjugationExteriorDualityBridge

abbrev Coord :=
  InfoGeometry.Canonical.CayleyConjugationExteriorDualityBridge.Coord
abbrev CoordEnd := Module.End ℝ Coord

/-- The concrete Peirce sign pattern `(+,+,-,-)` on the graded coordinates. -/
def peirceGrading : CoordEnd where
  toFun x := (x.1, x.2.1, -x.2.2.1, -x.2.2.2)
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' c x := by ext <;> simp

@[simp] theorem peirceGrading_apply (x : Coord) :
    peirceGrading x = (x.1, x.2.1, -x.2.2.1, -x.2.2.2) := rfl

/-- The exterior-degree/Witten parity pattern `(+,-,+,-)`. -/
abbrev exteriorFermionParity : CoordEnd := chiralGrading

theorem peirceGrading_sq : peirceGrading * peirceGrading = 1 := by
  apply LinearMap.ext
  intro x
  ext <;> simp [peirceGrading]

theorem exteriorFermionParity_sq :
    exteriorFermionParity * exteriorFermionParity = 1 := by
  simpa [exteriorFermionParity] using chiralGrading_sq

theorem peirceGrading_comm_exteriorFermionParity :
    peirceGrading * exteriorFermionParity =
      exteriorFermionParity * peirceGrading := by
  apply LinearMap.ext
  intro x
  ext <;> simp [peirceGrading, exteriorFermionParity, chiralGrading]

theorem middleSignFlip_eq_peirceGrading_mul_exteriorFermionParity :
    middleSignFlip = peirceGrading * exteriorFermionParity := by
  apply LinearMap.ext
  intro x
  ext <;> simp [peirceGrading, exteriorFermionParity, chiralGrading,
    middleSignFlip]

theorem middleSignFlip_eq_exteriorFermionParity_mul_peirceGrading :
    middleSignFlip = exteriorFermionParity * peirceGrading := by
  calc
    middleSignFlip = peirceGrading * exteriorFermionParity :=
      middleSignFlip_eq_peirceGrading_mul_exteriorFermionParity
    _ = exteriorFermionParity * peirceGrading :=
      peirceGrading_comm_exteriorFermionParity

theorem peirceGrading_anticommutes_hodgeStar :
    peirceGrading * hodgeStar = -(hodgeStar * peirceGrading) := by
  apply LinearMap.ext
  intro x
  ext <;> simp [peirceGrading, hodgeStar]

theorem exteriorFermionParity_anticommutes_hodgeStar :
    exteriorFermionParity * hodgeStar =
      -(hodgeStar * exteriorFermionParity) := by
  simpa [exteriorFermionParity] using chiralGrading_anticommutes_hodgeStar

theorem middleSignFlip_comm_hodgeStar :
    middleSignFlip * hodgeStar = hodgeStar * middleSignFlip := by
  apply LinearMap.ext
  intro x
  ext <;> simp [middleSignFlip, hodgeStar]

theorem cayleyConj_eq_scalarExchange_mul_peirce_mul_exteriorParity :
    cayleyConj = scalarExchange * peirceGrading * exteriorFermionParity := by
  rw [cayleyConj_eq_scalarExchange_mul_middleSignFlip,
    middleSignFlip_eq_peirceGrading_mul_exteriorFermionParity]
  simp only [mul_assoc]

end InfoGeometry.Canonical.CayleyWittenPeirceParityBridge
