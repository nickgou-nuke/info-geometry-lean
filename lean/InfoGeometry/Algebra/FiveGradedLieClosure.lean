import InfoGeometry.Algebra.FiveGradedLieJacobi
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Closure data for a five-graded Lie carrier

The existing `FiveGradedLieData` records homogeneous components inside an
ambient Lie algebra.  This owner adds the missing typed closure contract.  It
does not identify the carrier with an exceptional Lie algebra and it does not
assert endpoint compensation: that statement is explicit data.
-/

namespace InfoGeometry.Algebra.FiveGradedLieClosureData

open InfoGeometry.Algebra.FiveGradedTKK
open InfoGeometry.Algebra.FiveGradedLieAntisymmetry

variable (R L : Type*) [CommRing R]
variable [LieRing L] [LieAlgebra R L]

/-- A homogeneous bracket has the expected sum of weights whenever that sum is
represented by one of the five declared weights. -/
structure FiveGradedLieClosure (G : FiveGradedLieData R L) where
  bracket_mem : ∀ (u v w : Weight5) (x y : L),
    x ∈ G.component u → y ∈ G.component v →
    Weight5.toInt w = Weight5.toInt u + Weight5.toInt v →
    ⁅x, y⁆ ∈ G.component w

namespace ClosureData

variable {R L : Type*} [CommRing R]
variable [LieRing L] [LieAlgebra R L]
variable {G : FiveGradedLieData R L}

theorem bracket_mem_of_weight_sum
    (C : FiveGradedLieClosure R L G)
    (u v w : Weight5) (x y : L)
    (hx : x ∈ G.component u) (hy : y ∈ G.component v)
    (hw : Weight5.toInt w = Weight5.toInt u + Weight5.toInt v) :
    ⁅x, y⁆ ∈ G.component w := by
  exact C.bracket_mem u v w x y hx hy hw

/-- The endpoint relation is deliberately a witness, not a consequence of
the grading contract. -/
structure EndpointCompensation (G : FiveGradedLieData R L)
    (C : FiveGradedLieClosure R L G) where
  ePlus : L
  eMinus : L
  hCartan : L
  ePlus_mem : (ePlus : L) ∈ G.component Weight5.pos_two
  eMinus_mem : (eMinus : L) ∈ G.component Weight5.neg_two
  hCartan_mem : (hCartan : L) ∈ G.component Weight5.zero
  compensation : ⁅ePlus, eMinus⁆ = hCartan

theorem endpoint_compensation
    {C : FiveGradedLieClosure R L G}
    (H : EndpointCompensation G C) :
    ⁅H.ePlus, H.eMinus⁆ = H.hCartan :=
  H.compensation

end ClosureData

end InfoGeometry.Algebra.FiveGradedLieClosureData
