import InfoGeometry.Canonical.TKKJordanPairData

/-!
# TKK decomposition compatibility surface

The former file used diagonal `2 × 2` complex matrices as a surrogate for a
five-graded TKK Lie algebra and labelled commuting matrix calculations as
strong/Cartan structure.  The canonical owner already provides the genuine
graded Lie carrier and bracket-closure laws.  This file only forwards that
surface for legacy `proofs/` imports; it introduces no matrix carrier.
-/

namespace TKKCartanDecomposition

abbrev TKKGrading := TKKJordanPairData.TKKGrade

abbrev FiveGradedLieAlgebra (R : Type*) [CommRing R] :=
  TKKJordanPairData.FiveGradedLieAlgebra R

theorem bracket_grade_closed
    {R : Type*} [CommRing R]
    (G : FiveGradedLieAlgebra R)
    {i j k : TKKGrading}
    (hijk : TKKJordanPairData.gradeAdd i j = some k)
    {x y : G.L}
    (hx : x ∈ G.grade i) (hy : y ∈ G.grade j) :
    ⁅x, y⁆ ∈ G.grade k :=
  TKKJordanPairData.bracket_grade_closed G hijk hx hy

theorem bracket_grade_outside_zero
    {R : Type*} [CommRing R]
    (G : FiveGradedLieAlgebra R)
    {i j : TKKGrading}
    (hij : TKKJordanPairData.gradeAdd i j = none)
    {x y : G.L}
    (hx : x ∈ G.grade i) (hy : y ∈ G.grade j) :
    ⁅x, y⁆ = 0 :=
  TKKJordanPairData.bracket_grade_outside_zero G hij hx hy

end TKKCartanDecomposition
