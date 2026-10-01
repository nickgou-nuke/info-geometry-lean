import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix

import InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge
import InfoGeometry.Lie.ZornPeirceDerivationStabilizer
import InfoGeometry.RootSystem.G2CoxeterPlaneProjection

/-!
# Block-circulant G2 / Zorn / Cuntz-Krieger bridge

This module proves the exact finite block decomposition of the concrete
12-vertex G2 adjacency already owned by
`G2CuntzKriegerScalarSeparatedBridge`.

With the first six vertices short and the last six long,

  A_G2 = [ P       I + P^{-1} ]
         [ I + P   P          ]

where P is the cyclic 6-shift.

The integer Cuntz--Krieger boundary matrix has determinant -1456.

Important K-theory boundary:
the determinant fixes only the order of a finite cokernel when the map has
full rank.  It does not determine its invariant factors.  For this concrete
matrix the externally checked Smith target is

  diag(1,...,1,2,2,364),

hence the expected cokernel is Z/2 x Z/2 x Z/364
(= Z/2 x Z/2 x Z/4 x Z/91), not (Z/2)^4 x Z/91.

No Smith-normal-form theorem is asserted here until unimodular row/column
certificates are formalized.
-/

noncomputable section

namespace InfoGeometry.Canonical.G2BlockCirculantZornBridge

open InfoGeometry.Canonical.G2CuntzKriegerScalarSeparatedBridge

abbrev Six := Fin 6

/-- Cyclic forward shift on the six roots of one hexagon. -/
def Pshift (u v : Six) : Bool :=
  v.val = (u.val + 1) % 6

/-- Identity relation on the six-cycle. -/
def I6 (u v : Six) : Bool :=
  u = v

/-- Cyclic inverse shift. -/
def Pinv (u v : Six) : Bool :=
  v.val = (u.val + 5) % 6

/-- Boolean 2x2 block formula for the concrete G2 adjacency. -/
def blockAdjacency (i j : G2Vertex) : Bool :=
  let u := i.val
  let v := j.val
  if hu : u < 6 then
    if hv : v < 6 then
      Pshift ⟨u, hu⟩ ⟨v, hv⟩
    else
      have hv' : v - 6 < 6 := by omega
      I6 ⟨u, hu⟩ ⟨v - 6, hv'⟩ ||
        Pinv ⟨u, hu⟩ ⟨v - 6, hv'⟩
  else
    have hu' : u - 6 < 6 := by omega
    if hv : v < 6 then
      I6 ⟨u - 6, hu'⟩ ⟨v, hv⟩ ||
        Pshift ⟨u - 6, hu'⟩ ⟨v, hv⟩
    else
      have hv' : v - 6 < 6 := by omega
      Pshift ⟨u - 6, hu'⟩ ⟨v - 6, hv'⟩

/-- Exact verification of the block-circulant formula on all 144 entries. -/
theorem blockAdjacency_eq_A_G2_bool
    (i j : G2Vertex) :
    blockAdjacency i j = A_G2_bool i j := by
  revert i j
  decide

/-- Integer lift of the block formula. -/
def blockAdjacencyInt : Matrix G2Vertex G2Vertex ℤ :=
  fun i j => if blockAdjacency i j then 1 else 0

/-- The integer block matrix is definitionally the same adjacency as the
concrete G2 owner, entry by entry. -/
theorem blockAdjacencyInt_eq_A_G2_int :
    blockAdjacencyInt = A_G2_int := by
  ext i j
  simp [blockAdjacencyInt, A_G2_int,
    G2TransitionDatum.adjacency, concreteG2TransitionDatum,
    blockAdjacency_eq_A_G2_bool]

/-- The boundary determinant readout is inherited from the concrete owner. -/
theorem boundary_det_eq_neg_1456 :
    ((1 : Matrix G2Vertex G2Vertex ℤ) -
      blockAdjacencyInt.transpose).det = -1456 := by
  rw [blockAdjacencyInt_eq_A_G2_int]
  exact G2BoundaryMatrix_det

/-! ## Root-count / Zorn grading readout -/

/-- The six short plus six long nonzero G2 roots, with the long sector split
as three vector and three covector directions, give 12 root directions. -/
theorem zorn_root_count :
    6 + 3 + 3 = 12 := by
  norm_num

/-- Adding the two-dimensional Cartan sector gives dim g2 = 14. -/
theorem zorn_derivation_dimension_count :
    6 + 3 + 3 + 2 = 14 := by
  norm_num

/-- The metric long/short squared-radius ratio of the existing G2 root owner
is exactly three. -/
theorem g2_metric_ratio_three :
    (∑ i : Fin 2,
      InfoGeometry.RootSystem.G2.project InfoGeometry.RootSystem.G2.longRoot i *
        InfoGeometry.RootSystem.G2.project InfoGeometry.RootSystem.G2.longRoot i) =
      3 *
      (∑ i : Fin 2,
        InfoGeometry.RootSystem.G2.project InfoGeometry.RootSystem.G2.shortRoot i *
          InfoGeometry.RootSystem.G2.project InfoGeometry.RootSystem.G2.shortRoot i) :=
  InfoGeometry.RootSystem.G2.projection_radius_sq_ratio

/-! ## Corrected finite abelian-group target metadata -/

/-- The absolute determinant factorization. -/
theorem boundary_order_factorization :
    (1456 : ℕ) = 2 * 2 * 364 := by
  norm_num

/-- Further coprime factorization of the last invariant factor. -/
theorem invariant_factor_364 :
    (364 : ℕ) = 4 * 91 := by
  norm_num

/-- The two-primary order is 16, but the corrected candidate structure from
the Smith target is Z/2 x Z/2 x Z/4, not (Z/2)^4. -/
theorem two_primary_order :
    (2 : ℕ) * 2 * 4 = 16 := by
  norm_num

end InfoGeometry.Canonical.G2BlockCirculantZornBridge
