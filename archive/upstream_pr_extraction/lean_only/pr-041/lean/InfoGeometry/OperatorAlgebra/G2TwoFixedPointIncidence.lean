import Mathlib.Tactic

/-!
# Fixed-point incidence ledger for the `G₂(2)` outer `C₂` property

This module is the Lean twin of
`tools/sympy/g2_2_fixed_point_incidence.py`.

The GAP verifier reconstructs the degree-63 split Cayley hexagon point graph
from the Atlas action of `G₂(2)` as the invariant orbital graph of valency `6`.
Its `63` triangles are used as the `63` lines of `H(2)`.

For the outer `C₂` representative recorded in
`G2TwoAutomorphismTheorem`, the fixed point list is
`[1, 19, 30, 32, 41, 42, 54]`.  Under the reconstructed `H(2)` incidence,
these seven points contain exactly `3` internal lines, not `7`.  Thus this file
records a theorem-safe boundary: the fixed set is a seven-point invariant set,
but it is not promoted here to a Fano-plane subgeometry.
-/

namespace InfoGeometry.OperatorAlgebra.G2TwoFixedPointIncidence

/-- Degree of the Atlas point action used for the split Cayley hexagon point graph. -/
def h2PointCount : Nat := 63

/-- Number of edges in the valency-six point graph: `63 * 6 / 2 = 189`. -/
def h2PointGraphEdgeCount : Nat := 189

/-- Number of triangle-lines reconstructed in the point graph. -/
def h2LineCount : Nat := 63

/-- Number of points fixed by the chosen outer `C₂` representative. -/
def outerC2FixedPointCount : Nat := 7

/-- Number of point-graph edges inside the fixed seven-point set. -/
def fixedInternalEdgeCount : Nat := 9

/-- Number of reconstructed `H(2)` lines entirely inside the fixed set. -/
def fixedInternalLineCount : Nat := 3

/-- Number of reconstructed `H(2)` lines meeting the fixed set. -/
def fixedIncidentLineCount : Nat := 15

/-- The number of lines in a Fano plane.  Used only as a count separator. -/
def fanoPlaneLineCount : Nat := 7

/-- GAP fixed-point list for the selected representative. -/
def outerC2FixedPointList : List Nat := [1, 19, 30, 32, 41, 42, 54]

/-- GAP internal fixed lines for the selected representative and incidence. -/
def fixedInternalLines : List (List Nat) :=
  [[1, 19, 41], [19, 30, 42], [19, 32, 54]]

/-- The fixed-point list has seven entries. -/
theorem outerC2FixedPointList_length :
    outerC2FixedPointList.length = outerC2FixedPointCount := by
  norm_num [outerC2FixedPointList, outerC2FixedPointCount]

/-- The internal fixed-line list has three entries. -/
theorem fixedInternalLines_length :
    fixedInternalLines.length = fixedInternalLineCount := by
  norm_num [fixedInternalLines, fixedInternalLineCount]

/-- Point-graph edge accounting for the degree-63 valency-six graph. -/
theorem h2_point_graph_edge_accounting :
    2 * h2PointGraphEdgeCount = h2PointCount * 6 := by
  norm_num [h2PointGraphEdgeCount, h2PointCount]

/-- The three internal fixed lines account for the nine internal fixed edges. -/
theorem fixed_internal_line_edge_accounting :
    fixedInternalLineCount * 3 = fixedInternalEdgeCount := by
  norm_num [fixedInternalLineCount, fixedInternalEdgeCount]

/-- Count separator: this fixed set has three internal lines, not seven. -/
theorem fixedInternalLineCount_ne_fanoPlaneLineCount :
    fixedInternalLineCount ≠ fanoPlaneLineCount := by
  norm_num [fixedInternalLineCount, fanoPlaneLineCount]

end InfoGeometry.OperatorAlgebra.G2TwoFixedPointIncidence
