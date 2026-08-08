import Mathlib.Tactic

/-!
# Finite `G₂(2)` split Cayley hexagon incidence property ledger

This module is the Lean twin of
`tools/sympy/g2_2_hexagon_incidence_property.py`.

The runtime property uses GAP/Atlas to recover the unique `G₂(2)`-invariant
63-line orbit in the degree-63 action, verifies the split Cayley hexagon
incidence parameters, and records how the committed outer `C₂` involution acts
on that line system.

Scope boundary:

* The explicit incidence enumeration is a runtime property, not reproduced by
  kernel enumeration here.
* The fixed points of the outer involution are recorded as a seven-point set.
* Under the property line system, the fixed point set has only three all-fixed
  lines, so this module deliberately does **not** assert a Fano-plane fixed
  subgeometry.
-/

namespace InfoGeometry.OperatorAlgebra.G2TwoHexagonIncidenceWitness

/-- Number of points in the degree-63 split Cayley hexagon action. -/
def pointCount : Nat := 63

/-- Number of lines in the recovered invariant line orbit. -/
def lineCount : Nat := 63

/-- Each line contains three points. -/
def lineSize : Nat := 3

/-- Each point is incident with three lines. -/
def pointDegree : Nat := 3

/-- The property incidence graph diameter. -/
def incidenceGraphDiameter : Nat := 6

/-- The property incidence graph girth. -/
def incidenceGraphGirth : Nat := 12

/-- Number of `G₂(2)`-invariant line orbits satisfying the hexagon parameters. -/
def candidateLineOrbitCount : Nat := 1

/-- Number of points fixed by the chosen outer `C₂` property. -/
def fixedPointCount : Nat := 7

/-- Number of lines whose three points are all fixed by the outer `C₂` property. -/
def allFixedPointLineCount : Nat := 3

/-- Number of lines fixed setwise by the outer `C₂` property. -/
def setwiseFixedLineCount : Nat := 9

/-- Fano plane line count for comparison only. -/
def fanoPlaneLineCount : Nat := 7

/-- Hexagon point/line balance in the property `H(2)` incidence system. -/
theorem point_count_eq_line_count : pointCount = lineCount := by
  rfl

/-- Total incidences counted from the point side. -/
def pointSideIncidences : Nat := pointCount * pointDegree

/-- Total incidences counted from the line side. -/
def lineSideIncidences : Nat := lineCount * lineSize

/-- The property incidence counts agree: `63 * 3 = 63 * 3`. -/
theorem incidence_count_accounting : pointSideIncidences = lineSideIncidences := by
  norm_num [pointSideIncidences, lineSideIncidences, pointCount, pointDegree, lineCount, lineSize]

/-- The incidence graph has the generalized-hexagon diameter/girth profile. -/
theorem hexagon_graph_profile :
    incidenceGraphDiameter = 6 ∧ incidenceGraphGirth = 12 := by
  decide

/-- The runtime search found a unique invariant line orbit with the target parameters. -/
theorem unique_candidate_line_orbit_count : candidateLineOrbitCount = 1 := by
  rfl

/-- The outer property has seven fixed points in the degree-63 action. -/
theorem outer_property_fixed_point_count : fixedPointCount = 7 := by
  rfl

/-- Only three property lines have all three points fixed by the outer property. -/
theorem all_fixed_point_line_count_eq_three : allFixedPointLineCount = 3 := by
  rfl

/-- Nine property lines are fixed setwise by the outer property. -/
theorem setwise_fixed_line_count_eq_nine : setwiseFixedLineCount = 9 := by
  rfl

/--
Under the property split Cayley hexagon line system, the seven fixed points do
not carry the seven all-fixed lines of a Fano plane.
-/
theorem fixed_points_not_fano_plane_by_all_fixed_line_count :
    allFixedPointLineCount ≠ fanoPlaneLineCount := by
  norm_num [allFixedPointLineCount, fanoPlaneLineCount]

end InfoGeometry.OperatorAlgebra.G2TwoHexagonIncidenceWitness
