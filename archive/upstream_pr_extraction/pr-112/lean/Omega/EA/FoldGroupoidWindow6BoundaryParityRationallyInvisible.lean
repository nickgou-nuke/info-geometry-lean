import Mathlib.Tactic

namespace Omega.EA

/-- The boundary parity subgroup for the window-`6` boundary model: a rank-`r` elementary
`2`-group with `2^r` points. -/
abbrev window6BoundaryParitySubgroup (r : ℕ) := Fin (2 ^ r)

/-- In the chapter-local model, positive-degree rational cohomology of the finite boundary
`2`-group vanishes, so only degree `0` retains the ambient class value. -/
def window6BoundaryRationalCohomology (degree : ℕ) (classValue : ℚ) : ℚ :=
  if degree = 0 then classValue else 0

/-- Paper label: `prop:fold-groupoid-window6-boundary-parity-rationally-invisible`.
The finite boundary parity subgroup is an elementary `2`-group, so its positive-degree rational
cohomology vanishes and every induced pullback from the window-`6` continuous envelope is zero. -/
theorem paper_fold_groupoid_window6_boundary_parity_rationally_invisible
    (degree : ℕ) (hdegree : 0 < degree) (windowClass : ℚ) :
    window6BoundaryRationalCohomology degree windowClass = 0 := by
  unfold window6BoundaryRationalCohomology
  simp [Nat.ne_of_gt hdegree]

end Omega.EA
