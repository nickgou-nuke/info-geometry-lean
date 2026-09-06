import Omega.Conclusion.Window6RadialObservableAlgebra

namespace Omega.Conclusion

/-
The source theorem also contains the concrete boundary indicator and its
least-squares error.  The owner currently available in Lean proves the exact
finite radial-algebra core: shell factorisation and the four cubic Lagrange
idempotents.  Keep this theorem at that proved scope rather than certifying the
unformalized boundary projection by `True`.
-/
/-- Finite algebraic core of `thm:conclusion-window6-boundary-radial-defect`. -/
theorem paper_conclusion_window6_boundary_radial_defect :
    conclusion_window6_radial_observable_algebra_statement := by
  exact paper_conclusion_window6_radial_observable_algebra

end Omega.Conclusion
