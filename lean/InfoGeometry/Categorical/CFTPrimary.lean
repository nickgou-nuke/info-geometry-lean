import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

abbrev PrimaryState := ℝ × ℝ

namespace PrimaryState

abbrev Δ (p : PrimaryState) : ℝ := p.1
abbrev c (p : PrimaryState) : ℝ := p.2

end PrimaryState
