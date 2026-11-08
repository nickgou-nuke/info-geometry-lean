import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Real.Basic

noncomputable section

namespace InfoGeometry.Geometry

/-- The "master bridge" glide convention: translation in x, reflection in y. -/
def glideMaster (p : ℝ × ℝ) : ℝ × ℝ := (p.1 + 1, -p.2)

/-- The "quotient deck generator" glide convention: reflection in x, translation in y. -/
def glideDeck (p : ℝ × ℝ) : ℝ × ℝ := (-p.1, p.2 + 1)

/-- The coordinate transformation that maps one convention to the other is simply swapping the axes. -/
def glideCoordinateSwap : (ℝ × ℝ) ≃ (ℝ × ℝ) :=
  Equiv.prodComm ℝ ℝ

theorem glide_conventions_conjugate (p : ℝ × ℝ) :
    glideCoordinateSwap (glideMaster (glideCoordinateSwap.symm p)) = glideDeck p := by
  rfl

end InfoGeometry.Geometry
end noncomputable section
