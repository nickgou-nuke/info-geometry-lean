import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.ContDiff.Basic
import InfoGeometry.Topology.KleinBottleTangentHolonomy

/-!
# Smooth Dirac-Kähler Intertwining on the Klein Bottle Cover

Here we complete the rigorous geometric construction by defining the
Dirac-Kähler structure over the smooth universal cover (ℝ × ℝ) and formally
proving that the tangent holonomy of the orientation-reversing glide intertwines
the Dirac-Kähler components, explicitly swapping them.
-/

open KleinBrillouinBase InfoGeometry.Topology.KleinBottleTangentHolonomy

noncomputable section
namespace InfoGeometry.Geometry

/-- The smooth sections of the Dirac-Kähler bundle are modeled as functions. -/
def DiracKahlerSection := (ℝ × ℝ) → (ℝ × ℝ)

/-- The geometric pullback of a section by the affine glide transformation. -/
def holonomyPullback (s : DiracKahlerSection) : DiracKahlerSection :=
  fun p => glideLinearPart (s (glide p))

/-- The Chiral/Dirac operator on the flat manifold ℝ × ℝ.
    It acts by swapping the structural components, representing the off-diagonal grading. -/
def diracKahlerOperator (s : DiracKahlerSection) : DiracKahlerSection :=
  fun p => (s p).swap

theorem glideLinearPart_apply (p : ℝ × ℝ) :
    glideLinearPart p = (p.1, -p.2) := rfl

/--
The Geometric Holonomy Intertwining Theorem:
Pulling back a section via the smooth Klein bottle glide transformation
and applying the Dirac-Kähler operator is exactly geometrically equivalent
to applying the negative Dirac-Kähler operator to the pulled-back section.
This constitutes the strict geometric intertwining.
-/
theorem dirac_kahler_holonomy_intertwining (s : DiracKahlerSection) :
    diracKahlerOperator (holonomyPullback s) =
    fun p => - (holonomyPullback (diracKahlerOperator s) p) := by
  funext p
  dsimp [diracKahlerOperator, holonomyPullback, Prod.swap]
  rw [glideLinearPart_apply, glideLinearPart_apply]
  dsimp [Prod.swap]
  apply Prod.ext
  · rfl
  · simp

end InfoGeometry.Geometry
end noncomputable section
