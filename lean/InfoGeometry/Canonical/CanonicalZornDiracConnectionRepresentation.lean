import InfoGeometry.Canonical.CanonicalZornRealSpin44
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CanonicalZornCliffordRepresentation
import InfoGeometry.Optics.OperatorValuedConnection

/-!
# Dirac-valued connection readout for the real Zorn representation

The existing real split `(4,4)` Zorn representation supplies gamma operators
on `DiracSpinor16`.  This owner places those operators in the repository's
algebraic operator-valued connection datum.  It proves the two independent
readouts that are available at this level: the connection curvature is the
ordered gamma commutator, and each gamma square is the represented quadratic
form.  No differential Lichnerowicz identity is inferred from these constant
data alone.
-/

noncomputable section

namespace CanonicalZornDiracConnectionRepresentation

open CanonicalZornRealSpin44
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Optics.OperatorValuedConnection

abbrev DiracEnd :=
  Module.End ℝ CanonicalZornCliffordRepresentation.DiracSpinor16

def realGammaConnection :
    Connection (Point := Unit) (Tangent := RealSplit44) (Value := DiracEnd) where
  form := fun _ X => realGammaLinear X
  derivative := fun _ _ _ => 0
  derivative_swap := by intro; simp
  derivative_same := by intro; simp

theorem realGammaConnection_curvature (X Y : RealSplit44) :
    curvature realGammaConnection () X Y =
      realGammaLinear X * realGammaLinear Y -
        realGammaLinear Y * realGammaLinear X := by
  simp [curvature, realGammaConnection, wedgeSquare]

theorem realGammaConnection_curvature_swap (X Y : RealSplit44) :
    curvature realGammaConnection () Y X =
      -curvature realGammaConnection () X Y := by
  exact curvature_swap realGammaConnection () X Y

theorem realGammaConnection_gamma_square (X : RealSplit44) :
    realGammaLinear X * realGammaLinear X =
      algebraMap ℝ DiracEnd (realQuadratic44 X) := by
  exact realGamma_sq X

theorem realGammaConnection_gamma_square_as_curvature_free_diagonal
    (X : RealSplit44) :
    curvature realGammaConnection () X X = 0 ∧
      realGammaLinear X * realGammaLinear X =
        algebraMap ℝ DiracEnd (realQuadratic44 X) := by
  exact ⟨curvature_same realGammaConnection () X,
    realGammaConnection_gamma_square X⟩

end CanonicalZornDiracConnectionRepresentation
