import InfoGeometry.Canonical.AlgebraicStarEnvelope
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Optics.OperatorValuedConnection

/-!
# Operator-valued connection transport into an algebraic star envelope

This is the stagewise noncommutative bridge for the algebraic star envelope.
The stage injection is used only through its underlying ring homomorphism, so
the result is an instance of the general curvature transport theorem rather
than a scalar or diagonal model.
-/

noncomputable section

namespace InfoGeometry.Canonical.AlgebraicStarEnvelopeConnectionTransport

open InfoGeometry.Canonical.AlgebraicStarEnvelope
open InfoGeometry.Optics.OperatorValuedConnection
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

theorem stageInjection_curvature
    {Point Tangent : Type*} {i : I}
    (C : Connection (Point := Point) (Tangent := Tangent)
      (Value := Stage i))
    (p : Point) (X Y : Tangent) :
    stageInjection Stage sys i (curvature C p X Y) =
      curvature
        (mapConnection
          (stageInjection Stage sys i).toAlgHom.toRingHom C) p X Y := by
  exact mapConnection_curvature
    (stageInjection Stage sys i).toAlgHom.toRingHom C p X Y

end InfoGeometry.Canonical.AlgebraicStarEnvelopeConnectionTransport

end noncomputable section
