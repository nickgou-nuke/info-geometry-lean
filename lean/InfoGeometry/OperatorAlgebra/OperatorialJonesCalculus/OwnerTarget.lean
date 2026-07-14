import Mathlib
import InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus.PolarizationProjectors

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus

/-! ## 5. Owner target -/

/--
Owner target for connecting Fresnel/Jones data to the bilingual operator
geometry.
-/
structure OperatorialJonesOwnerTarget
    (Op : Type*) [Ring Op] [Algebra ℂ Op] where
  /-- The Fresnel `s/p` projector pair owned by the Jones calculus layer. -/
  projectors : PolarizationProjectorPair Op

namespace OperatorialJonesOwnerTarget

variable {Op : Type*} [Ring Op] [Algebra ℂ Op]

/-- Read back the concrete projector pair carried by the owner target. -/
def toProjectorPair
    (T : OperatorialJonesOwnerTarget Op) :
    PolarizationProjectorPair Op :=
  T.projectors

@[simp] theorem toProjectorPair_mk
    (P : PolarizationProjectorPair Op) :
    toProjectorPair (OperatorialJonesOwnerTarget.mk P) = P :=
  rfl

end OperatorialJonesOwnerTarget

end InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus
