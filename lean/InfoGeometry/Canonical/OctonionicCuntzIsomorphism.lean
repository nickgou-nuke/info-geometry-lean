import InfoGeometry.Canonical.ChiralConeOctonionicBridge

/-!
# Projector-level split-octonion/Cuntz comparison

The light-cone construction supplies two complementary self-adjoint
idempotents.  This is the projector shadow of a two-sector Cuntz resolution;
it is not an isomorphism with `𝒪₂`, since no isometry generators are
constructed here.
-/

namespace InfoGeometry.Canonical

variable {R : Type*} [Field R] [CharZero R]

abbrev LightconeCuntzProjectorData (R : Type*) [Field R] [CharZero R] :=
  {u : R // u * u = 1}

namespace LightconeCuntzProjectorData

abbrev u (D : LightconeCuntzProjectorData R) : R := D.1
abbrev square_eq_one (D : LightconeCuntzProjectorData R) : D.u * D.u = 1 := D.2

def projectorPlus (D : LightconeCuntzProjectorData R) : R := lightconePlus D.u
def projectorMinus (D : LightconeCuntzProjectorData R) : R := lightconeMinus D.u

theorem projector_plus_idempotent (D : LightconeCuntzProjectorData R) :
    projectorPlus D * projectorPlus D = projectorPlus D :=
  lightconePlus_idempotent D.u D.square_eq_one

theorem projector_minus_idempotent (D : LightconeCuntzProjectorData R) :
    projectorMinus D * projectorMinus D = projectorMinus D :=
  lightconeMinus_idempotent D.u D.square_eq_one

theorem projector_orthogonal (D : LightconeCuntzProjectorData R) :
    projectorPlus D * projectorMinus D = 0 :=
  lightcone_orthogonality D.u D.square_eq_one

theorem projector_resolution (D : LightconeCuntzProjectorData R) :
    projectorPlus D + projectorMinus D = 1 :=
  lightcone_resolution D.u

theorem projector_cuntz_like_relations (D : LightconeCuntzProjectorData R) :
    (projectorPlus D * projectorPlus D = projectorPlus D) ∧
    (projectorMinus D * projectorMinus D = projectorMinus D) ∧
    (projectorPlus D * projectorMinus D = 0) ∧
    (projectorPlus D + projectorMinus D = 1) := by
  exact ⟨projector_plus_idempotent D, projector_minus_idempotent D,
    projector_orthogonal D, projector_resolution D⟩

end LightconeCuntzProjectorData
end InfoGeometry.Canonical
