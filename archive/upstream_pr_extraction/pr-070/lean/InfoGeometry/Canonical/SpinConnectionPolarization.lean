import InfoGeometry.Canonical.SpinConnection
import InfoGeometry.Optics.SheetWittCircularBasis

/-!
# Spin transport of sheet/circular projectors

The existing spin connection acts on bounded endomorphisms by conjugation.
This module identifies its exact polarization consequence: if transport fixes
the two commuting involutions, it fixes every joint spectral projector derived
from them.
-/

noncomputable section

namespace InfoGeometry.Canonical.SpinConnectionPolarization

open InfoGeometry.Krein
open InfoGeometry.Krein.NeutralSpace
open InfoGeometry.Optics.SheetWittCircularBasis

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev EndN := NeutralSpace E →L[ℝ] NeutralSpace E

/--
A spin transport fixing the hyperbolic and circular involutions fixes each of
their four joint spectral modes.
-/
theorem transportEnd_jointProjector_of_axes
    (S : SpinConnection E) (t : ℝ)
    (P : CommutingInvolutions (EndN (E := E)))
    (hH : transportEnd S t P.hyperbolic = P.hyperbolic)
    (hC : transportEnd S t P.circular = P.circular)
    (hSign cSign : Bool) :
    transportEnd S t (P.jointProjector hSign cSign) =
      P.jointProjector hSign cSign := by
  have hHyper (sign : Bool) :
      transportEnd S t
          (choose sign
            (CommutingInvolutions.hyperbolicInvolution P).Pleft
            (CommutingInvolutions.hyperbolicInvolution P).Pright) =
        choose sign
          (CommutingInvolutions.hyperbolicInvolution P).Pleft
          (CommutingInvolutions.hyperbolicInvolution P).Pright := by
    cases sign <;>
      simp [choose, CommutingInvolutions.hyperbolicInvolution,
        InfoGeometry.OperatorAlgebra.ChiralInvolution.Pleft,
        InfoGeometry.OperatorAlgebra.ChiralInvolution.Pright, hH]
  have hCircular (sign : Bool) :
      transportEnd S t
          (choose sign
            (CommutingInvolutions.circularInvolution P).Pleft
            (CommutingInvolutions.circularInvolution P).Pright) =
        choose sign
          (CommutingInvolutions.circularInvolution P).Pleft
          (CommutingInvolutions.circularInvolution P).Pright := by
    cases sign <;>
      simp [choose, CommutingInvolutions.circularInvolution,
        InfoGeometry.OperatorAlgebra.ChiralInvolution.Pleft,
        InfoGeometry.OperatorAlgebra.ChiralInvolution.Pright, hC]
  unfold CommutingInvolutions.jointProjector
  rw [transportEnd_mul, hHyper, hCircular]

end InfoGeometry.Canonical.SpinConnectionPolarization
