import InfoGeometry.Canonical.SpinConnection
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
  let F := conjEnd (S.U t : NeutralSpace E ≃L[ℝ] NeutralSpace E)
  change F P.hyperbolic = P.hyperbolic at hH
  change F P.circular = P.circular at hC
  change F (P.jointProjector hSign cSign) = P.jointProjector hSign cSign
  cases hSign <;> cases cSign <;>
    simp only [CommutingInvolutions.jointProjector, choose,
      CommutingInvolutions.hyperbolicInvolution,
      CommutingInvolutions.circularInvolution,
      InfoGeometry.OperatorAlgebra.ChiralInvolution.Pleft,
      InfoGeometry.OperatorAlgebra.ChiralInvolution.Pright,
      Bool.false_eq_true, if_false, if_true,
      map_mul, map_smul, map_add, map_sub, map_one, hH, hC]

/-- Fixing both axes makes vector transport preserve each joint-projector range. -/
theorem transport_mem_jointProjector_range
    (S : SpinConnection E) (t : ℝ)
    (P : CommutingInvolutions (EndN (E := E)))
    (hH : transportEnd S t P.hyperbolic = P.hyperbolic)
    (hC : transportEnd S t P.circular = P.circular)
    (hSign cSign : Bool) (v : NeutralSpace E)
    (hv : v ∈ LinearMap.range (P.jointProjector hSign cSign).toLinearMap) :
    (S.U t : NeutralSpace E ≃L[ℝ] NeutralSpace E) v ∈
      LinearMap.range (P.jointProjector hSign cSign).toLinearMap := by
  rcases hv with ⟨w, rfl⟩
  let U : NeutralSpace E ≃L[ℝ] NeutralSpace E := S.U t
  refine ⟨U w, ?_⟩
  have h := congrArg (fun A : EndN (E := E) => A (U w))
    (transportEnd_jointProjector_of_axes S t P hH hC hSign cSign)
  change U (P.jointProjector hSign cSign (U.symm (U w))) =
    P.jointProjector hSign cSign (U w) at h
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h.symm

end InfoGeometry.Canonical.SpinConnectionPolarization
