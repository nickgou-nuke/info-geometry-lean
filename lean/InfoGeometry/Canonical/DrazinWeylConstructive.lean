import InfoGeometry.Quantum.TriadicWeylBridge

/-!
# Constructive Drazin/Weyl Compatibility Owner

Constructive owner interface for routing Drazin-side inverse candidates into the
Weyl-compatibility surface used by `TriadicWeylBridge`.
-/

namespace InfoGeometry.Canonical.DrazinWeylConstructive

open InfoGeometry.Krein
open InfoGeometry.Quantum.TriadicWeylBridge

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Constructive compatibility datum: a candidate inverse together with the proved
commutation relation against the spectral sheet involution.
-/
structure ConstructiveDrazinWeylData where
  drazinInverse : EndH
  commutes_spectralEpsilon :
    drazinInverse.comp (spectral_epsilon (E := E))
      = (spectral_epsilon (E := E)).comp drazinInverse

/-- Shim theorem exporting constructive commutation into legacy Weyl compatibility. -/
theorem drazinInverse_isWeylCompatible
    (D : ConstructiveDrazinWeylData (E := E)) :
    IsWeylCompatible (E := E) D.drazinInverse := by
  exact (isWeylCompatible_iff_comp_spectralEpsilon (E := E) D.drazinInverse).2
    D.commutes_spectralEpsilon

end InfoGeometry.Canonical.DrazinWeylConstructive
