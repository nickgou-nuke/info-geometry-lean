import InfoGeometry.Canonical.CommutantMoebiusFenchelMirrorBridge

/-!
# Commutant--Möbius--Legendre Capstone

This capstone is an explicit alias layer over the finite owner theorem surface
in `InfoGeometry.Canonical.CommutantMoebiusFenchelMirrorBridge`.

It intentionally does not claim the global infinite CAR commutant, a global
`SL(2,ℝ)` completion of the Cuntz map, or equality of those global structures.
Those remain proof debt until supplied by native Lean owner theorems.
-/

namespace CommutantMoebiusLegendre

export InfoGeometry.Canonical.CommutantMoebiusFenchelMirrorBridge
  (finite_commutant_moebius_fenchel_mirror_o55_window
   supplied_o55_and_dirac_hodge_trace_window)

end CommutantMoebiusLegendre
