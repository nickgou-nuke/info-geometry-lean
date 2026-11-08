import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import InfoGeometry.Canonical.CStarAlgebraStateColimit
import InfoGeometry.Canonical.BostConnesKMS

/-!
# Bost--Connes generators in the native GNS representation

The Bost--Connes partition series and its zeta identification are owned by
`InfoGeometry.Arithmetic.BostConnesNativeZetaPartition`; the projection
readout and its explicit KMS closure boundary are owned by
`InfoGeometry.Canonical.BostConnesKMS`. Neither a scalar-valued function
definition nor an arbitrary cyclic module is a C*-algebraic KMS state or a
GNS construction. This file records the concrete transport that is justified:
an isometric indexed generator remains an isometry in Mathlib's GNS
representation of any supplied normalized positive state.
-/

noncomputable section

namespace InfoGeometry.Physics.BostConnesGNS

open InfoGeometry.Canonical.BostConnesKMS
open CStarStateColimit.Native

variable {Op : Type*}
variable [CStarAlgebra Op] [PartialOrder Op] [StarOrderedRing Op]

/-- The native GNS representation sends each Cuntz-indexed Bost--Connes
generator to an isometry. This uses the actual Mathlib GNS star-algebra
homomorphism, not an abstract cyclicity field. -/
theorem gns_generator_isometry
    (C : BostConnesCuntzSystem Op)
    (ω : State Op) (n : ℕ+) :
    star (ω.functional.gnsStarAlgHom (S C n)) *
        ω.functional.gnsStarAlgHom (S C n) = 1 := by
  have hgen : star (S C n) * S C n = 1 := by
    change star (C.generator n) * C.generator n = 1
    exact C.generator_isometry n
  simpa only [map_mul, map_star, map_one] using
    congrArg ω.functional.gnsStarAlgHom hgen

end InfoGeometry.Physics.BostConnesGNS
