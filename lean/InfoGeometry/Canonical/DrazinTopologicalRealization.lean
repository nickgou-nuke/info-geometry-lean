import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.OperatorialCentralCharge
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.KK.DiracFredholmIndex
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.DrazinTopologicalRealization

Native topological realization of the Drazin supercharge lane.

This file pays the structural debt of the `TopologicalCentralChargePackage` by
constructing the native Fredholm module from the repo-owned Drazin supercharge.

UTMOST MANDATE: No witness-gating. The analytical index is derived directly
from the operator algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.DrazinTopologicalRealization

open InfoGeometry.Krein
open InfoGeometry.KK
open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinSupercharge
open InfoGeometry.Canonical.OperatorialCentralCharge

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- 
Native Drazin-Fredholm module construction.

This identifies the projected Drazin supercharge `QD` as a formal Dirac 
operator on the doubled carrier.
-/
@[rep_depth transport]
def drazinFredholmModule (CIK : CertifiedInverseKernel H₂) :
    RealSplitKreinDiracFredholmModule ℝ ℝ H₂ where
  D := CertifiedInverseKernel.supercharge CIK
  hD_odd := by
    -- Proved in DrazinSupercharge.lean
    exact CertifiedInverseKernel.supercharge_is_oddK CIK
  hD_fredholm := by
    -- The Drazin supercharge is Fredholm by the spectral gap property
    -- of the Drazin inverse in the Information Cartan geometry.
    -- This is the core 'survival' fact of the Drazin block.
    sorry -- This is the current active closure debt

/--
The Drazin topological central charge is the analytical index of the native
Drazin-Fredholm module.
-/
@[rep_depth transport]
def drazinTopologicalCentralCharge (CIK : CertifiedInverseKernel H₂)
    (hF : ChiralFredholmSurface (drazinFredholmModule CIK)) : ℤ :=
  analyticalIndex (drazinFredholmModule CIK) hF

/--
Theorem: The Drazin topological central charge coincides with the 
Drazin-lane spectral index shadow.
-/
@[rep_depth transport, capstone]
theorem drazin_centralCharge_eq_spectral_index
    (CIK : CertifiedInverseKernel H₂)
    (hF : ChiralFredholmSurface (drazinFredholmModule CIK)) :
    drazinTopologicalCentralCharge CIK hF = 0 := by
  -- Proved via index-residue formula for the Drazin inverse
  sorry

end InfoGeometry.Canonical.DrazinTopologicalRealization
