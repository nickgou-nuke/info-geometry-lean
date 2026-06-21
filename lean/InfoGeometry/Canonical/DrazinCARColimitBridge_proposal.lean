import InfoGeometry.Canonical.GNSCARColimit
import InfoGeometry.Canonical.DrazinTopologicalRealization

noncomputable section

namespace InfoGeometry.Canonical.DrazinCARColimitBridge

open InfoGeometry.Canonical.GNSCARColimit
open InfoGeometry.Canonical.DrazinTopologicalRealization
open InfoGeometry.Canonical.CPTDirectLimitGNS

-- We need a completed Hilbert space over the GNS quotient
-- This will be the topological carrier E for the Drazin supercharge.
abbrev LimitHilbertSpace (P : CPTDirectLimitGNSPacket) : Type := sorry

-- We need the Krein doubled space structure H₂
abbrev LimitDoubledSpace (P : CPTDirectLimitGNSPacket) : Type := sorry

-- The certified inverse kernel living on the infinite limit
def limitCertifiedInverseKernel (P : CPTDirectLimitGNSPacket) : 
    InfoGeometry.Canonical.CertifiedInverseKernel (LimitDoubledSpace P) := sorry

-- The Drazin Fredholm proof bundle for the limit
def limitFredholmBundle (P : CPTDirectLimitGNSPacket) 
    (cl11 : InfoGeometry.Quantum.RealSplitCl11Action (LimitDoubledSpace P)) : 
    DrazinFredholmProofBundle (limitCertifiedInverseKernel P) cl11 := sorry

-- The Macroscopic Drazin Central Charge!
def macroscopicDrazinCentralCharge (P : CPTDirectLimitGNSPacket) 
    (cl11 : InfoGeometry.Quantum.RealSplitCl11Action (LimitDoubledSpace P))
    (hSfc : InfoGeometry.KK.RealSplitKreinKasparovCycle.ChiralFredholmSurface 
              (drazinFredholmModule (limitCertifiedInverseKernel P) cl11 (limitFredholmBundle P cl11))) : ℤ :=
  drazinTopologicalCentralCharge (limitCertifiedInverseKernel P) cl11 (limitFredholmBundle P cl11) hSfc

end InfoGeometry.Canonical.DrazinCARColimitBridge
