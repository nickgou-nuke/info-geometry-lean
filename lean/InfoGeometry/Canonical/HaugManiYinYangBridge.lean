/-
InfoGeometry/Canonical/HaugManiYinYangBridge.lean

The former bridge encoded a complex-like multiplication table and sector
conjugation by explicit `2 × 2` real matrices.  It was a finite coordinate
shadow, not a noncommutative Hestenes/Krein theorem, and it has no maintained
Lean consumers.

The canonical noncommutative route is:

`RealDoubledChiralKreinModularBridge`
  → `ModularSignCPT`
  → `RealMajoranaCategory` / `RealSplitClifford`
  → `TomitaTakesakiModularFlow`.

This file is an import-routing marker only.  It exports no scalar matrix
replacement API and does not claim a Tomita, KMS, or Riemann theorem.
-/

import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinModularBridge
import InfoGeometry.OperatorAlgebra.ModularSignCPT
import InfoGeometry.Quantum.RealMajoranaCategory
import InfoGeometry.Quantum.RealSplitClifford
import InfoGeometry.Canonical.TomitaTakesakiModularFlow

namespace InfoGeometry.Canonical.HaugManiYinYangBridge

/- The former finite matrix bridge is retired; use the native owners above. -/

end InfoGeometry.Canonical.HaugManiYinYangBridge
