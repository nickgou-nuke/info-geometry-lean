import InfoGeometry.Arithmetic.MoebiusWeylEuler
import InfoGeometry.Arithmetic.PrimonGasPartition
import InfoGeometry.Arithmetic.PrimeSuperalgebra
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Arithmetic.UResRepresentations
import InfoGeometry.Arithmetic.Capstone
import InfoGeometry.Canonical.WeylCharacterEquivalence
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Canonical.LogDetRadonNikodymMechanism
import DAG.AffineProjectiveClosure
import DAG.HarmonicKMS

/-!
# Conditional Euler-product readout

This owner exposes one identity supplied by the prime-superalgebra owner.
The imported Fredholm, KMS, Möbius, and finite-product modules are not
combined into a new theorem here.
-/

open Complex

namespace InfoGeometry.Arithmetic.UnifiedCapstone

/--
**Conditional Euler-product identity.**

For `Re β > 1`, the supplied infinite bosonic Euler-product readout equals
Mathlib's `riemannZeta`.
-/
theorem master_euler_product_eq_riemannZeta
    {β : ℂ} (hRe : 1 < β.re) :
    InfoGeometry.Arithmetic.PrimeSuperalgebra.infiniteComplexBosonicEulerProduct β =
      riemannZeta β := by
  exact InfoGeometry.Arithmetic.PrimeSuperalgebra.infiniteComplexBosonicEulerProduct_eq_riemannZeta hRe

end InfoGeometry.Arithmetic.UnifiedCapstone
