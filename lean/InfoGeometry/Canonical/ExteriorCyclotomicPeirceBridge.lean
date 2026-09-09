import Mathlib

/-!
# Canonical exterior/cyclotomic bridge

This owner records only the carrier-level facts that are available in the
current repository: exterior creation is nilpotent, while the degree clock
and the Hodge operator are separate structures.  Analytic or geometric
identifications are intentionally not asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ExteriorCyclotomicPeirceBridge

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem exterior_creation_square_zero (v : V) :
    (LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ v)) ^ 2 =
      (0 : Module.End ℂ (ExteriorAlgebra ℂ V)) := by
  apply LinearMap.ext
  intro x
  change ExteriorAlgebra.ι ℂ v * (ExteriorAlgebra.ι ℂ v * x) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

end InfoGeometry.Canonical.ExteriorCyclotomicPeirceBridge
