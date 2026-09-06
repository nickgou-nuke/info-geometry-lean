import InfoGeometry.Clifford.Cl55ChiralSectorFinrankLedger

/-!
# Contract for the missing chiral-sector flip

This is the exact algebraic interface needed to turn the complementary
32-dimensional decomposition into two 16-dimensional sectors.  No concrete
Clifford or octonionic action is assumed here.
-/

namespace InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge

variable (flip : chiralPlusSector →ₗ[ℝ] chiralMinusSector)

theorem chiralSector_finrank_eq_of_bijective
    (hflip : Function.Bijective flip) :
    Module.finrank ℝ chiralPlusSector =
      Module.finrank ℝ chiralMinusSector := by
  exact (LinearEquiv.ofBijective flip hflip).finrank_eq

theorem chiralSector_finrank_each_eq_16_of_bijective
    (hflip : Function.Bijective flip) :
    Module.finrank ℝ chiralPlusSector = 16 ∧
      Module.finrank ℝ chiralMinusSector = 16 := by
  have heq := chiralSector_finrank_eq_of_bijective flip hflip
  have hsum := chiralSectors_finrank_add_reexport
  omega

end InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
