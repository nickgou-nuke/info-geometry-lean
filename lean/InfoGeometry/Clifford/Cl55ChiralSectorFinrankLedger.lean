import InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55SpinorDimensionReadout

/-!
# Finite-dimensional ledger for the chiral spinor sectors

This file records only the consequence of the existing projector decomposition:
the two chiral submodules have complementary dimensions summing to 32.  It
does not identify either sector with an octonionic carrier.
-/

namespace InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge

open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.SpinorRep

theorem chiralSectors_finrank_add_reexport :
    Module.finrank ℝ chiralPlusSector +
        Module.finrank ℝ chiralMinusSector = 32 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    chiralPlusSector chiralMinusSector
  rw [chiralSectors_sup_top, chiralSectors_disjoint] at h
  simpa [finrank_top, finrank_bot, spinorSpace_five_finrank] using h.symm

theorem chiralSectors_finrank_eq_of_exchange
    (e : chiralPlusSector ≃ₗ[ℝ] chiralMinusSector) :
    Module.finrank ℝ chiralPlusSector =
      Module.finrank ℝ chiralMinusSector := by
  exact e.finrank_eq

theorem chiralSectors_finrank_eq_sixteen_of_exchange
    (e : chiralPlusSector ≃ₗ[ℝ] chiralMinusSector) :
    Module.finrank ℝ chiralPlusSector = 16 ∧
      Module.finrank ℝ chiralMinusSector = 16 := by
  have heq := chiralSectors_finrank_eq_of_exchange e
  have hsum := chiralSectors_finrank_add_reexport
  omega

end InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
