import InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55ChiralSectorFlipContract

noncomputable section

namespace InfoGeometry.Clifford.Cl55ChiralCoordinateBridge

open InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
open InfoGeometry.Clifford.SpinorRep

variable
  (hPlus : Module.finrank ℝ chiralPlusSector = 16)
  (hMinus : Module.finrank ℝ chiralMinusSector = 16)

noncomputable def chiralPlusCoordinateEquiv
    (hPlus : Module.finrank ℝ chiralPlusSector = 16) :
    chiralPlusSector ≃ₗ[ℝ] (Fin 16 → ℝ) := by
  let _ := hPlus
  exact LinearEquiv.ofFinrankEq _ _ (by
    rw [hPlus]
    simp [Module.finrank_fintype_fun_eq_card])

noncomputable def chiralMinusCoordinateEquiv
    (hMinus : Module.finrank ℝ chiralMinusSector = 16) :
    chiralMinusSector ≃ₗ[ℝ] (Fin 16 → ℝ) := by
  let _ := hMinus
  exact LinearEquiv.ofFinrankEq _ _ (by
    rw [hMinus]
    simp [Module.finrank_fintype_fun_eq_card])

theorem chiralPlusCoordinateEquiv_finrank
    (hPlus : Module.finrank ℝ chiralPlusSector = 16) :
    Module.finrank ℝ chiralPlusSector =
      Module.finrank ℝ (Fin 16 → ℝ) := by
  exact (chiralPlusCoordinateEquiv hPlus).finrank_eq

theorem chiralMinusCoordinateEquiv_finrank
    (hMinus : Module.finrank ℝ chiralMinusSector = 16) :
    Module.finrank ℝ chiralMinusSector =
      Module.finrank ℝ (Fin 16 → ℝ) := by
  exact (chiralMinusCoordinateEquiv hMinus).finrank_eq

noncomputable def chiralCoordinateEquiv
    (hPlus : Module.finrank ℝ chiralPlusSector = 16)
    (hMinus : Module.finrank ℝ chiralMinusSector = 16) :
    SpinorSpace 5 ≃ₗ[ℝ] (Fin 16 → ℝ) × (Fin 16 → ℝ) :=
  (chiralPlusSector.prodEquivOfIsCompl chiralMinusSector
      chiralSectors_isCompl).symm.trans
    (LinearEquiv.prodCongr (chiralPlusCoordinateEquiv hPlus)
      (chiralMinusCoordinateEquiv hMinus))

noncomputable def chiralCoordinateEquiv_of_bijective_flip
    (flip : chiralPlusSector →ₗ[ℝ] chiralMinusSector)
    (hflip : Function.Bijective flip) :
    SpinorSpace 5 ≃ₗ[ℝ] (Fin 16 → ℝ) × (Fin 16 → ℝ) := by
  have hdim := chiralSector_finrank_each_eq_16_of_bijective flip hflip
  exact chiralCoordinateEquiv hdim.1 hdim.2

theorem chiralCoordinateEquiv_of_bijective_flip_finrank
    (flip : chiralPlusSector →ₗ[ℝ] chiralMinusSector)
    (hflip : Function.Bijective flip) :
    Module.finrank ℝ (SpinorSpace 5) =
      Module.finrank ℝ ((Fin 16 → ℝ) × (Fin 16 → ℝ)) := by
  exact (chiralCoordinateEquiv_of_bijective_flip flip hflip).finrank_eq

end InfoGeometry.Clifford.Cl55ChiralCoordinateBridge
