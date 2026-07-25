import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeExteriorRepresentation
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.Canonical.PrimeExteriorRepresentationCalibration

Canonical wrapper for the finite square-free exterior representation.

This file adds no analytic content. It only re-exports the exterior-state
readbacks under a canonical owner-facing namespace.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeExteriorRepresentationCalibration

open InfoGeometry.Arithmetic.PrimeExteriorRepresentation
open InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState

/-- Canonical re-export of the local occupation/membership readback. -/
theorem canonicalLocalOccupation_eq_one_iff_mem
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    localOccupation p S = 1 ↔ p ∈ S :=
  localOccupation_eq_one_iff_mem p S

/-- Canonical re-export of the local occupation/absence readback. -/
theorem canonicalLocalOccupation_eq_zero_iff_not_mem
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    localOccupation p S = 0 ↔ p ∉ S :=
  localOccupation_eq_zero_iff_not_mem p S

/-- Canonical re-export of the local parity/membership readback. -/
theorem canonicalLocalParitySign_eq_neg_one_iff_mem
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    localParitySign p S = -1 ↔ p ∈ S :=
  localParitySign_eq_neg_one_iff_mem p S

/-- Canonical re-export of the local parity/absence readback. -/
theorem canonicalLocalParitySign_eq_one_iff_not_mem
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel) :
    localParitySign p S = 1 ↔ p ∉ S :=
  localParitySign_eq_one_iff_not_mem p S

/-- Canonical re-export of the global chirality product readback. -/
theorem canonicalGamma_eq_prod_localParity
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    (S : SquareFreePrimeState PrimeLabel) :
    Gamma S = ∏ p ∈ S, localParitySign p S :=
  gamma_eq_prod_localParity S

/-- Canonical re-export of the square-free chirality parity readback. -/
theorem canonicalGamma_eq_negOne_pow_fermionNumber
    {PrimeLabel : Type*} [DecidableEq PrimeLabel]
    (S : SquareFreePrimeState PrimeLabel) :
    Gamma S = (-1 : ℤ) ^ fermionNumber S :=
  Gamma_eq_negOne_pow_fermionNumber S

/-- The canonical owner target is proved. -/
theorem primeExteriorRepresentationOwnerTarget :
    ∀ {PrimeLabel : Type*} [DecidableEq PrimeLabel]
      (p : PrimeLabel) (S : SquareFreePrimeState PrimeLabel),
      (localOccupation p S = 1 ↔ p ∈ S) ∧
      (localOccupation p S = 0 ↔ p ∉ S) ∧
      (localParitySign p S = -1 ↔ p ∈ S) ∧
      (localParitySign p S = 1 ↔ p ∉ S) ∧
      Gamma S = (-1 : ℤ) ^ fermionNumber S := by
  intro PrimeLabel _ p S
  exact ⟨canonicalLocalOccupation_eq_one_iff_mem p S,
    canonicalLocalOccupation_eq_zero_iff_not_mem p S,
    canonicalLocalParitySign_eq_neg_one_iff_mem p S,
    canonicalLocalParitySign_eq_one_iff_not_mem p S,
    canonicalGamma_eq_negOne_pow_fermionNumber S⟩

end InfoGeometry.Canonical.PrimeExteriorRepresentationCalibration
