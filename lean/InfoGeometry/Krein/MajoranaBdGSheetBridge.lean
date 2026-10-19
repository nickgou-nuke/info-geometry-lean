/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford
import InfoGeometry.Canonical.KreinMajoranaBlockInvariance
import InfoGeometry.Canonical.RealifiedDoubledKreinHodgeBridge
import InfoGeometry.Krein.PolarizedSector
import InfoGeometry.Krein.MajoranaSheetConnectors

/-!
# The concrete Kitaev BdG boundary vectors on the doubled real Krein carrier

The first four and last four Nambu coordinates are identified with the two
coordinates of `DoubledSpace (Fin 4 → ℝ)`.  Theorems below transport the
existing sweet-spot matrix kernel vectors and identify the particle-hole
swap and diagonal signature with the doubled-space modular swap and
fundamental symmetry.  Spectral sheet projections are component readouts;
they are not asserted to remain in the BdG kernel.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Krein.MajoranaBdGSheetBridge

open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Krein.MajoranaSheetConnectors
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford
open InfoGeometry.Canonical.KreinMajoranaBlockInvariance

abbrev E4 := EuclideanSpace ℝ (Fin 4)
abbrev H4 := InfoGeometry.Krein.DoubledSpace E4

private def fin8ToSum : Fin 8 ≃ (Fin 4 ⊕ Fin 4) where
  toFun i :=
    if h : i.val < 4 then Sum.inl ⟨i.val, h⟩
    else Sum.inr ⟨i.val - 4, by omega⟩
  invFun
    | Sum.inl i => ⟨i.val, by omega⟩
    | Sum.inr i => ⟨i.val + 4, by omega⟩
  left_inv i := by
    by_cases h : i.val < 4
    · simp [h]
    · simp [h]
      apply Fin.ext
      simp
      omega
  right_inv s := by
    cases s with
    | inl i => simp
    | inr i => simp

private theorem fin8ToSum_symm_inl (i : Fin 4) :
    fin8ToSum.symm (Sum.inl i) = ⟨i.val, by omega⟩ := by
  apply Fin.ext
  rfl

private theorem fin8ToSum_symm_inr (i : Fin 4) :
    fin8ToSum.symm (Sum.inr i) = ⟨i.val + 4, by omega⟩ := by
  apply Fin.ext
  rfl

private def rawVec8PairEquiv :
    InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford.Vec8R ≃ₗ[ℝ]
      ((Fin 4 → ℝ) × (Fin 4 → ℝ)) where
  toFun v :=
    (fun i => v (fin8ToSum.symm (Sum.inl i)),
     fun i => v (fin8ToSum.symm (Sum.inr i)))
  invFun p := fun j => Sum.elim p.1 p.2 (fin8ToSum j)
  left_inv v := by
    funext j
    change Sum.elim (fun i => v (fin8ToSum.symm (Sum.inl i)))
      (fun i => v (fin8ToSum.symm (Sum.inr i))) (fin8ToSum j) = v j
    cases h : fin8ToSum j with
    | inl i =>
        simp only [Sum.elim_inl]
        congr 1
        apply fin8ToSum.injective
        simp [h]
    | inr i =>
        simp only [Sum.elim_inr]
        congr 1
        apply fin8ToSum.injective
        simp [h]
  right_inv p := by
    apply Prod.ext <;> funext i <;> simp
  map_add' v w := by
    apply Prod.ext <;> funext i <;> simp
  map_smul' c v := by
    apply Prod.ext <;> funext i <;> simp

private def vec8PairEquiv :
    InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford.Vec8R ≃ₗ[ℝ] (E4 × E4) :=
  rawVec8PairEquiv.trans
    ((WithLp.linearEquiv (2 : ENNReal) ℝ (Fin 4 → ℝ)).symm.prodCongr
      (WithLp.linearEquiv (2 : ENNReal) ℝ (Fin 4 → ℝ)).symm)

private theorem rawVec8PairEquiv_apply
    (v : InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford.Vec8R) :
    rawVec8PairEquiv v =
      (fun i : Fin 4 => v ⟨i.val, by omega⟩,
       fun i : Fin 4 => v ⟨i.val + 4, by omega⟩) := by
  apply Prod.ext
  · funext i
    change v (fin8ToSum.symm (Sum.inl i)) = _
    rw [fin8ToSum_symm_inl]
  · funext i
    change v (fin8ToSum.symm (Sum.inr i)) = _
    rw [fin8ToSum_symm_inr]

private theorem vec8PairEquiv_apply
    (v : InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford.Vec8R) :
    vec8PairEquiv v =
      (WithLp.toLp (2 : ENNReal) (fun i : Fin 4 => v ⟨i.val, by omega⟩),
       WithLp.toLp (2 : ENNReal) (fun i : Fin 4 => v ⟨i.val + 4, by omega⟩)) := by
  simp [vec8PairEquiv, rawVec8PairEquiv_apply, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply]

/-- Split the Nambu coordinates into the two real sheets. -/
noncomputable def nambuDoubledEquiv :
    InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford.Vec8R ≃ₗ[ℝ] H4 :=
  vec8PairEquiv.trans
    (WithLp.linearEquiv (2 : ENNReal) ℝ (E4 × E4)).symm

@[simp] theorem nambuDoubledEquiv_apply
    (v : InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford.Vec8R) :
    nambuDoubledEquiv v =
      InfoGeometry.Krein.to_doubled
        (WithLp.toLp (2 : ENNReal) (fun i : Fin 4 => v ⟨i.val, by omega⟩))
        (WithLp.toLp (2 : ENNReal) (fun i : Fin 4 => v ⟨i.val + 4, by omega⟩)) := by
  have hpair : vec8PairEquiv v =
      (WithLp.toLp (2 : ENNReal) (fun i : Fin 4 => v ⟨i.val, by omega⟩),
       WithLp.toLp (2 : ENNReal) (fun i : Fin 4 => v ⟨i.val + 4, by omega⟩)) :=
    vec8PairEquiv_apply v
  change WithLp.toLp (2 : ENNReal) (vec8PairEquiv v) = _
  rw [hpair]

private def basis0 : E4 := WithLp.toLp (2 : ENNReal) (fun i => if i.val = 0 then 1 else 0)
private def basis3 : E4 := WithLp.toLp (2 : ENNReal) (fun i => if i.val = 3 then 1 else 0)

private theorem particleHole8_low_apply
    (v : InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford.Vec8R) (i : Fin 4) :
    (particleHole8.mulVec v) ⟨i.val, by omega⟩ = v ⟨i.val + 4, by omega⟩ := by
  fin_cases i <;>
    simp [particleHole8, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

private theorem particleHole8_high_apply
    (v : InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford.Vec8R) (i : Fin 4) :
    (particleHole8.mulVec v) ⟨i.val + 4, by omega⟩ = v ⟨i.val, by omega⟩ := by
  fin_cases i <;>
    simp [particleHole8, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

private theorem kreinMetric8_low_apply
    (v : InfoGeometry.Canonical.KreinMajoranaBlockInvariance.Vec8R) (i : Fin 4) :
    (kreinMetric8.mulVec v) ⟨i.val, by omega⟩ = v ⟨i.val, by omega⟩ := by
  fin_cases i <;>
    simp [kreinMetric8, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

private theorem kreinMetric8_high_apply
    (v : InfoGeometry.Canonical.KreinMajoranaBlockInvariance.Vec8R) (i : Fin 4) :
    (kreinMetric8.mulVec v) ⟨i.val + 4, by omega⟩ = -v ⟨i.val + 4, by omega⟩ := by
  fin_cases i <;>
    simp [kreinMetric8, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

/-- The Nambu particle-hole involution becomes the modular swap of the two sheets. -/
theorem particleHole8_intertwines_modular_j
    (v : InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford.Vec8R) :
    nambuDoubledEquiv (particleHole8.mulVec v) =
      InfoGeometry.Krein.modular_j (E := E4) (nambuDoubledEquiv v) := by
  rw [nambuDoubledEquiv_apply, nambuDoubledEquiv_apply]
  apply InfoGeometry.Krein.DoubledSpace.ext <;>
    ext i <;>
    simp [InfoGeometry.Krein.modular_j, particleHole8_low_apply, particleHole8_high_apply]

/-- The diagonal ((4,4)) Krein grading becomes the doubled-space fundamental symmetry. -/
theorem kreinMetric8_intertwines_spectral_epsilon
    (v : InfoGeometry.Canonical.KreinMajoranaBlockInvariance.Vec8R) :
    nambuDoubledEquiv (kreinMetric8.mulVec v) =
      InfoGeometry.Krein.spectral_epsilon (E := E4) (nambuDoubledEquiv v) := by
  rw [nambuDoubledEquiv_apply, nambuDoubledEquiv_apply]
  apply InfoGeometry.Krein.DoubledSpace.ext <;>
    ext i <;>
    simp [InfoGeometry.Krein.spectral_epsilon,
      kreinMetric8_low_apply, kreinMetric8_high_apply]

@[simp] theorem leftMode_sheet_coordinates :
    nambuDoubledEquiv majoranaZeroModeLeft8 =
      InfoGeometry.Krein.to_doubled basis0 (-basis0) := by
  rw [nambuDoubledEquiv_apply]
  apply InfoGeometry.Krein.DoubledSpace.ext <;> ext i <;>
    fin_cases i <;> norm_num [majoranaZeroModeLeft8, basis0]

@[simp] theorem rightMode_sheet_coordinates :
    nambuDoubledEquiv majoranaZeroModeRight8 =
      InfoGeometry.Krein.to_doubled basis3 basis3 := by
  rw [nambuDoubledEquiv_apply]
  apply InfoGeometry.Krein.DoubledSpace.ext <;> ext i <;>
    fin_cases i <;> norm_num [majoranaZeroModeRight8, basis3]

/-- The transported left boundary mode is isotropic for the canonical
doubled Krein form. -/
theorem leftMode_krein_isotropic :
    InfoGeometry.Canonical.RealifiedDoubledKreinHodgeBridge.kreinForm
      (E := E4) (nambuDoubledEquiv majoranaZeroModeLeft8)
      (nambuDoubledEquiv majoranaZeroModeLeft8) = 0 := by
  rw [leftMode_sheet_coordinates,
    InfoGeometry.Canonical.RealifiedDoubledKreinHodgeBridge.kreinForm_apply]
  simp

/-- The transported right boundary mode is isotropic for the canonical
doubled Krein form. -/
theorem rightMode_krein_isotropic :
    InfoGeometry.Canonical.RealifiedDoubledKreinHodgeBridge.kreinForm
      (E := E4) (nambuDoubledEquiv majoranaZeroModeRight8)
      (nambuDoubledEquiv majoranaZeroModeRight8) = 0 := by
  rw [rightMode_sheet_coordinates,
    InfoGeometry.Canonical.RealifiedDoubledKreinHodgeBridge.kreinForm_apply]
  simp

private theorem leftMode_ne_zero :
    majoranaZeroModeLeft8 ≠ 0 := by
  intro h
  have h0 := congrArg
    (fun v : InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford.Vec8R => v 0) h
  norm_num [majoranaZeroModeLeft8] at h0

private theorem rightMode_ne_zero :
    majoranaZeroModeRight8 ≠ 0 := by
  intro h
  have h3 := congrArg
    (fun v : InfoGeometry.Canonical.MajoranaKitaevSpinor8DClifford.Vec8R => v 3) h
  norm_num [majoranaZeroModeRight8] at h3

/-- The transported left BdG mode is a nonzero doubled-space vector. -/
theorem transported_leftMode_ne_zero :
    nambuDoubledEquiv majoranaZeroModeLeft8 ≠ 0 := by
  intro h
  apply leftMode_ne_zero
  apply nambuDoubledEquiv.injective
  rw [nambuDoubledEquiv.map_zero]
  exact h

/-- The transported right BdG mode is a nonzero doubled-space vector. -/
theorem transported_rightMode_ne_zero :
    nambuDoubledEquiv majoranaZeroModeRight8 ≠ 0 := by
  intro h
  apply rightMode_ne_zero
  apply nambuDoubledEquiv.injective
  rw [nambuDoubledEquiv.map_zero]
  exact h

/-- The left boundary BdG kernel vector is odd under particle-hole sheet exchange. -/
theorem leftMode_modular_j_odd :
    InfoGeometry.Krein.modular_j (E := E4)
      (nambuDoubledEquiv majoranaZeroModeLeft8) =
        -(nambuDoubledEquiv majoranaZeroModeLeft8) := by
  rw [leftMode_sheet_coordinates]
  apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [InfoGeometry.Krein.modular_j]

/-- The right boundary BdG kernel vector is even under particle-hole sheet exchange. -/
theorem rightMode_modular_j_even :
    InfoGeometry.Krein.modular_j (E := E4)
      (nambuDoubledEquiv majoranaZeroModeRight8) =
        nambuDoubledEquiv majoranaZeroModeRight8 := by
  rw [rightMode_sheet_coordinates]
  apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [InfoGeometry.Krein.modular_j]

/-- Positive-sheet readout of the left boundary mode. -/
theorem leftMode_plus_projection :
    InfoGeometry.Krein.spectralPlusProj (E := E4)
      (nambuDoubledEquiv majoranaZeroModeLeft8) =
        plusPoint (E := E4) basis0 := by
  rw [leftMode_sheet_coordinates]
  exact spectralPlusProj_apply_to_doubled _ _

/-- Negative-sheet readout of the left boundary mode. -/
theorem leftMode_minus_projection :
    InfoGeometry.Krein.spectralMinusProj (E := E4)
      (nambuDoubledEquiv majoranaZeroModeLeft8) =
        minusPoint (E := E4) (-basis0) := by
  rw [leftMode_sheet_coordinates]
  exact spectralMinusProj_apply_to_doubled _ _

/-- Positive-sheet readout of the right boundary mode. -/
theorem rightMode_plus_projection :
    InfoGeometry.Krein.spectralPlusProj (E := E4)
      (nambuDoubledEquiv majoranaZeroModeRight8) =
        plusPoint (E := E4) basis3 := by
  rw [rightMode_sheet_coordinates]
  exact spectralPlusProj_apply_to_doubled _ _

/-- Negative-sheet readout of the right boundary mode. -/
theorem rightMode_minus_projection :
    InfoGeometry.Krein.spectralMinusProj (E := E4)
      (nambuDoubledEquiv majoranaZeroModeRight8) =
        minusPoint (E := E4) basis3 := by
  rw [rightMode_sheet_coordinates]
  exact spectralMinusProj_apply_to_doubled _ _

/-- The CAR Majorana connector carries the left mode's plus-sheet component
to the coordinate-matched minus sheet. -/
theorem leftMode_CAR_connector_crosses_sheets :
    (InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARCreation (E := E4) +
      InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARAnnihilation (E := E4))
        (InfoGeometry.Krein.spectralPlusProj (E := E4)
          (nambuDoubledEquiv majoranaZeroModeLeft8)) =
      minusPoint (E := E4) basis0 := by
  rw [leftMode_plus_projection]
  exact majorana_swap_maps_plusPoint_to_minusPoint basis0

/-- The CAR Majorana connector carries the right mode's plus-sheet component
to the coordinate-matched minus sheet. -/
theorem rightMode_CAR_connector_crosses_sheets :
    (InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARCreation (E := E4) +
      InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARAnnihilation (E := E4))
        (InfoGeometry.Krein.spectralPlusProj (E := E4)
          (nambuDoubledEquiv majoranaZeroModeRight8)) =
      minusPoint (E := E4) basis3 := by
  rw [rightMode_plus_projection]
  exact majorana_swap_maps_plusPoint_to_minusPoint basis3

/-- The sweet-spot BdG operator conjugated to the doubled carrier. -/
noncomputable def transportedSweetSpot (t : ℝ) : H4 → H4 := fun z =>
  nambuDoubledEquiv ((kitaevSweetSpot8 t).mulVec (nambuDoubledEquiv.symm z))

/-- The transported left BdG boundary vector remains in the transported kernel. -/
theorem transported_leftMode_is_zero (t : ℝ) :
    transportedSweetSpot t (nambuDoubledEquiv majoranaZeroModeLeft8) = 0 := by
  rw [transportedSweetSpot, nambuDoubledEquiv.symm_apply_apply,
    left_majorana_zero_mode_energy8, nambuDoubledEquiv.map_zero]

/-- The transported right BdG boundary vector remains in the transported kernel. -/
theorem transported_rightMode_is_zero (t : ℝ) :
    transportedSweetSpot t (nambuDoubledEquiv majoranaZeroModeRight8) = 0 := by
  rw [transportedSweetSpot, nambuDoubledEquiv.symm_apply_apply,
    right_majorana_zero_mode_energy8, nambuDoubledEquiv.map_zero]

end InfoGeometry.Krein.MajoranaBdGSheetBridge
