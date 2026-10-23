/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.BipolarTwoDimensionalSkewObstruction

/-! Classification of skew cotangent maps on the existing two-coordinate carrier. -/

noncomputable section

namespace InfoGeometry.Thermo.BipolarTwoDimensionalSkewObstruction

open InfoGeometry.Thermo.GenericMetriplecticFlow

def skewCoordinateMap (c : ℝ) : Covector State2 →ₗ[ℝ] State2 where
  toFun α := ![c * α thetaBasis2, -c * α etaBasis2]
  map_add' α β := by ext i; fin_cases i <;> simp [mul_add]
  map_smul' r α := by ext i; fin_cases i <;> simp <;> ring

theorem skewCoordinateMap_coefficient (c : ℝ) :
    etaCovector2 (skewCoordinateMap c thetaCovector2) = c := by
  simp [skewCoordinateMap, etaCovector2]

theorem skewCoordinateMap_skew (c : ℝ) (α β : Covector State2) :
    α (skewCoordinateMap c β) = -β (skewCoordinateMap c α) := by
  rw [state2_coordinate_decomposition (skewCoordinateMap c β),
    state2_coordinate_decomposition (skewCoordinateMap c α)]
  simp [skewCoordinateMap]
  ring

theorem skew_operator_eq_coordinateMap (L : Covector State2 →ₗ[ℝ] State2)
    (h : ∀ α β : Covector State2, α (L β) = -β (L α)) :
    L = skewCoordinateMap (etaCovector2 (L thetaCovector2)) := by
  have hη : etaCovector2 (L etaCovector2) = 0 :=
    CharZero.eq_neg_self_iff.mp (h etaCovector2 etaCovector2)
  have hθ : thetaCovector2 (L thetaCovector2) = 0 :=
    CharZero.eq_neg_self_iff.mp (h thetaCovector2 thetaCovector2)
  have hcross := h thetaCovector2 etaCovector2
  change L etaCovector2 0 = 0 at hη
  change L thetaCovector2 1 = 0 at hθ
  change L etaCovector2 1 = -L thetaCovector2 0 at hcross
  change L = skewCoordinateMap (L thetaCovector2 0)
  apply LinearMap.ext
  intro α
  rw [covector2_coordinate_decomposition α]
  ext i
  fin_cases i <;>
    simp [skewCoordinateMap, hη, hθ, hcross] <;> ring

theorem skew_operator_classification (L : Covector State2 →ₗ[ℝ] State2) :
    (∀ α β : Covector State2, α (L β) = -β (L α)) ↔
      ∃! c : ℝ, L = skewCoordinateMap c := by
  constructor
  · intro h
    refine ⟨etaCovector2 (L thetaCovector2), skew_operator_eq_coordinateMap L h, ?_⟩
    intro c hc
    rw [hc, skewCoordinateMap_coefficient]
  · rintro ⟨c, rfl, _⟩
    exact skewCoordinateMap_skew c

theorem skewCoordinateMap_apply_eq_zero_iff (c : ℝ) (α : Covector State2) :
    skewCoordinateMap c α = 0 ↔ c = 0 ∨ α = 0 := by
  constructor
  · intro h
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have hθ := congrFun h 0
      have hη := congrFun h 1
      simp only [skewCoordinateMap, LinearMap.coe_mk, AddHom.coe_mk,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Pi.zero_apply] at hθ hη
      have hθ0 : α thetaBasis2 = 0 := (mul_eq_zero.mp hθ).resolve_left hc
      have hη0 : α etaBasis2 = 0 := (mul_eq_zero.mp hη).resolve_left (neg_ne_zero.mpr hc)
      rw [covector2_coordinate_decomposition α, hθ0, hη0]
      simp
  · rintro (rfl | rfl) <;> ext i <;> fin_cases i <;> simp [skewCoordinateMap]

end InfoGeometry.Thermo.BipolarTwoDimensionalSkewObstruction
