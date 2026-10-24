/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.BostConnesThermalTime

namespace InfoGeometry.Physics.BostConnesThermalTime

open InfoGeometry.Clifford.Cl11CoordinateAlgebra

/-- The existing circular flow preserves the Clifford product precisely at
the times where its transverse sine vanishes. -/
theorem modularFlowCl11_multiplicative_iff (t : ℝ) :
    (∀ q r : Cl11, modularFlowCl11 t (q * r) =
      modularFlowCl11 t q * modularFlowCl11 t r) ↔ Real.sin (2 * t) = 0 := by
  constructor
  · intro hm
    have he := congrArg Cl11.e2 (hm e1Basis e2Basis)
    change (modularFlowCl11 t (mul e1Basis e2Basis)).e2 =
      (mul (modularFlowCl11 t e1Basis) (modularFlowCl11 t e2Basis)).e2 at he
    simp [modularFlowCl11, mul, e1Basis, e2Basis] at he
    linarith
  · intro hs q r
    change modularFlowCl11 t (mul q r) =
      mul (modularFlowCl11 t q) (modularFlowCl11 t r)
    rcases Real.sin_eq_zero_iff_cos_eq.mp hs with hc | hc <;>
      ext <;> simp [modularFlowCl11, mul, hs, hc] <;> ring

/-- Integer half-periods are exactly the multiplicative time slices. -/
theorem modularFlowCl11_multiplicative_iff_half_period (t : ℝ) :
    (∀ q r : Cl11, modularFlowCl11 t (q * r) =
      modularFlowCl11 t q * modularFlowCl11 t r) ↔
        ∃ k : ℤ, t = (k : ℝ) * Real.pi / 2 := by
  rw [modularFlowCl11_multiplicative_iff, Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith⟩

/-- The nontrivial multiplicative half-period is inner conjugation by `e₁`. -/
theorem modularFlowCl11_half_period_eq_conjugation (q : Cl11) :
    modularFlowCl11 (Real.pi / 2) q = e1Basis * q * e1Basis := by
  change modularFlowCl11 (Real.pi / 2) q = mul (mul e1Basis q) e1Basis
  ext <;> simp [modularFlowCl11, mul, e1Basis,
    show 2 * (Real.pi / 2) = Real.pi by ring]

/-- Every admissible time acts by one of these two explicit automorphisms. -/
theorem modularFlowCl11_eq_id_or_conjugation {t : ℝ} (ht : Real.sin (2 * t) = 0) :
    modularFlowCl11 t = id ∨
      modularFlowCl11 t = (fun q : Cl11 => e1Basis * q * e1Basis) := by
  rcases Real.sin_eq_zero_iff_cos_eq.mp ht with hc | hc
  · left
    funext q
    ext <;> simp [modularFlowCl11, ht, hc]
  · right
    funext q
    change modularFlowCl11 t q = mul (mul e1Basis q) e1Basis
    ext <;> simp [modularFlowCl11, mul, e1Basis, ht, hc]

/-- Promotion of the existing additive equivalence at the exact admissible times. -/
noncomputable def modularFlowCl11RingEquiv (t : ℝ) (ht : Real.sin (2 * t) = 0) :
    Cl11 ≃+* Cl11 :=
  { modularFlowCl11AddEquiv t with
    map_mul' := (modularFlowCl11_multiplicative_iff t).mpr ht }

@[simp] theorem modularFlowCl11RingEquiv_apply (t : ℝ)
    (ht : Real.sin (2 * t) = 0) (q : Cl11) :
    modularFlowCl11RingEquiv t ht q = modularFlowCl11 t q := rfl

end InfoGeometry.Physics.BostConnesThermalTime
