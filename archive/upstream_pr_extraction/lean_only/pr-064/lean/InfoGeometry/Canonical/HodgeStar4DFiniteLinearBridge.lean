import InfoGeometry.Canonical.HodgeStar4DFinite
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Linear bridge for the finite Lorentzian Hodge star

The finite two-form owner gives the coordinate Hodge star as a function.  This
file exposes the same operator as a native `LinearMap`, retaining its
Lorentzian square law `⋆² = -id`.  It is a readout bridge only; it does not
claim a smooth manifold, a metric-derived exterior Hodge operator, or a de
Rham theorem.
-/

namespace InfoGeometry.Canonical.HodgeStar4DFiniteLinearBridge

open InfoGeometry.Canonical.HodgeStar4DFinite

noncomputable def hodgeStarLinear : TwoFormC →ₗ[ℂ] TwoFormC where
  toFun := hodgeStar
  map_add' F G := by
    funext i
    fin_cases i <;> simp [hodgeStar] <;> ring
  map_smul' c F := by
    funext i
    fin_cases i <;> simp [hodgeStar]

@[simp] theorem hodgeStarLinear_apply (F : TwoFormC) :
    hodgeStarLinear F = hodgeStar F := rfl

noncomputable def selfDualPartLinear : TwoFormC →ₗ[ℂ] TwoFormC where
  toFun := selfDualPart
  map_add' F G := by
    funext i
    fin_cases i <;> simp [selfDualPart, hodgeStar] <;> ring
  map_smul' c F := by
    funext i
    fin_cases i <;> simp [selfDualPart, hodgeStar] <;> ring

noncomputable def antiSelfDualPartLinear : TwoFormC →ₗ[ℂ] TwoFormC where
  toFun := antiSelfDualPart
  map_add' F G := by
    funext i
    fin_cases i <;> simp [antiSelfDualPart, hodgeStar] <;> ring
  map_smul' c F := by
    funext i
    fin_cases i <;> simp [antiSelfDualPart, hodgeStar] <;> ring

@[simp] theorem selfDualPartLinear_apply (F : TwoFormC) :
    selfDualPartLinear F = selfDualPart F := rfl

@[simp] theorem antiSelfDualPartLinear_apply (F : TwoFormC) :
    antiSelfDualPartLinear F = antiSelfDualPart F := rfl

theorem selfDualPartLinear_add_antiSelfDualPartLinear (F : TwoFormC) :
    selfDualPartLinear F + antiSelfDualPartLinear F = F := by
  simpa [selfDualPartLinear_apply, antiSelfDualPartLinear_apply] using
    self_plus_anti F

theorem hodgeStarLinear_selfDualPartLinear (F : TwoFormC) :
    hodgeStarLinear (selfDualPartLinear F) =
      fun i => Complex.I * selfDualPartLinear F i := by
  simpa [hodgeStarLinear_apply, selfDualPartLinear_apply] using
    hodgeStar_selfDualPart F

theorem hodgeStarLinear_antiSelfDualPartLinear (F : TwoFormC) :
    hodgeStarLinear (antiSelfDualPartLinear F) =
      fun i => -Complex.I * antiSelfDualPartLinear F i := by
  simpa [hodgeStarLinear_apply, antiSelfDualPartLinear_apply] using
    hodgeStar_antiSelfDualPart F

theorem selfDualPartLinear_idempotent :
    selfDualPartLinear.comp selfDualPartLinear = selfDualPartLinear := by
  ext F i
  have h := hodgeStarLinear_selfDualPartLinear F
  have hi := congrFun h i
  simp only [LinearMap.comp_apply]
  rw [selfDualPartLinear_apply, selfDualPartLinear_apply]
  rw [selfDualPartLinear_apply] at hi
  rw [hodgeStarLinear_apply] at hi
  fin_cases i <;> simp [selfDualPart, hodgeStar] at hi ⊢ <;> ring_nf
  all_goals simp [Complex.I_sq] <;> ring

theorem antiSelfDualPartLinear_idempotent :
    antiSelfDualPartLinear.comp antiSelfDualPartLinear = antiSelfDualPartLinear := by
  ext F i
  have h := hodgeStarLinear_antiSelfDualPartLinear F
  have hi := congrFun h i
  simp only [LinearMap.comp_apply]
  rw [antiSelfDualPartLinear_apply, antiSelfDualPartLinear_apply]
  rw [antiSelfDualPartLinear_apply] at hi
  rw [hodgeStarLinear_apply] at hi
  fin_cases i <;> simp [antiSelfDualPart, hodgeStar] at hi ⊢ <;> ring_nf
  all_goals simp [Complex.I_sq] <;> ring

theorem selfDualPartLinear_comp_antiSelfDualPartLinear :
    selfDualPartLinear.comp antiSelfDualPartLinear = 0 := by
  ext F i
  simp only [LinearMap.comp_apply]
  fin_cases i <;> simp [selfDualPartLinear, antiSelfDualPartLinear,
    selfDualPart, antiSelfDualPart, hodgeStar] <;> ring_nf
  all_goals simp [Complex.I_sq]

theorem antiSelfDualPartLinear_comp_selfDualPartLinear :
    antiSelfDualPartLinear.comp selfDualPartLinear = 0 := by
  ext F i
  simp only [LinearMap.comp_apply]
  fin_cases i <;> simp [selfDualPartLinear, antiSelfDualPartLinear,
    selfDualPart, antiSelfDualPart, hodgeStar] <;> ring_nf
  all_goals simp [Complex.I_sq]

theorem selfDualPartLinear_eq_self_iff (F : TwoFormC) :
    selfDualPartLinear F = F ↔
      hodgeStarLinear F = fun i => Complex.I * F i := by
  constructor
  · intro h
    have he := hodgeStarLinear_selfDualPartLinear F
    rw [h] at he
    exact he
  · intro h
    ext i
    have hi : hodgeStar F i = Complex.I * F i := by
      simpa [hodgeStarLinear_apply] using congrFun h i
    change (F i - Complex.I * hodgeStar F i) / 2 = F i
    rw [hi]
    ring_nf
    rw [Complex.I_sq]
    ring

theorem antiSelfDualPartLinear_eq_self_iff (F : TwoFormC) :
    antiSelfDualPartLinear F = F ↔
      hodgeStarLinear F = fun i => -Complex.I * F i := by
  constructor
  · intro h
    have he := hodgeStarLinear_antiSelfDualPartLinear F
    rw [h] at he
    exact he
  · intro h
    ext i
    have hi : hodgeStar F i = -Complex.I * F i := by
      simpa [hodgeStarLinear_apply] using congrFun h i
    change (F i + Complex.I * hodgeStar F i) / 2 = F i
    rw [hi]
    ring_nf
    rw [Complex.I_sq]
    ring

theorem selfDualPartLinear_add_antiSelfDualPartLinear_map :
    selfDualPartLinear + antiSelfDualPartLinear = LinearMap.id := by
  ext F i
  simpa [LinearMap.add_apply, LinearMap.id_apply] using
    congrFun (selfDualPartLinear_add_antiSelfDualPartLinear F) i

theorem hodgeStarLinear_comp_selfDualPartLinear :
    hodgeStarLinear.comp selfDualPartLinear =
      Complex.I • selfDualPartLinear := by
  ext F i
  have h := hodgeStarLinear_selfDualPartLinear F
  simpa [LinearMap.comp_apply, Pi.smul_apply] using congrFun h i

theorem hodgeStarLinear_comp_antiSelfDualPartLinear :
    hodgeStarLinear.comp antiSelfDualPartLinear =
      (-Complex.I) • antiSelfDualPartLinear := by
  ext F i
  have h := hodgeStarLinear_antiSelfDualPartLinear F
  simpa [LinearMap.comp_apply, Pi.smul_apply] using congrFun h i

theorem hodgeStarLinear_square :
    hodgeStarLinear.comp hodgeStarLinear = -LinearMap.id := by
  ext F i
  fin_cases i <;> simp [hodgeStarLinear, hodgeStar]

theorem hodgeStarLinear_square_apply (F : TwoFormC) :
    hodgeStarLinear (hodgeStarLinear F) = -F := by
  have h := congrArg (fun f : TwoFormC →ₗ[ℂ] TwoFormC => f F)
    hodgeStarLinear_square
  simpa [LinearMap.comp_apply] using h

theorem hodgeStarLinear_signed_square :
    hodgeStarLinear.comp hodgeStarLinear =
      (-1 : ℂ) • LinearMap.id := by
  rw [hodgeStarLinear_square]
  ext F i
  simp

theorem hodgeStarLinear_signed_square_apply (F : TwoFormC) :
    hodgeStarLinear (hodgeStarLinear F) = (-1 : ℂ) • F := by
  have h := congrArg (fun f : TwoFormC →ₗ[ℂ] TwoFormC => f F)
    hodgeStarLinear_signed_square
  simpa [LinearMap.comp_apply] using h

end InfoGeometry.Canonical.HodgeStar4DFiniteLinearBridge
