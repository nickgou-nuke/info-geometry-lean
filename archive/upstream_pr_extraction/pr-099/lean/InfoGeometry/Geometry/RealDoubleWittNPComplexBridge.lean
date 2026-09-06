import InfoGeometry.Geometry.NewmanPenroseNullTetrad
import InfoGeometry.Geometry.RealDoubleWittNPReadout
import InfoGeometry.Geometry.RealDoubleWittNPFlow

/-!
# Real double-Witt carrier in the complex NP carrier

The real `(2,2)` carrier is embedded into the complexified Lorentz carrier by
the coordinate-preserving real-linear map.  The map is injective and its
bilinear readout is exactly the real causal form, with the normalization used
by `lorentzBilinear`.

This is a carrier intertwiner only; it introduces no connection or curvature
data.
-/

namespace InfoGeometry.Geometry.RealDoubleWittNPComplexBridge

noncomputable section

open InfoGeometry.Geometry.NewmanPenrose
open InfoGeometry.Geometry.RealDoubleWittNP

def toComplex : RealDoubleWittNP.Carrier →ₗ[ℝ] NewmanPenrose.Carrier where
  toFun x := ![
    (x.1 0 : ℂ),
    (x.2 1 : ℂ),
    Complex.I * (x.2 0 : ℂ),
    (x.1 1 : ℂ)]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp <;> ring

@[simp] theorem toComplex_apply (x : RealDoubleWittNP.Carrier) :
    toComplex x = ![
      (x.1 0 : ℂ),
      (x.2 1 : ℂ),
      Complex.I * (x.2 0 : ℂ),
      (x.1 1 : ℂ)] := rfl

theorem toComplex_injective : Function.Injective toComplex := by
  intro x y h
  apply Prod.ext
  · funext i
    fin_cases i
    · have hi := congrArg Complex.re (congrFun h 0)
      simpa [toComplex] using hi
    · have hi := congrArg Complex.re (congrFun h 3)
      simpa [toComplex] using hi
  · funext i
    fin_cases i
    · have hi := congrArg Complex.im (congrFun h 2)
      simpa [toComplex] using hi
    · have hr := congrArg Complex.re (congrFun h 1)
      simpa [toComplex] using hr

theorem lorentzBilinear_toComplex (x y : RealDoubleWittNP.Carrier) :
    NewmanPenrose.lorentzBilinear (toComplex x) (toComplex y) =
      (2 : ℂ) * (causalForm x y : ℂ) := by
  simp [NewmanPenrose.lorentzBilinear, toComplex, causalForm]
  ring_nf
  simp [Complex.I_mul_I]
  ring

theorem toComplex_preserves_null (x : RealDoubleWittNP.Carrier)
    (hx : causalForm x x = 0) :
    NewmanPenrose.lorentzBilinear (toComplex x) (toComplex x) = 0 := by
  rw [lorentzBilinear_toComplex, hx]
  simp

theorem lorentzBilinear_toComplex_self_eq_zero_iff
    (x : RealDoubleWittNP.Carrier) :
    NewmanPenrose.lorentzBilinear (toComplex x) (toComplex x) = 0 ↔
      causalForm x x = 0 := by
  rw [lorentzBilinear_toComplex]
  constructor
  · intro h
    exact_mod_cast (by simpa using h)
  · intro h
    simp [h]

theorem toComplex_cPlusLift :
    toComplex cPlusLift = NewmanPenrose.ell := by
  ext i
  fin_cases i <;> simp [toComplex, cPlusLift, cPlus,
    NewmanPenrose.ell]

theorem toComplex_cMinusLift :
    toComplex cMinusLift = (4 : ℂ) • NewmanPenrose.n := by
  ext i
  fin_cases i <;> simp [toComplex, cMinusLift, cMinus,
    NewmanPenrose.n]

theorem toComplex_ePlusLift :
    toComplex ePlusLift = (2 : ℂ) • NewmanPenrose.m := by
  ext i
  fin_cases i <;> simp [toComplex, ePlusLift, ePlus,
    NewmanPenrose.m] <;> ring

theorem toComplex_eMinusLift :
    toComplex eMinusLift = (-2 : ℂ) • NewmanPenrose.mbar := by
  ext i
  fin_cases i <;> simp [toComplex, eMinusLift, eMinus,
    NewmanPenrose.mbar] <;> ring

theorem star_toComplex_ePlusLift :
    star (toComplex ePlusLift) = -toComplex eMinusLift := by
  rw [toComplex_ePlusLift, toComplex_eMinusLift]
  simp [NewmanPenrose.np_conj_m]

theorem star_toComplex_eMinusLift :
    star (toComplex eMinusLift) = -toComplex ePlusLift := by
  rw [toComplex_eMinusLift, toComplex_ePlusLift]
  simp [NewmanPenrose.np_conj_mbar]

def doubleWittBoost (t : ℝ) :
    RealDoubleWittNP.Carrier →ₗ[ℝ] RealDoubleWittNP.Carrier where
  toFun x := (wittBoost t x.1, wittBoost t x.2)
  map_add' x y := by
    apply Prod.ext <;> simp
  map_smul' a x := by
    apply Prod.ext <;> simp

/-! The real-linear operator induced on the complex NP readout. -/

def npReadoutBoost (t : ℝ) :
    NewmanPenrose.Carrier →ₗ[ℝ] NewmanPenrose.Carrier where
  toFun z :=
    let a : ℂ := ((Real.exp t + Real.exp (-t)) / 2 : ℝ)
    let b : ℂ := ((Real.exp t - Real.exp (-t)) / 2 : ℝ)
    ![a * z 0 + b * z 3,
      a * z 1 - Complex.I * b * z 2,
      Complex.I * b * z 1 + a * z 2,
      b * z 0 + a * z 3]
  map_add' x y := by
    dsimp
    funext i
    fin_cases i <;> simp [Pi.add_apply] <;> ring
  map_smul' r x := by
    dsimp
    funext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul] <;> ring

theorem toComplex_doubleWittBoost_intertwines
    (t : ℝ) (x : RealDoubleWittNP.Carrier) :
    toComplex (doubleWittBoost t x) =
      npReadoutBoost t (toComplex x) := by
  funext i
  fin_cases i
  · simp [toComplex, doubleWittBoost, wittBoost, npReadoutBoost] <;> ring
  · simp [toComplex, doubleWittBoost, wittBoost, npReadoutBoost]
    ring_nf
    simp [Complex.I_sq]
    ring
  · simp [toComplex, doubleWittBoost, wittBoost, npReadoutBoost] <;> ring
  · simp [toComplex, doubleWittBoost, wittBoost, npReadoutBoost] <;> ring

@[simp] theorem doubleWittBoost_apply
    (t : ℝ) (x : RealDoubleWittNP.Carrier) :
    doubleWittBoost t x = (wittBoost t x.1, wittBoost t x.2) := rfl

theorem doubleWittBoost_preserves_causalForm
    (t : ℝ) (x y : RealDoubleWittNP.Carrier) :
    causalForm (doubleWittBoost t x) (doubleWittBoost t y) =
      causalForm x y := by
  rcases x with ⟨xc, xe⟩
  rcases y with ⟨yc, ye⟩
  change causalForm (wittBoost t xc, wittBoost t xe)
      (wittBoost t yc, wittBoost t ye) = causalForm (xc, xe) (yc, ye)
  simp only [causalForm]
  linear_combination
    wittBoost_preserves_plane_form t xc yc +
      wittBoost_preserves_plane_form t xe ye

theorem doubleWittBoost_preserves_null_iff
    (t : ℝ) (x : RealDoubleWittNP.Carrier) :
    causalForm (doubleWittBoost t x) (doubleWittBoost t x) = 0 ↔
      causalForm x x = 0 := by
  rw [doubleWittBoost_preserves_causalForm]

theorem doubleWittBoost_zero :
    doubleWittBoost 0 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x, y⟩
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [doubleWittBoost, wittBoost] <;> ring
  · funext i
    fin_cases i <;> simp [doubleWittBoost, wittBoost] <;> ring

theorem doubleWittBoost_add (s t : ℝ) :
    (doubleWittBoost s).comp (doubleWittBoost t) =
      doubleWittBoost (s + t) := by
  have hpos : Real.exp s * Real.exp t = Real.exp (s + t) := by
    rw [← Real.exp_add]
  have hneg : Real.exp (-s) * Real.exp (-t) = Real.exp (-(s + t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hplane (z : Plane) :
      wittBoost s (wittBoost t z) = wittBoost (s + t) z := by
    funext i
    fin_cases i
    · simp [wittBoost]
      rw [← mul_assoc, ← mul_assoc, hpos, hneg]
      rw [show -t + -s = -(s + t) by ring]
    · simp [wittBoost]
      rw [← mul_assoc, ← mul_assoc, hpos, hneg]
      rw [show -t + -s = -(s + t) by ring]
  apply LinearMap.ext
  intro x
  rcases x with ⟨x, y⟩
  apply Prod.ext
  · exact hplane x
  · exact hplane y

theorem doubleWittBoost_inverse (t : ℝ) :
    (doubleWittBoost (-t)).comp (doubleWittBoost t) = LinearMap.id := by
  rw [doubleWittBoost_add, neg_add_cancel, doubleWittBoost_zero]

theorem doubleWittBoost_inverse_right (t : ℝ) :
    (doubleWittBoost t).comp (doubleWittBoost (-t)) = LinearMap.id := by
  rw [doubleWittBoost_add, add_neg_cancel, doubleWittBoost_zero]

theorem doubleWittBoost_injective (t : ℝ) :
    Function.Injective (doubleWittBoost t) := by
  intro x y hxy
  have h := congrArg (doubleWittBoost (-t)) hxy
  have hx := congrArg (fun f :
      RealDoubleWittNP.Carrier →ₗ[ℝ] RealDoubleWittNP.Carrier => f x)
    (doubleWittBoost_inverse t)
  have hy := congrArg (fun f :
      RealDoubleWittNP.Carrier →ₗ[ℝ] RealDoubleWittNP.Carrier => f y)
    (doubleWittBoost_inverse t)
  simpa [LinearMap.comp_apply] using
    (show x = y from (by
      calc
        x = doubleWittBoost (-t) (doubleWittBoost t x) := by
          simpa [LinearMap.comp_apply] using hx.symm
        _ = doubleWittBoost (-t) (doubleWittBoost t y) := h
        _ = y := by
          simpa [LinearMap.comp_apply] using hy))

theorem doubleWittBoost_surjective (t : ℝ) :
    Function.Surjective (doubleWittBoost t) := by
  intro y
  refine ⟨doubleWittBoost (-t) y, ?_⟩
  have hinv := congrArg (fun f :
      RealDoubleWittNP.Carrier →ₗ[ℝ] RealDoubleWittNP.Carrier => f y)
    (doubleWittBoost_inverse_right t)
  simpa [LinearMap.comp_apply] using hinv

theorem toComplex_doubleWittBoost_preserves_lorentzBilinear
    (t : ℝ) (x y : RealDoubleWittNP.Carrier) :
    NewmanPenrose.lorentzBilinear
        (toComplex (doubleWittBoost t x))
        (toComplex (doubleWittBoost t y)) =
      NewmanPenrose.lorentzBilinear (toComplex x) (toComplex y) := by
  rw [lorentzBilinear_toComplex, lorentzBilinear_toComplex,
    doubleWittBoost_preserves_causalForm]

theorem toComplex_doubleWittBoost_preserves_null_iff
    (t : ℝ) (x : RealDoubleWittNP.Carrier) :
    NewmanPenrose.lorentzBilinear
        (toComplex (doubleWittBoost t x))
        (toComplex (doubleWittBoost t x)) = 0 ↔
      NewmanPenrose.lorentzBilinear (toComplex x) (toComplex x) = 0 := by
  rw [lorentzBilinear_toComplex_self_eq_zero_iff,
    doubleWittBoost_preserves_null_iff,
    lorentzBilinear_toComplex_self_eq_zero_iff]

theorem doubleWittBoost_cPlusLift (t : ℝ) :
    doubleWittBoost t cPlusLift = Real.exp t • cPlusLift := by
  simp [doubleWittBoost, cPlusLift, wittBoost_cPlus]

theorem doubleWittBoost_cMinusLift (t : ℝ) :
    doubleWittBoost t cMinusLift = Real.exp (-t) • cMinusLift := by
  simp [doubleWittBoost, cMinusLift, wittBoost_cMinus]

theorem doubleWittBoost_ePlusLift (t : ℝ) :
    doubleWittBoost t ePlusLift = Real.exp t • ePlusLift := by
  simp [doubleWittBoost, ePlusLift, wittBoost_ePlus]

theorem doubleWittBoost_eMinusLift (t : ℝ) :
    doubleWittBoost t eMinusLift = Real.exp (-t) • eMinusLift := by
  simp [doubleWittBoost, eMinusLift, wittBoost_eMinus]

theorem toComplex_doubleWittBoost_cPlusLift (t : ℝ) :
    toComplex (doubleWittBoost t cPlusLift) =
      Real.exp t • NewmanPenrose.ell := by
  rw [doubleWittBoost_cPlusLift, map_smul, toComplex_cPlusLift]

theorem toComplex_doubleWittBoost_cMinusLift (t : ℝ) :
    toComplex (doubleWittBoost t cMinusLift) =
      Real.exp (-t) • ((4 : ℂ) • NewmanPenrose.n) := by
  rw [doubleWittBoost_cMinusLift, map_smul, toComplex_cMinusLift]

theorem toComplex_doubleWittBoost_ePlusLift (t : ℝ) :
    toComplex (doubleWittBoost t ePlusLift) =
      Real.exp t • ((2 : ℂ) • NewmanPenrose.m) := by
  rw [doubleWittBoost_ePlusLift, map_smul, toComplex_ePlusLift]

theorem toComplex_doubleWittBoost_eMinusLift (t : ℝ) :
    toComplex (doubleWittBoost t eMinusLift) =
      Real.exp (-t) • ((-2 : ℂ) • NewmanPenrose.mbar) := by
  rw [doubleWittBoost_eMinusLift, map_smul, toComplex_eMinusLift]

end

end InfoGeometry.Geometry.RealDoubleWittNPComplexBridge
