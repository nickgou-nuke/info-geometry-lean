import Mathlib
import InfoGeometry.Topology.ChiralSolderingTopological

/-!
# Cyclotomic charge on the native Zorn carrier

The upper and lower native Zorn coordinates carry opposite cubic weights.
This owner records the resulting charge as a continuous map on the same
coordinate topology used for native soldering.  It does not introduce a
second Zorn carrier or claim multiplicativity of the charge beyond the
coordinate calculation below.
-/

namespace InfoGeometry.Topology.NativeZornCyclotomicChargeTopological

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Topology.ChiralSolderingTopological

noncomputable section

abbrev Zorn := InfoGeometry.Algebra.ZornMatrix ℂ

/-- Cubic charge: upper coordinates have weight `ω`, lower coordinates `ω²`. -/
def nativeCubicCharge (ω : ℂ) (X : Zorn) : Zorn where
  a := X.a
  v := ω • X.v
  w := (ω ^ 2) • X.w
  b := X.b

@[simp] theorem nativeCubicCharge_a (ω : ℂ) (X : Zorn) :
    (nativeCubicCharge ω X).a = X.a := rfl

@[simp] theorem nativeCubicCharge_b (ω : ℂ) (X : Zorn) :
    (nativeCubicCharge ω X).b = X.b := rfl

theorem continuous_nativeCubicCharge (ω : ℂ) :
    Continuous (nativeCubicCharge ω : Zorn → Zorn) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun X : Zorn =>
    ZornMatrix.coordEquiv (nativeCubicCharge ω X))
  simp only [ZornMatrix.coordEquiv]
  change Continuous (fun X : Zorn =>
    (X.a, ω • X.v, (ω ^ 2) • X.w, X.b))
  have hv : Continuous (fun X : Zorn => ω • X.v) := by
    apply continuous_pi
    intro i
    exact continuous_const.mul ((continuous_apply i).comp continuous_zorn_v)
  have hw : Continuous (fun X : Zorn => (ω ^ 2) • X.w) := by
    apply continuous_pi
    intro i
    exact continuous_const.mul ((continuous_apply i).comp continuous_zorn_w)
  exact continuous_zorn_a.prodMk (hv.prodMk (hw.prodMk continuous_zorn_b))

theorem nativeCubicCharge_cube
    (ω : ℂ) (hω : ω ^ 3 = 1) (X : Zorn) :
    nativeCubicCharge ω (nativeCubicCharge ω (nativeCubicCharge ω X)) = X := by
  ext
  · rfl
  ·
    rename_i i
    simp [nativeCubicCharge, smul_eq_mul]
    calc
      ω * (ω * (ω * X.v i)) = ω ^ 3 * X.v i := by ring
      _ = X.v i := by rw [hω, one_mul]
  ·
    rename_i i
    simp [nativeCubicCharge, smul_eq_mul]
    calc
      ω ^ 2 * (ω ^ 2 * (ω ^ 2 * X.w i)) = (ω ^ 3) ^ 2 * X.w i := by ring
      _ = X.w i := by rw [hω]; norm_num
  · rfl

theorem nativeCubicCharge_cube_function
    (ω : ℂ) (hω : ω ^ 3 = 1) :
    (nativeCubicCharge ω) ∘ (nativeCubicCharge ω) ∘
        (nativeCubicCharge ω) = id := by
  funext X
  exact nativeCubicCharge_cube ω hω X

end
end InfoGeometry.Topology.NativeZornCyclotomicChargeTopological
