import Mathlib
import InfoGeometry.Canonical.ChiralConeZornCarrier

/-!
# Topology on the chiral Zorn carrier

The chiral Zorn owner is an algebraic, generally nonassociative carrier.  This
owner equips its finite coordinate model with the induced product topology and
records continuity of the native Zorn operations.  It does not turn the
carrier into an associative operator algebra.
-/

namespace InfoGeometry.Canonical.ChiralConeZornCarrier

open InfoGeometry.Physics.SplitOctonionBraidSU3

abbrev ZornCoordinate :=
  ℂ × ((Fin 3 → ℂ) × ((Fin 3 → ℂ) × ℂ))

def zornCoordinates : Zorn → ZornCoordinate := fun X =>
  (X.a, (X.u, (X.v, X.b)))

instance : TopologicalSpace Zorn :=
  TopologicalSpace.induced zornCoordinates inferInstance

theorem continuous_zornCoordinates : Continuous zornCoordinates :=
  continuous_induced_dom

theorem continuous_zorn_a :
    Continuous (fun X : Zorn => X.a) := by
  exact continuous_fst.comp continuous_zornCoordinates

theorem continuous_zorn_u :
    Continuous (fun X : Zorn => X.u) := by
  exact continuous_fst.comp (continuous_snd.comp continuous_zornCoordinates)

theorem continuous_zorn_v :
    Continuous (fun X : Zorn => X.v) := by
  exact continuous_fst.comp (continuous_snd.comp
    (continuous_snd.comp continuous_zornCoordinates))

theorem continuous_zorn_b :
    Continuous (fun X : Zorn => X.b) := by
  exact continuous_snd.comp (continuous_snd.comp
    (continuous_snd.comp continuous_zornCoordinates))

attribute [fun_prop] continuous_zorn_a continuous_zorn_u
  continuous_zorn_v continuous_zorn_b

theorem continuous_zorn_dot3 :
    Continuous (fun p : Zorn × Zorn => dot3 p.1.u p.2.v) := by
  have h0 := (continuous_apply 0).comp
    (continuous_zorn_u.comp
      (continuous_fst : Continuous (fun p : Zorn × Zorn => p.1)))
  have h1 := (continuous_apply 1).comp
    (continuous_zorn_u.comp
      (continuous_fst : Continuous (fun p : Zorn × Zorn => p.1)))
  have h2 := (continuous_apply 2).comp
    (continuous_zorn_u.comp
      (continuous_fst : Continuous (fun p : Zorn × Zorn => p.1)))
  have k0 := (continuous_apply 0).comp
    (continuous_zorn_v.comp
      (continuous_snd : Continuous (fun p : Zorn × Zorn => p.2)))
  have k1 := (continuous_apply 1).comp
    (continuous_zorn_v.comp
      (continuous_snd : Continuous (fun p : Zorn × Zorn => p.2)))
  have k2 := (continuous_apply 2).comp
    (continuous_zorn_v.comp
      (continuous_snd : Continuous (fun p : Zorn × Zorn => p.2)))
  simpa [dot3] using (((h0.mul k0).add (h1.mul k1)).add (h2.mul k2))

theorem continuous_zorn_dot3_vu :
    Continuous (fun p : Zorn × Zorn => dot3 p.1.v p.2.u) := by
  have h0 := (continuous_apply 0).comp
    (continuous_zorn_v.comp
      (continuous_fst : Continuous (fun p : Zorn × Zorn => p.1)))
  have h1 := (continuous_apply 1).comp
    (continuous_zorn_v.comp
      (continuous_fst : Continuous (fun p : Zorn × Zorn => p.1)))
  have h2 := (continuous_apply 2).comp
    (continuous_zorn_v.comp
      (continuous_fst : Continuous (fun p : Zorn × Zorn => p.1)))
  have k0 := (continuous_apply 0).comp
    (continuous_zorn_u.comp
      (continuous_snd : Continuous (fun p : Zorn × Zorn => p.2)))
  have k1 := (continuous_apply 1).comp
    (continuous_zorn_u.comp
      (continuous_snd : Continuous (fun p : Zorn × Zorn => p.2)))
  have k2 := (continuous_apply 2).comp
    (continuous_zorn_u.comp
      (continuous_snd : Continuous (fun p : Zorn × Zorn => p.2)))
  simpa [dot3] using (((h0.mul k0).add (h1.mul k1)).add (h2.mul k2))

theorem continuous_zorn_cross3 :
    Continuous (fun p : Zorn × Zorn => cross3 p.1.v p.2.v) := by
  apply continuous_pi
  intro i
  fin_cases i
  · simp only [cross3]
    exact
      ((continuous_apply 1).comp (continuous_zorn_v.comp continuous_fst)).mul
          ((continuous_apply 2).comp (continuous_zorn_v.comp continuous_snd)) |>.sub
        (((continuous_apply 2).comp (continuous_zorn_v.comp continuous_fst)).mul
          ((continuous_apply 1).comp (continuous_zorn_v.comp continuous_snd)))
  · simp only [cross3]
    exact
      ((continuous_apply 2).comp (continuous_zorn_v.comp continuous_fst)).mul
          ((continuous_apply 0).comp (continuous_zorn_v.comp continuous_snd)) |>.sub
        (((continuous_apply 0).comp (continuous_zorn_v.comp continuous_fst)).mul
          ((continuous_apply 2).comp (continuous_zorn_v.comp continuous_snd)))
  · simp only [cross3]
    exact
      ((continuous_apply 0).comp (continuous_zorn_v.comp continuous_fst)).mul
          ((continuous_apply 1).comp (continuous_zorn_v.comp continuous_snd)) |>.sub
        (((continuous_apply 1).comp (continuous_zorn_v.comp continuous_fst)).mul
          ((continuous_apply 0).comp (continuous_zorn_v.comp continuous_snd)))

attribute [fun_prop] continuous_zorn_cross3

theorem continuous_zorn_cross3_uu :
    Continuous (fun p : Zorn × Zorn => cross3 p.1.u p.2.u) := by
  apply continuous_pi
  intro i
  fin_cases i
  · simp only [cross3]
    exact
      ((continuous_apply 1).comp (continuous_zorn_u.comp continuous_fst)).mul
          ((continuous_apply 2).comp (continuous_zorn_u.comp continuous_snd)) |>.sub
        (((continuous_apply 2).comp (continuous_zorn_u.comp continuous_fst)).mul
          ((continuous_apply 1).comp (continuous_zorn_u.comp continuous_snd)))
  · simp only [cross3]
    exact
      ((continuous_apply 2).comp (continuous_zorn_u.comp continuous_fst)).mul
          ((continuous_apply 0).comp (continuous_zorn_u.comp continuous_snd)) |>.sub
        (((continuous_apply 0).comp (continuous_zorn_u.comp continuous_fst)).mul
          ((continuous_apply 2).comp (continuous_zorn_u.comp continuous_snd)))
  · simp only [cross3]
    exact
      ((continuous_apply 0).comp (continuous_zorn_u.comp continuous_fst)).mul
          ((continuous_apply 1).comp (continuous_zorn_u.comp continuous_snd)) |>.sub
        (((continuous_apply 1).comp (continuous_zorn_u.comp continuous_fst)).mul
          ((continuous_apply 0).comp (continuous_zorn_u.comp continuous_snd)))

attribute [fun_prop] continuous_zorn_dot3 continuous_zorn_dot3_vu
  continuous_zorn_cross3_uu

theorem continuous_zornMul :
    Continuous (fun p : Zorn × Zorn => zornMul p.1 p.2) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : Zorn × Zorn =>
    zornCoordinates (zornMul p.1 p.2))
  unfold zornCoordinates zornMul
  fun_prop

theorem continuous_zornAdd :
    Continuous (fun p : Zorn × Zorn => zornAdd p.1 p.2) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : Zorn × Zorn =>
    zornCoordinates (zornAdd p.1 p.2))
  unfold zornCoordinates zornAdd
  fun_prop

theorem continuous_zornSub :
    Continuous (fun p : Zorn × Zorn => zornSub p.1 p.2) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : Zorn × Zorn =>
    zornCoordinates (zornSub p.1 p.2))
  unfold zornCoordinates zornSub
  fun_prop

theorem continuous_zornSmul :
    Continuous (fun p : ℂ × Zorn => zornSmul p.1 p.2) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : ℂ × Zorn =>
    zornCoordinates (zornSmul p.1 p.2))
  unfold zornCoordinates zornSmul
  fun_prop

theorem continuous_leftRegular (X : Zorn) :
    Continuous (leftRegular X) := by
  simpa [leftRegular, Function.comp_def] using
    (continuous_zornMul.comp (continuous_const.prodMk continuous_id))

end InfoGeometry.Canonical.ChiralConeZornCarrier
