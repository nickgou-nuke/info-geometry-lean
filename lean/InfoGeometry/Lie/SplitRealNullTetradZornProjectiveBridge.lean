import InfoGeometry.Lie.SplitRealNullTetradZornBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionEllKleinProjectiveFlow

/-!
# Projective transport of the split-real tetrad/Zorn intertwiner

The injective tetrad embedding descends to projective rays.  The uniform
double-Witt boost and the closed active `ell` flow commute after this
projectivization.  This is a projective linear-flow theorem, not a statement
about Newman--Penrose connections or split-octonion multiplication.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Lie.SplitRealNullTetradZornProjectiveBridge

open InfoGeometry.Clifford.SplitRealNullTetrad
open InfoGeometry.Lie.SplitOctonionEllKleinFlow
open InfoGeometry.Lie.SplitOctonionEllKleinProjectiveFlow
open InfoGeometry.Lie.SplitOctonionAxialKleinProjective
open InfoGeometry.Lie.SplitRealNullTetradZornBridge.Tetrad

abbrev TetradProjective := ℙ ℝ Carrier
abbrev ActiveProjective :=
  ℙ ℝ InfoGeometry.Lie.SplitOctonionAxialWittReduction.ActiveSector

/-- Projectivization of the concrete injective tetrad embedding. -/
def tetradActiveProjectiveMap : TetradProjective → ActiveProjective :=
  Projectivization.map toActive toActive_injective

private theorem toActive_ne_zero (X : Carrier) (hX : X ≠ 0) :
    toActive X ≠ 0 := by
  intro h
  apply hX
  apply toActive_injective
  simpa using h

@[simp] theorem tetradActiveProjectiveMap_mk
    (X : Carrier) (hX : X ≠ 0) :
    tetradActiveProjectiveMap (Projectivization.mk ℝ X hX) =
      Projectivization.mk ℝ (toActive X) (toActive_ne_zero X hX) := by
  exact Projectivization.map_mk _ _ _ _

theorem isKlein_tetradActiveProjectiveMap_mk_iff
    (X : Carrier) (hX : X ≠ 0) :
    _root_.InfoGeometry.Projective.ExteriorKleinProjective.IsKlein
        (InfoGeometry.Lie.SplitOctonionAxialKleinProjective.activeExteriorProjectiveMap
          (tetradActiveProjectiveMap (Projectivization.mk ℝ X hX))) ↔
      quad X = 0 := by
  rw [tetradActiveProjectiveMap_mk]
  rw [isKlein_activeExteriorProjectiveMap_mk_iff]
  exact toActive_null_iff X

theorem tetradActiveProjectiveMap_injective :
    Function.Injective tetradActiveProjectiveMap := by
  exact Projectivization.map_injective toActive toActive_injective

/-- Projectivized uniform double-Witt boost. -/
def doubleWittBoostProjectiveMap (t : ℝ) :
    TetradProjective → TetradProjective :=
  Projectivization.map (doubleWittBoostEquiv t).toLinearMap
    (doubleWittBoostEquiv t).injective

private theorem doubleWittBoost_ne_zero (t : ℝ)
    (X : Carrier) (hX : X ≠ 0) : doubleWittBoost t X ≠ 0 := by
  intro h
  apply hX
  have h' := congrArg (doubleWittBoost (-t)) h
  simpa [doubleWittBoost_neg_apply] using h'

@[simp] theorem doubleWittBoostProjectiveMap_mk (t : ℝ)
    (X : Carrier) (hX : X ≠ 0) :
    doubleWittBoostProjectiveMap t (Projectivization.mk ℝ X hX) =
      Projectivization.mk ℝ (doubleWittBoost t X)
        (doubleWittBoost_ne_zero t X hX) := by
  exact Projectivization.map_mk _ _ _ _

/-- The projectivized tetrad embedding intertwines the uniform double-Witt
boost with the already constructed projective active `ell` flow. -/
theorem tetradActiveProjectiveMap_intertwines
    (t : ℝ) (p : TetradProjective) :
    tetradActiveProjectiveMap (doubleWittBoostProjectiveMap t p) =
      ellFlowActiveProjectiveMap t (tetradActiveProjectiveMap p) := by
  refine Projectivization.ind (p := p) ?_
  intro X hX
  simp only [doubleWittBoostProjectiveMap_mk,
    tetradActiveProjectiveMap_mk, ellFlowActiveProjectiveMap_mk]
  congr 1
  exact toActive_intertwines_ellFlow t X

/-- The projective tetrad flow inherits the additive rapidity law. -/
theorem doubleWittBoostProjectiveMap_add (s t : ℝ)
    (p : TetradProjective) :
    doubleWittBoostProjectiveMap (s + t) p =
      doubleWittBoostProjectiveMap s (doubleWittBoostProjectiveMap t p) := by
  refine Projectivization.ind (p := p) ?_
  intro X hX
  simp only [doubleWittBoostProjectiveMap_mk]
  congr 1
  exact doubleWittBoost_add s t X

@[simp] theorem doubleWittBoostProjectiveMap_zero
    (p : TetradProjective) :
    doubleWittBoostProjectiveMap 0 p = p := by
  refine Projectivization.ind (p := p) ?_
  intro X hX
  simp only [doubleWittBoostProjectiveMap_mk]
  congr 1
  exact doubleWittBoost_zero X

theorem doubleWittBoostProjectiveMap_neg_left (t : ℝ)
    (p : TetradProjective) :
    doubleWittBoostProjectiveMap (-t)
        (doubleWittBoostProjectiveMap t p) = p := by
  have h := doubleWittBoostProjectiveMap_add (-t) t p
  rw [neg_add_cancel, doubleWittBoostProjectiveMap_zero] at h
  exact h.symm

theorem doubleWittBoostProjectiveMap_neg_right (t : ℝ)
    (p : TetradProjective) :
    doubleWittBoostProjectiveMap t
        (doubleWittBoostProjectiveMap (-t) p) = p := by
  have h := doubleWittBoostProjectiveMap_add t (-t) p
  rw [add_neg_cancel, doubleWittBoostProjectiveMap_zero] at h
  exact h.symm

theorem doubleWittBoostProjectiveMap_bijective (t : ℝ) :
    Function.Bijective (doubleWittBoostProjectiveMap t) := by
  constructor
  · intro p q h
    have h' := congrArg (doubleWittBoostProjectiveMap (-t)) h
    simpa only [doubleWittBoostProjectiveMap_neg_left] using h'
  · intro q
    refine ⟨doubleWittBoostProjectiveMap (-t) q, ?_⟩
    exact doubleWittBoostProjectiveMap_neg_right t q

/-- The concrete projective double-Witt flow is an actual equivalence. -/
def doubleWittBoostProjectiveEquiv (t : ℝ) :
    TetradProjective ≃ TetradProjective where
  toFun := doubleWittBoostProjectiveMap t
  invFun := doubleWittBoostProjectiveMap (-t)
  left_inv := doubleWittBoostProjectiveMap_neg_left t
  right_inv := doubleWittBoostProjectiveMap_neg_right t

@[simp] theorem doubleWittBoostProjectiveEquiv_apply
    (t : ℝ) (p : TetradProjective) :
    doubleWittBoostProjectiveEquiv t p =
      doubleWittBoostProjectiveMap t p := rfl

@[simp] theorem doubleWittBoostProjectiveEquiv_symm_apply
    (t : ℝ) (p : TetradProjective) :
    (doubleWittBoostProjectiveEquiv t).symm p =
      doubleWittBoostProjectiveMap (-t) p := rfl

theorem doubleWittBoostProjectiveEquiv_add
    (s t : ℝ) (p : TetradProjective) :
    doubleWittBoostProjectiveEquiv (s + t) p =
      doubleWittBoostProjectiveEquiv s
        (doubleWittBoostProjectiveEquiv t p) := by
  change doubleWittBoostProjectiveMap (s + t) p =
    doubleWittBoostProjectiveMap s
      (doubleWittBoostProjectiveMap t p)
  exact doubleWittBoostProjectiveMap_add s t p

theorem doubleWittBoostProjective_causalMinus_fixed (t : ℝ) :
    doubleWittBoostProjectiveMap t
        (Projectivization.mk ℝ causalMinus causalMinus_ne_zero) =
      Projectivization.mk ℝ causalMinus causalMinus_ne_zero := by
  rw [doubleWittBoostProjectiveMap, Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  exact ⟨Units.mk0 (Real.exp t) (Real.exp_ne_zero t), by
    change Real.exp t • causalMinus = doubleWittBoost t causalMinus
    rw [doubleWittBoost_causalMinus]⟩

theorem doubleWittBoostProjective_causalPlus_fixed (t : ℝ) :
    doubleWittBoostProjectiveMap t
        (Projectivization.mk ℝ causalPlus causalPlus_ne_zero) =
      Projectivization.mk ℝ causalPlus causalPlus_ne_zero := by
  rw [doubleWittBoostProjectiveMap, Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  exact ⟨Units.mk0 (Real.exp (-t)) (Real.exp_ne_zero (-t)), by
    change Real.exp (-t) • causalPlus = doubleWittBoost t causalPlus
    rw [doubleWittBoost_causalPlus]⟩

theorem doubleWittBoostProjective_entropyMinus_fixed (t : ℝ) :
    doubleWittBoostProjectiveMap t
        (Projectivization.mk ℝ entropyMinus entropyMinus_ne_zero) =
      Projectivization.mk ℝ entropyMinus entropyMinus_ne_zero := by
  rw [doubleWittBoostProjectiveMap, Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  exact ⟨Units.mk0 (Real.exp t) (Real.exp_ne_zero t), by
    change Real.exp t • entropyMinus = doubleWittBoost t entropyMinus
    rw [doubleWittBoost_entropyMinus]⟩

theorem doubleWittBoostProjective_entropyPlus_fixed (t : ℝ) :
    doubleWittBoostProjectiveMap t
        (Projectivization.mk ℝ entropyPlus entropyPlus_ne_zero) =
      Projectivization.mk ℝ entropyPlus entropyPlus_ne_zero := by
  rw [doubleWittBoostProjectiveMap, Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).2
  exact ⟨Units.mk0 (Real.exp (-t)) (Real.exp_ne_zero (-t)), by
    change Real.exp (-t) • entropyPlus = doubleWittBoost t entropyPlus
    rw [doubleWittBoost_entropyPlus]⟩

end InfoGeometry.Lie.SplitRealNullTetradZornProjectiveBridge
