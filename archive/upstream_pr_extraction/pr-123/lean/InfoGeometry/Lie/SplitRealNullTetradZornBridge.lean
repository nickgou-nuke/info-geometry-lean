import InfoGeometry.Clifford.SplitRealNullTetrad
import InfoGeometry.Lie.SplitOctonionEllKleinFlow

/-!
# A split-real null tetrad inside the active Zorn/Klein carrier

This file chooses a concrete four-dimensional subcarrier of the six-dimensional
active Zorn support.  Two Witt pairs of the native split `(2,2)` tetrad are
sent to the first two upper/lower Zorn coordinate pairs; the third pair is
zero.  The embedding preserves the native quadratic forms exactly.

The uniform double-Witt boost is deliberately distinct from the
entropy-plane-only boost.  It rescales both positive Witt coordinates by
`exp t` and both negative coordinates by `exp (-t)`, and therefore intertwines
the restriction of the closed `ell` flow.  No Newman--Penrose connection,
spin-coefficient, curvature, or split-octonion multiplication claim is made.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitRealNullTetradZornBridge

open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionAxialKleinBridge
open InfoGeometry.Lie.SplitOctonionAxialWittReduction
open InfoGeometry.Lie.SplitOctonionEllClosedFlow
open InfoGeometry.Lie.SplitOctonionEllKleinFlow

namespace Tetrad

open InfoGeometry.Clifford.SplitRealNullTetrad

abbrev Active :=
  InfoGeometry.Lie.SplitOctonionAxialWittReduction.ActiveSector

/-- The four tetrad Witt coordinates placed in the first two of the three
active Zorn Witt pairs. -/
def toActiveWitt : Carrier →ₗ[ℝ] WittCoordinates where
  toFun X :=
    (![wittCoordinates X 0, wittCoordinates X 2, 0],
      ![-wittCoordinates X 1, -wittCoordinates X 3, 0])
  map_add' X Y := by
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [wittCoordinates] <;> ring
  map_smul' r X := by
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [wittCoordinates, smul_eq_mul] <;> ring

/-- The chosen real `(2,2)` tetrad subcarrier of the active Zorn support. -/
def toActive : Carrier →ₗ[ℝ] Active :=
  activeSectorEquiv.symm.toLinearMap.comp toActiveWitt

@[simp] theorem activeSectorEquiv_toActive (X : Carrier) :
    activeSectorEquiv (toActive X) = toActiveWitt X := by
  exact activeSectorEquiv.apply_symm_apply (toActiveWitt X)

theorem toActiveWitt_injective : Function.Injective toActiveWitt := by
  intro X Y h
  have h0 := congrArg (fun Z : WittCoordinates => Z.1 0) h
  have h1 := congrArg (fun Z : WittCoordinates => Z.2 0) h
  have h2 := congrArg (fun Z : WittCoordinates => Z.1 1) h
  have h3 := congrArg (fun Z : WittCoordinates => Z.2 1) h
  apply funext
  intro i
  fin_cases i <;> simp [toActiveWitt, wittCoordinates] at h0 h1 h2 h3 ⊢ <;>
    linarith

theorem toActive_injective : Function.Injective toActive := by
  intro X Y h
  apply toActiveWitt_injective
  simpa only [activeSectorEquiv_toActive] using congrArg activeSectorEquiv h

/-! ## The uniform double-Witt boost and the `ell`-flow intertwiner -/

/-- The uniform boost of both hyperbolic planes.  This is not the
entropy-plane-only boost from the tetrad owner. -/
def doubleWittBoost (t : ℝ) : Carrier →ₗ[ℝ] Carrier where
  toFun X :=
    ![Real.cosh t * X 0 + Real.sinh t * X 1,
      Real.sinh t * X 0 + Real.cosh t * X 1,
      Real.cosh t * X 2 + Real.sinh t * X 3,
      Real.sinh t * X 2 + Real.cosh t * X 3]
  map_add' X Y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' r X := by
    funext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring

theorem doubleWittBoost_pairing (t : ℝ) (X Y : Carrier) :
    pairing (doubleWittBoost t X) (doubleWittBoost t Y) = pairing X Y := by
  have h := Real.cosh_sq_sub_sinh_sq t
  simp [pairing, doubleWittBoost]
  linear_combination
    (X 0 * Y 0 - X 1 * Y 1 + X 2 * Y 2 - X 3 * Y 3) * h

theorem doubleWittBoost_quad (t : ℝ) (X : Carrier) :
    quad (doubleWittBoost t X) = quad X := by
  simp only [quad_apply]
  exact doubleWittBoost_pairing t X X

theorem doubleWittBoost_quad_eq_zero_iff (t : ℝ) (X : Carrier) :
    quad (doubleWittBoost t X) = 0 ↔ quad X = 0 := by
  rw [doubleWittBoost_quad]

/-- The native Zorn determinant restricts to the split `(2,2)` tetrad
quadratic form. -/
theorem detZ_toActive (X : Carrier) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (toActive X).1 = quad X := by
  have hdet := kleinForm_activeKleinLinearEquiv (toActive X)
  rw [activeKleinLinearEquiv, LinearEquiv.trans_apply,
    activeSectorEquiv_toActive] at hdet
  have hw : wittKleinLinearEquiv (toActiveWitt X) =
      wittKleinEquiv (toActiveWitt X) := by
    change wittKleinLinearEquiv.toEquiv (toActiveWitt X) =
      wittKleinEquiv (toActiveWitt X)
    rw [wittKleinLinearEquiv_toEquiv]
  rw [← hdet, hw, kleinForm_wittKleinEquiv]
  simp [toActiveWitt, InfoGeometry.Canonical.ZornMatrix.dot, quad_apply,
    pairing, wittCoordinates]
  ring

/-! The quadratic identity determines the full polarized form.  The factor two
is explicit because `activeDetPolar` is the polarization difference rather
than the normalized symmetric bilinear pairing. -/

theorem detZ_toActive_polar (X Y : Carrier) :
    activeDetPolar (toActive X) (toActive Y) =
      2 * pairing X Y := by
  unfold activeDetPolar
  have hadd : (toActive (X + Y)).1 =
      (toActive X).1 + (toActive Y).1 := by
    exact congrArg Subtype.val (toActive.map_add X Y)
  rw [← hadd, detZ_toActive, detZ_toActive, detZ_toActive]
  simp only [quad_apply]
  simp [pairing]
  ring

theorem toActive_kleinPolar (X Y : Carrier) :
    activeKleinPolar (toActive X) (toActive Y) =
      2 * pairing X Y := by
  rw [activeKleinLinearEquiv_preserves_polar, detZ_toActive_polar]

theorem doubleWittBoost_toActive_kleinPolar (t : ℝ) (X Y : Carrier) :
    activeKleinPolar
        (toActive (doubleWittBoost t X))
        (toActive (doubleWittBoost t Y)) =
      activeKleinPolar (toActive X) (toActive Y) := by
  rw [toActive_kleinPolar, toActive_kleinPolar]
  rw [doubleWittBoost_pairing]

theorem doubleWittBoost_toActive_null_iff (t : ℝ) (X : Carrier) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        (toActive (doubleWittBoost t X)).1 = 0 ↔
      quad X = 0 := by
  rw [detZ_toActive, doubleWittBoost_quad]

theorem toActive_null_iff (X : Carrier) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (toActive X).1 = 0 ↔
      quad X = 0 := by
  rw [detZ_toActive]

/-- The image is literally supported on the first two Zorn Witt pairs. -/
@[simp] theorem toActive_third_upper (X : Carrier) :
    (activeSectorEquiv (toActive X)).1 2 = 0 := by
  simp [toActiveWitt]

@[simp] theorem toActive_third_lower (X : Carrier) :
    (activeSectorEquiv (toActive X)).2 2 = 0 := by
  simp [toActiveWitt]

@[simp] theorem doubleWittBoost_causalMinus (t : ℝ) :
    doubleWittBoost t causalMinus = Real.exp t • causalMinus := by
  have h := Real.cosh_add_sinh t
  funext i
  fin_cases i <;> simp [doubleWittBoost, causalMinus] <;> linarith

@[simp] theorem doubleWittBoost_causalPlus (t : ℝ) :
    doubleWittBoost t causalPlus = Real.exp (-t) • causalPlus := by
  have h := Real.cosh_sub_sinh t
  funext i
  fin_cases i <;> simp [doubleWittBoost, causalPlus] <;> linarith

@[simp] theorem doubleWittBoost_entropyMinus (t : ℝ) :
    doubleWittBoost t entropyMinus = Real.exp t • entropyMinus := by
  have h := Real.cosh_add_sinh t
  funext i
  fin_cases i <;> simp [doubleWittBoost, entropyMinus] <;> linarith

@[simp] theorem doubleWittBoost_entropyPlus (t : ℝ) :
    doubleWittBoost t entropyPlus = Real.exp (-t) • entropyPlus := by
  have h := Real.cosh_sub_sinh t
  funext i
  fin_cases i <;> simp [doubleWittBoost, entropyPlus] <;> linarith

theorem doubleWittBoost_add (s t : ℝ) (X : Carrier) :
    doubleWittBoost (s + t) X =
      doubleWittBoost s (doubleWittBoost t X) := by
  funext i
  fin_cases i <;>
    simp [doubleWittBoost, Real.cosh_add, Real.sinh_add] <;> ring

@[simp] theorem doubleWittBoost_zero (X : Carrier) :
    doubleWittBoost 0 X = X := by
  funext i
  fin_cases i <;> simp [doubleWittBoost]

theorem doubleWittBoost_neg_apply (t : ℝ) (X : Carrier) :
    doubleWittBoost (-t) (doubleWittBoost t X) = X := by
  rw [← doubleWittBoost_add]
  simp

theorem doubleWittBoost_apply_neg (t : ℝ) (X : Carrier) :
    doubleWittBoost t (doubleWittBoost (-t) X) = X := by
  rw [← doubleWittBoost_add]
  simp

/-- The double-Witt boost as a genuine linear equivalence. -/
def doubleWittBoostEquiv (t : ℝ) : Carrier ≃ₗ[ℝ] Carrier where
  toLinearMap := doubleWittBoost t
  invFun := doubleWittBoost (-t)
  left_inv := doubleWittBoost_neg_apply t
  right_inv := doubleWittBoost_apply_neg t

theorem toActiveWitt_doubleWittBoost (t : ℝ) (X : Carrier) :
    toActiveWitt (doubleWittBoost t X) =
      (Real.exp t • (toActiveWitt X).1,
        Real.exp (-t) • (toActiveWitt X).2) := by
  apply Prod.ext <;> funext i <;> fin_cases i
  all_goals
    simp [toActiveWitt, doubleWittBoost, wittCoordinates, smul_eq_mul]
  · rw [← Real.cosh_add_sinh]
    ring
  · rw [← Real.cosh_add_sinh]
    ring
  · rw [← Real.cosh_sub_sinh]
    ring
  · rw [← Real.cosh_sub_sinh]
    ring

theorem activeSectorEquiv_ellFlowActive (t : ℝ) (Z : Active) :
    activeSectorEquiv (ellFlowActive t Z) =
      (Real.exp t • (activeSectorEquiv Z).1,
        Real.exp (-t) • (activeSectorEquiv Z).2) := by
  change ((ellFlowPhi t Z.1).x, (ellFlowPhi t Z.1).y) = _
  rw [ellFlowPhi_coord]
  rfl

/-- Exact linear intertwining with the closed `ell` flow on the chosen
four-dimensional active subcarrier. -/
theorem toActive_intertwines_ellFlow (t : ℝ) (X : Carrier) :
    toActive (doubleWittBoost t X) = ellFlowActive t (toActive X) := by
  apply activeSectorEquiv.injective
  rw [activeSectorEquiv_toActive, toActiveWitt_doubleWittBoost,
    activeSectorEquiv_ellFlowActive, activeSectorEquiv_toActive]

/-- Consequently the concrete tetrad embedding transports the invariant
quadratic flow without changing its native `(2,2)` form. -/
theorem detZ_ellFlow_toActive (t : ℝ) (X : Carrier) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        (ellFlowActive t (toActive X)).1 = quad X := by
  rw [← toActive_intertwines_ellFlow, detZ_toActive, doubleWittBoost_quad]

end Tetrad

end InfoGeometry.Lie.SplitRealNullTetradZornBridge
