import InfoGeometry.Canonical.ProjectiveAffineConformalClosure55
import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Canonical.Cl55ProjectiveBoundary
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Coordinate bridge from the affine/projective `(5,5)` model to native `V55`

`PACSplit55` is a coordinate presentation of the same ten-dimensional split
quadratic space used by the native Clifford owner.  This file records the
typed coordinate transport without identifying the two projective quotients.
The custom `Projective55` quotient also contains the zero representative,
whereas Mathlib's `Projectivization` is formed from nonzero vectors.  This
owner therefore projectivizes only the explicitly nonzero conformal image.
-/

namespace InfoGeometry.Canonical.PACSplit55Cl55CoordinateBridge

open ProjectiveAffineConformalClosure55
open InfoGeometry.Clifford.Clifford55
open scoped LinearAlgebra.Projectivization

noncomputable def pacSplit55ToV55 (X : PACSplit55) : V55 :=
  (![X.x0, X.x1, X.x2, X.x3, X.u],
    ![X.y0, X.y1, X.y2, X.y3, X.v])

def pacSplit55Zero : PACSplit55 where
  x0 := 0
  x1 := 0
  x2 := 0
  x3 := 0
  y0 := 0
  y1 := 0
  y2 := 0
  y3 := 0
  u := 0
  v := 0

noncomputable def v55ToPacSplit55 (v : V55) : PACSplit55 where
  x0 := v.1 0
  x1 := v.1 1
  x2 := v.1 2
  x3 := v.1 3
  y0 := v.2 0
  y1 := v.2 1
  y2 := v.2 2
  y3 := v.2 3
  u := v.1 4
  v := v.2 4

theorem pacSplit55ToV55_left_inverse (X : PACSplit55) :
    v55ToPacSplit55 (pacSplit55ToV55 X) = X := by
  cases X
  simp [pacSplit55ToV55, v55ToPacSplit55]

theorem pacSplit55ToV55_right_inverse (v : V55) :
    pacSplit55ToV55 (v55ToPacSplit55 v) = v := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

@[simp] theorem pacSplit55ToV55_zero :
    pacSplit55ToV55 pacSplit55Zero = 0 := by
  ext i <;> fin_cases i <;> rfl

theorem pacSplit55ToV55_injective :
    Function.Injective pacSplit55ToV55 :=
  Function.LeftInverse.injective pacSplit55ToV55_left_inverse

theorem pacSplit55ToV55_ne_zero_iff (X : PACSplit55) :
    pacSplit55ToV55 X ≠ 0 ↔ X ≠ pacSplit55Zero := by
  constructor
  · intro hX hzero
    apply hX
    rw [hzero, pacSplit55ToV55_zero]
  · intro hX hzero
    apply hX
    apply pacSplit55ToV55_injective
    rw [hzero, pacSplit55ToV55_zero]

theorem pacSplit55ToV55_surjective :
    Function.Surjective pacSplit55ToV55 :=
  Function.RightInverse.surjective pacSplit55ToV55_right_inverse

theorem pacSplit55ToV55_smul (a : ℝ) (X : PACSplit55) :
    pacSplit55ToV55 (smul55 a X) = a • pacSplit55ToV55 X := by
  cases X
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

theorem v55ToPacSplit55_smul (a : ℝ) (v : V55) :
    v55ToPacSplit55 (a • v) = smul55 a (v55ToPacSplit55 v) := by
  apply pacSplit55ToV55_injective
  rw [pacSplit55ToV55_right_inverse, pacSplit55ToV55_smul,
    pacSplit55ToV55_right_inverse]

noncomputable def pacProjectivize
    (X : PACSplit55) (hX : X ≠ pacSplit55Zero) : ℙ ℝ V55 :=
  Projectivization.mk ℝ (pacSplit55ToV55 X)
    ((pacSplit55ToV55_ne_zero_iff X).mpr hX)

theorem pacProjectivize_smul
    (a : ℝ) (ha : a ≠ 0) (X : PACSplit55)
    (hX : X ≠ pacSplit55Zero) :
    pacProjectivize (smul55 a X)
        (by
          intro h
          apply hX
          apply pacSplit55ToV55_injective
          have h' : a • pacSplit55ToV55 X = 0 := by
            calc
              a • pacSplit55ToV55 X =
                  pacSplit55ToV55 (smul55 a X) :=
                (pacSplit55ToV55_smul a X).symm
              _ = pacSplit55ToV55 pacSplit55Zero := congrArg pacSplit55ToV55 h
              _ = 0 := pacSplit55ToV55_zero
          have h'' : pacSplit55ToV55 X = 0 := by
            rcases smul_eq_zero.mp h' with ha0 | hX0
            · exact (ha ha0).elim
            · exact hX0
          calc
            pacSplit55ToV55 X = 0 := h''
            _ = pacSplit55ToV55 pacSplit55Zero :=
              pacSplit55ToV55_zero.symm) =
      pacProjectivize X hX := by
  unfold pacProjectivize
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  exact ⟨a, (pacSplit55ToV55_smul a X).symm⟩

theorem nativeQ55_pacSplit55ToV55 (X : PACSplit55) :
    InfoGeometry.Clifford.Clifford55.Q55 (pacSplit55ToV55 X) = Q55 X := by
  cases X
  simp [pacSplit55ToV55, InfoGeometry.Clifford.Clifford55.Q55,
    InfoGeometry.Clifford.Clifford55.Q5,
    InfoGeometry.Clifford.Clifford55.coord5,
    InfoGeometry.Clifford.Clifford55.fst55,
    InfoGeometry.Clifford.Clifford55.snd55,
    ProjectiveAffineConformalClosure55.Q55,
    Fin.sum_univ_succ]
  ring

/-! The affine conformal null cone reads back to native Clifford nilpotence. -/

noncomputable def pac44NativeNullVector (x : PACSplit44) : V55 :=
  pacSplit55ToV55 (conformalEmbed44to55 x)

theorem pac44NativeNullVector_Q55 (x : PACSplit44) :
    InfoGeometry.Clifford.Clifford55.Q55 (pac44NativeNullVector x) = 0 := by
  unfold pac44NativeNullVector
  rw [nativeQ55_pacSplit55ToV55, conformalEmbed44to55_null]

theorem pac44NativeNullClifford_sq_zero (x : PACSplit44) :
    ι55 (pac44NativeNullVector x) * ι55 (pac44NativeNullVector x) = 0 := by
  rw [CliffordAlgebra.ι_sq_scalar, pac44NativeNullVector_Q55]
  simp

theorem pacProjectivize_isProjectiveNull
    (X : PACSplit55) (hX : X ≠ pacSplit55Zero)
    (hQ : Q55 X = 0) :
    InfoGeometry.Canonical.Cl55ProjectiveBoundary.IsProjectiveNull
      InfoGeometry.Clifford.Clifford55.Q55 (pacProjectivize X hX) := by
  unfold pacProjectivize
  change InfoGeometry.Clifford.Clifford55.Q55 (pacSplit55ToV55 X) = 0
  rw [nativeQ55_pacSplit55ToV55, hQ]

theorem conformalEmbed44to55_ne_zero (x : PACSplit44) :
    conformalEmbed44to55 x ≠ pacSplit55Zero := by
  intro h
  have hu := congrArg PACSplit55.u h
  have hv := congrArg PACSplit55.v h
  simp [conformalEmbed44to55, pacSplit55Zero] at hu hv
  linarith

noncomputable def pac44NativeProjectivePoint
    (x : PACSplit44) : ℙ ℝ V55 :=
  pacProjectivize (conformalEmbed44to55 x)
    (conformalEmbed44to55_ne_zero x)

def chartCoordinate55 (w : V55) : ℝ := w.1 4 + w.2 4

def pacSplit55Base44 (X : PACSplit55) : PACSplit44 where
  x0 := X.x0
  x1 := X.x1
  x2 := X.x2
  x3 := X.x3
  y0 := X.y0
  y1 := X.y1
  y2 := X.y2
  y3 := X.y3

def affineGauge55 (X : PACSplit55) : ℝ := X.u + X.v

def affineDifference55 (X : PACSplit55) : ℝ := X.u - X.v

theorem pacSplit55_Q55_factorization (X : PACSplit55) :
    ProjectiveAffineConformalClosure55.Q55 X = Q44 (pacSplit55Base44 X) +
      affineDifference55 X * affineGauge55 X := by
  cases X
  unfold ProjectiveAffineConformalClosure55.Q55 Q44 pacSplit55Base44
    affineDifference55 affineGauge55
  ring

theorem chartCoordinate55_eq_affineGauge55 (X : PACSplit55) :
    chartCoordinate55 (pacSplit55ToV55 X) = affineGauge55 X := by
  rfl

theorem nativeQ55_pacSplit55_factorization (X : PACSplit55) :
    InfoGeometry.Clifford.Clifford55.Q55 (pacSplit55ToV55 X) =
      Q44 (pacSplit55Base44 X) +
        affineDifference55 X * affineGauge55 X := by
  rw [nativeQ55_pacSplit55ToV55, pacSplit55_Q55_factorization]

theorem pacSplit55_null_boundary_iff (X : PACSplit55) :
    ProjectiveAffineConformalClosure55.Q55 X = 0 ∧ affineGauge55 X = 0 ↔
      Q44 (pacSplit55Base44 X) = 0 ∧ affineGauge55 X = 0 := by
  rw [pacSplit55_Q55_factorization]
  constructor
  · rintro ⟨hQ, hGauge⟩
    constructor
    · simpa [hGauge] using hQ
    · exact hGauge
  · rintro ⟨hQ, hGauge⟩
    constructor
    · simpa [hGauge] using hQ
    · exact hGauge

theorem nativeQ55_null_boundary_iff (X : PACSplit55) :
    InfoGeometry.Clifford.Clifford55.Q55 (pacSplit55ToV55 X) = 0 ∧
        affineGauge55 X = 0 ↔
      Q44 (pacSplit55Base44 X) = 0 ∧ affineGauge55 X = 0 := by
  rw [nativeQ55_pacSplit55_factorization]
  constructor
  · rintro ⟨hQ, hGauge⟩
    exact ⟨by simpa [hGauge] using hQ, hGauge⟩
  · rintro ⟨hQ, hGauge⟩
    exact ⟨by simpa [hGauge] using hQ, hGauge⟩

def nativeAffineChart55 (p : ℙ ℝ V55) : Prop :=
  Quotient.liftOn' p
    (fun w : {x : V55 // x ≠ 0} => chartCoordinate55 w.val ≠ 0)
    (by
      rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨c, hc, rfl⟩
      dsimp
      change ((c : ℝ) * w.1 4 + (c : ℝ) * w.2 4 ≠ 0) =
        (w.1 4 + w.2 4 ≠ 0)
      apply propext
      constructor
      · intro h
        intro hs
        apply h
        calc
          (c : ℝ) * w.1 4 + (c : ℝ) * w.2 4 =
              (c : ℝ) * (w.1 4 + w.2 4) := by ring
          _ = 0 := by rw [hs, mul_zero]
      · intro h
        simpa [mul_add] using mul_ne_zero (Units.ne_zero c) h)

def nativeConformalBoundary55 (p : ℙ ℝ V55) : Prop :=
  Quotient.liftOn' p
    (fun w : {x : V55 // x ≠ 0} => chartCoordinate55 w.val = 0)
    (by
      rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨c, hc, rfl⟩
      dsimp
      change ((c : ℝ) * w.1 4 + (c : ℝ) * w.2 4 = 0) =
        (w.1 4 + w.2 4 = 0)
      apply propext
      constructor
      · intro h
        have h' : (c : ℝ) * (w.1 4 + w.2 4) = 0 := by
          simpa [mul_add] using h
        exact (mul_eq_zero.mp h').resolve_left (Units.ne_zero c)
      · intro h
        calc
          (c : ℝ) * w.1 4 + (c : ℝ) * w.2 4 =
              (c : ℝ) * (w.1 4 + w.2 4) := by ring
          _ = 0 := by rw [h, mul_zero])

def pacSplit55Infinity : PACSplit55 where
  x0 := 0
  x1 := 0
  x2 := 0
  x3 := 0
  y0 := 0
  y1 := 0
  y2 := 0
  y3 := 0
  u := 1
  v := -1

theorem pacSplit55Infinity_ne_zero :
    pacSplit55Infinity ≠ pacSplit55Zero := by
  intro h
  have hu := congrArg PACSplit55.u h
  norm_num [pacSplit55Infinity, pacSplit55Zero] at hu

noncomputable def nativeInfinityVector : V55 :=
  pacSplit55ToV55 pacSplit55Infinity

theorem nativeInfinityVector_ne_zero : nativeInfinityVector ≠ 0 := by
  rw [nativeInfinityVector, pacSplit55ToV55_ne_zero_iff]
  exact pacSplit55Infinity_ne_zero

theorem nativeInfinityVector_Q55 :
    InfoGeometry.Clifford.Clifford55.Q55 nativeInfinityVector = 0 := by
  unfold nativeInfinityVector
  rw [nativeQ55_pacSplit55ToV55]
  unfold pacSplit55Infinity ProjectiveAffineConformalClosure55.Q55
  norm_num

theorem nativeInfinityVector_polar (w : V55) :
    QuadraticMap.polar InfoGeometry.Clifford.Clifford55.Q55 w
        nativeInfinityVector =
      2 * chartCoordinate55 w := by
  rw [QuadraticMap.polar]
  simp [InfoGeometry.Clifford.Clifford55.Q55_apply,
    nativeInfinityVector, chartCoordinate55, pacSplit55ToV55,
    pacSplit55Infinity, Fin.sum_univ_succ]
  ring

theorem nativeConformalBoundary55_iff_projectiveBoundary
    (p : ℙ ℝ V55) :
    nativeConformalBoundary55 p ↔
      InfoGeometry.Canonical.Cl55ProjectiveBoundary.IsOnProjectiveBoundary
        InfoGeometry.Clifford.Clifford55.Q55 nativeInfinityVector p := by
  induction p using Projectivization.ind with
  | h w hw =>
      change chartCoordinate55 w = 0 ↔
        QuadraticMap.polar InfoGeometry.Clifford.Clifford55.Q55 w
          nativeInfinityVector = 0
      rw [nativeInfinityVector_polar]
      constructor <;> intro h <;> linarith

noncomputable def nativeInfinityProjectivePoint : ℙ ℝ V55 :=
  InfoGeometry.Canonical.Cl55ProjectiveBoundary.pointAtInfinity
    nativeInfinityVector nativeInfinityVector_ne_zero

theorem nativeInfinityProjectivePoint_isNull :
    InfoGeometry.Canonical.Cl55ProjectiveBoundary.IsProjectiveNull
      InfoGeometry.Clifford.Clifford55.Q55 nativeInfinityProjectivePoint := by
  simpa [nativeInfinityProjectivePoint,
    InfoGeometry.Canonical.Cl55ProjectiveBoundary.ProjectiveNullQuadric] using
    (InfoGeometry.Canonical.Cl55ProjectiveBoundary.pointAtInfinity_is_null
      InfoGeometry.Clifford.Clifford55.Q55 nativeInfinityVector
      nativeInfinityVector_Q55 nativeInfinityVector_ne_zero)

theorem nativeInfinityProjectivePoint_mem_conformalBoundary55 :
    nativeConformalBoundary55 nativeInfinityProjectivePoint := by
  unfold nativeConformalBoundary55 nativeInfinityProjectivePoint
  change chartCoordinate55 nativeInfinityVector = 0
  unfold chartCoordinate55 nativeInfinityVector pacSplit55ToV55
    pacSplit55Infinity
  change (1 : ℝ) + (-1) = 0
  norm_num

theorem nativeAffineChart55_iff_not_nativeConformalBoundary55
    (p : ℙ ℝ V55) :
    nativeAffineChart55 p ↔ ¬ nativeConformalBoundary55 p := by
  refine Quotient.inductionOn' p ?_
  intro w
  change (chartCoordinate55 w.val ≠ 0) ↔ ¬ chartCoordinate55 w.val = 0
  simp

/-- The projective null carrier splits into the affine chart and its
    conformal boundary.  This is only the propositional partition induced by
    the chart coordinate; it does not assert a topology or compactification
    theorem. -/
theorem nativeAffineChart55_or_nativeConformalBoundary55
    (p : ℙ ℝ V55) :
    nativeAffineChart55 p ∨ nativeConformalBoundary55 p := by
  by_cases h : nativeConformalBoundary55 p
  · exact Or.inr h
  · exact Or.inl ((nativeAffineChart55_iff_not_nativeConformalBoundary55 p).2 h)

theorem nativeAffineChart55_not_nativeConformalBoundary55
    (p : ℙ ℝ V55) :
    nativeAffineChart55 p → ¬ nativeConformalBoundary55 p := by
  exact (nativeAffineChart55_iff_not_nativeConformalBoundary55 p).1

theorem nativeConformalBoundary55_pacProjectivize_iff
    (X : PACSplit55) (hX : X ≠ pacSplit55Zero) :
    nativeConformalBoundary55 (pacProjectivize X hX) ↔
      chartCoordinate55 (pacSplit55ToV55 X) = 0 := by
  unfold nativeConformalBoundary55 pacProjectivize
  rfl

theorem conformalEmbed44to55_chartCoordinate (x : PACSplit44) :
    chartCoordinate55 (pacSplit55ToV55 (conformalEmbed44to55 x)) = 1 := by
  unfold chartCoordinate55 pacSplit55ToV55 conformalEmbed44to55
  change (1 - Q44 x) / 2 + (1 + Q44 x) / 2 = 1
  ring

theorem pac44NativeProjectivePoint_mem_affineChart (x : PACSplit44) :
    nativeAffineChart55 (pac44NativeProjectivePoint x) := by
  unfold nativeAffineChart55 pac44NativeProjectivePoint pacProjectivize
  change chartCoordinate55
      (pacSplit55ToV55 (conformalEmbed44to55 x)) ≠ 0
  rw [conformalEmbed44to55_chartCoordinate]
  norm_num

theorem pac44NativeProjectivePoint_not_mem_conformalBoundary (x : PACSplit44) :
    ¬ nativeConformalBoundary55 (pac44NativeProjectivePoint x) := by
  unfold nativeConformalBoundary55 pac44NativeProjectivePoint pacProjectivize
  change chartCoordinate55
      (pacSplit55ToV55 (conformalEmbed44to55 x)) ≠ 0
  rw [conformalEmbed44to55_chartCoordinate]
  norm_num

theorem pac44NativeProjectivePoint_isNull (x : PACSplit44) :
    InfoGeometry.Canonical.Cl55ProjectiveBoundary.IsProjectiveNull
      InfoGeometry.Clifford.Clifford55.Q55
      (pac44NativeProjectivePoint x) := by
  exact pacProjectivize_isProjectiveNull
    (conformalEmbed44to55 x)
    (conformalEmbed44to55_ne_zero x)
    (conformalEmbed44to55_null x)

/-! ### Quotient-level affine chart readback -/

noncomputable def affineChartRetractRep (w : V55) : PACSplit44 where
  x0 := (chartCoordinate55 w)⁻¹ * w.1 0
  x1 := (chartCoordinate55 w)⁻¹ * w.1 1
  x2 := (chartCoordinate55 w)⁻¹ * w.1 2
  x3 := (chartCoordinate55 w)⁻¹ * w.1 3
  y0 := (chartCoordinate55 w)⁻¹ * w.2 0
  y1 := (chartCoordinate55 w)⁻¹ * w.2 1
  y2 := (chartCoordinate55 w)⁻¹ * w.2 2
  y3 := (chartCoordinate55 w)⁻¹ * w.2 3

theorem pacSplit44_ext
    (x y : PACSplit44)
    (hx0 : x.x0 = y.x0) (hx1 : x.x1 = y.x1)
    (hx2 : x.x2 = y.x2) (hx3 : x.x3 = y.x3)
    (hy0 : x.y0 = y.y0) (hy1 : x.y1 = y.y1)
    (hy2 : x.y2 = y.y2) (hy3 : x.y3 = y.y3) :
    x = y := by
  cases x
  cases y
  simp_all

theorem affineChartRetractRep_smul
    (a : ℝ) (ha : a ≠ 0) (w : V55) :
    affineChartRetractRep (a • w) = affineChartRetractRep w := by
  apply pacSplit44_ext <;>
    simp [affineChartRetractRep, chartCoordinate55, smul_eq_mul, ha]
    <;> field_simp [ha]

noncomputable def nativeAffineChartRetractRaw
    (p : ℙ ℝ V55) : PACSplit44 :=
  Quotient.liftOn' p
    (fun w : {x : V55 // x ≠ 0} => affineChartRetractRep w.val)
    (by
      rintro ⟨v, hv⟩ ⟨w, hw⟩ ⟨c, hc, rfl⟩
      change affineChartRetractRep ((c : ℝ) • w) = affineChartRetractRep w
      exact affineChartRetractRep_smul (c : ℝ) (Units.ne_zero c) w)

def nativeNullAffineChart55 (p : ℙ ℝ V55) : Prop :=
  InfoGeometry.Canonical.Cl55ProjectiveBoundary.IsProjectiveNull
      InfoGeometry.Clifford.Clifford55.Q55 p ∧ nativeAffineChart55 p

noncomputable def nativeAffineChartRetract
    (p : {p : ℙ ℝ V55 // nativeNullAffineChart55 p}) : PACSplit44 :=
  nativeAffineChartRetractRaw p.1

noncomputable def nativeAffineChartLift (x : PACSplit44) :
    {p : ℙ ℝ V55 // nativeNullAffineChart55 p} :=
  ⟨pac44NativeProjectivePoint x,
    ⟨pac44NativeProjectivePoint_isNull x,
      pac44NativeProjectivePoint_mem_affineChart x⟩⟩

theorem nativeAffineChartRetract_lift (x : PACSplit44) :
    nativeAffineChartRetract (nativeAffineChartLift x) = x := by
  unfold nativeAffineChartRetract nativeAffineChartLift
  change affineChartRetractRep
      (pacSplit55ToV55 (conformalEmbed44to55 x)) = x
  apply pacSplit44_ext <;>
    simp [affineChartRetractRep, chartCoordinate55,
      pacSplit55ToV55, conformalEmbed44to55]
    <;> ring

/-! ### The converse quotient-level chart identity -/

theorem nativeAffineChartLift_retract_rep
    (w : V55) (hw : w ≠ 0)
    (hQ : InfoGeometry.Clifford.Clifford55.Q55 w = 0)
    (hGauge : chartCoordinate55 w ≠ 0) :
    pac44NativeProjectivePoint (affineChartRetractRep w) =
      Projectivization.mk ℝ w hw := by
  let X : PACSplit55 := v55ToPacSplit55 w
  have hXQ : Q55 X = 0 := by
    rw [← nativeQ55_pacSplit55ToV55 X]
    simpa [X] using hQ
  have hFactor :
      Q44 (pacSplit55Base44 X) +
          affineDifference55 X * affineGauge55 X = 0 := by
    rw [← pacSplit55_Q55_factorization X, hXQ]
  have hBase :
      Q44 (pacSplit55Base44 X) =
        -affineDifference55 X * affineGauge55 X := by
    linarith
  have hGaugeX : affineGauge55 X = chartCoordinate55 w := by
    simp [X, affineGauge55, chartCoordinate55, v55ToPacSplit55]
  have hDiffX : affineDifference55 X = w.1 4 - w.2 4 := by
    simp [X, v55ToPacSplit55, affineDifference55]
  have hQRetract :
      Q44 (affineChartRetractRep w) =
        -affineDifference55 X / chartCoordinate55 w := by
    rw [hGaugeX] at hBase
    rw [hDiffX] at hBase ⊢
    simp [X, v55ToPacSplit55, pacSplit55Base44, affineDifference55,
      Q44] at hBase
    simp [X, v55ToPacSplit55, affineDifference55] at hBase ⊢
    unfold affineChartRetractRep Q44 chartCoordinate55 at *
    field_simp [hGauge]
    nlinarith [hBase]
  unfold pac44NativeProjectivePoint pacProjectivize
  have hvec :
      pacSplit55ToV55
          (conformalEmbed44to55 (affineChartRetractRep w)) =
        (chartCoordinate55 w)⁻¹ • w := by
    apply Prod.ext <;> funext i
    · fin_cases i
      · simp [conformalEmbed44to55, affineChartRetractRep,
          pacSplit55ToV55, chartCoordinate55]
      · simp [conformalEmbed44to55, affineChartRetractRep,
          pacSplit55ToV55, chartCoordinate55]
      · simp [conformalEmbed44to55, affineChartRetractRep,
          pacSplit55ToV55, chartCoordinate55]
      · simp [conformalEmbed44to55, affineChartRetractRep,
          pacSplit55ToV55, chartCoordinate55]
      · change (1 - Q44 (affineChartRetractRep w)) / 2 =
          (chartCoordinate55 w)⁻¹ * w.1 4
        rw [hQRetract]
        field_simp [hGauge]
        rw [hDiffX]
        simp [chartCoordinate55, affineDifference55]
        ring
    · fin_cases i
      · simp [conformalEmbed44to55, affineChartRetractRep,
          pacSplit55ToV55, chartCoordinate55]
      · simp [conformalEmbed44to55, affineChartRetractRep,
          pacSplit55ToV55, chartCoordinate55]
      · simp [conformalEmbed44to55, affineChartRetractRep,
          pacSplit55ToV55, chartCoordinate55]
      · simp [conformalEmbed44to55, affineChartRetractRep,
          pacSplit55ToV55, chartCoordinate55]
      · change (1 + Q44 (affineChartRetractRep w)) / 2 =
          (chartCoordinate55 w)⁻¹ * w.2 4
        rw [hQRetract]
        field_simp [hGauge]
        rw [hDiffX]
        simp [chartCoordinate55, affineDifference55]
        ring
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  exact ⟨(chartCoordinate55 w)⁻¹, hvec.symm⟩

theorem nativeAffineChartLift_retract
    (p : {p : ℙ ℝ V55 // nativeNullAffineChart55 p}) :
    nativeAffineChartLift (nativeAffineChartRetract p) = p := by
  rcases p with ⟨p, hp⟩
  apply Subtype.ext
  revert hp
  refine Quotient.inductionOn' p ?_
  intro w hp
  have hpNull := hp.1
  have hpChart := hp.2
  have hwQ : InfoGeometry.Clifford.Clifford55.Q55 w.1 = 0 := by
    change InfoGeometry.Clifford.Clifford55.Q55 w.1 = 0 at hpNull
    exact hpNull
  have hwGauge : chartCoordinate55 w.1 ≠ 0 := by
    change chartCoordinate55 w.1 ≠ 0 at hpChart
    exact hpChart
  change pac44NativeProjectivePoint
      (affineChartRetractRep w.1) = Quotient.mk'' w
  exact nativeAffineChartLift_retract_rep w.1 w.2 hwQ hwGauge

end InfoGeometry.Canonical.PACSplit55Cl55CoordinateBridge
