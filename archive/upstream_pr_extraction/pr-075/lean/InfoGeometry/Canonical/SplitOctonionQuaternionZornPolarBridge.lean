import InfoGeometry.Canonical.SplitOctonionQuaternionPolar
import InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionQuaternionZornPolarBridge

open SplitOctonion
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates

abbrev H := Quaternion ℝ
abbrev Vec3 := Fin 3 → ℝ
abbrev QuaternionCoordinates := ℝ × Vec3
abbrev CartesianCoordinates := QuaternionCoordinates × QuaternionCoordinates
abbrev CanonicalZorn := InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CZ

/-- The real coordinate equivalence for a quaternion. -/
noncomputable def quaternionCoordinatesEquiv : H ≃ QuaternionCoordinates where
  toFun q := (q.re, ![q.imI, q.imJ, q.imK])
  invFun q := QuaternionAlgebra.mk (q.1) (q.2 0) (q.2 1) (q.2 2)
  left_inv q := by
    apply QuaternionAlgebra.ext
    · rfl
    · rfl
    · rfl
    · rfl
  right_inv q := by
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> rfl

@[simp] theorem quaternionCoordinatesEquiv_apply (q : H) :
    quaternionCoordinatesEquiv q = (q.re, ![q.imI, q.imJ, q.imK]) := rfl

@[simp] theorem quaternionCoordinatesEquiv_symm_apply (q : QuaternionCoordinates) :
    quaternionCoordinatesEquiv.symm q =
      QuaternionAlgebra.mk (q.1) (q.2 0) (q.2 1) (q.2 2) := rfl

def quaternionCoordinatesMul (q r : QuaternionCoordinates) :
    QuaternionCoordinates :=
  (q.1 * r.1 - InfoGeometry.Canonical.ZornMatrix.dot q.2 r.2,
    fun i => q.1 * r.2 i + r.1 * q.2 i +
      InfoGeometry.Canonical.ZornMatrix.cross q.2 r.2 i)

theorem quaternionCoordinatesEquiv_mul (q r : H) :
    quaternionCoordinatesEquiv (q * r) =
      quaternionCoordinatesMul (quaternionCoordinatesEquiv q)
        (quaternionCoordinatesEquiv r) := by
  apply Prod.ext
  · simp [quaternionCoordinatesMul, quaternionCoordinatesEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot, QuaternionAlgebra.re_mul]
    ring
  · funext i
    fin_cases i <;>
      simp [quaternionCoordinatesMul, quaternionCoordinatesEquiv,
        InfoGeometry.Canonical.ZornMatrix.cross,
        QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
        QuaternionAlgebra.imK_mul] <;>
      ring

theorem quaternionCoordinatesEquiv_add (q r : H) :
    quaternionCoordinatesEquiv (q + r) =
      quaternionCoordinatesEquiv q + quaternionCoordinatesEquiv r := by
  apply Prod.ext
  · simp [quaternionCoordinatesEquiv]
  · funext i
    fin_cases i <;> simp [quaternionCoordinatesEquiv]

theorem quaternionCoordinatesEquiv_star (q : H) :
    quaternionCoordinatesEquiv (star q) =
      (q.re, fun i => -((quaternionCoordinatesEquiv q).2 i)) := by
  apply Prod.ext
  · simp [quaternionCoordinatesEquiv]
  · funext i
    fin_cases i <;> simp [quaternionCoordinatesEquiv]

noncomputable def splitOctonionPairEquiv : SplitOctonion ≃ H × H where
  toFun X := (X.a, X.b)
  invFun p := ⟨p.1, p.2⟩
  left_inv X := by cases X; rfl
  right_inv p := by cases p; rfl

/-- The quaternion-pair carrier is linearly identified with the Cartesian
`(4+4)` coordinates used by the canonical Zorn carrier. -/
noncomputable def splitOctonionCartesianEquiv :
    SplitOctonion ≃ CartesianCoordinates :=
  splitOctonionPairEquiv.trans
    (Equiv.prodCongr quaternionCoordinatesEquiv quaternionCoordinatesEquiv)

@[simp] theorem splitOctonionCartesianEquiv_apply (X : SplitOctonion) :
    splitOctonionCartesianEquiv X =
      (quaternionCoordinatesEquiv X.a, quaternionCoordinatesEquiv X.b) := rfl

/-- The resulting native linear equivalence to the canonical Zorn carrier. -/
noncomputable def splitOctonionCanonicalZornEquiv :
    SplitOctonion ≃ CanonicalZorn :=
  splitOctonionCartesianEquiv.trans cartesianZornLinearEquiv.toEquiv

@[simp] theorem splitOctonionCanonicalZornEquiv_apply (X : SplitOctonion) :
    splitOctonionCanonicalZornEquiv X =
      cartesianZornLinearEquiv
        (quaternionCoordinatesEquiv X.a, quaternionCoordinatesEquiv X.b) := rfl

theorem quaternionNorm_coordinates (q : H) :
    quaternionNorm (quaternionCoordinatesEquiv q) = Quaternion.normSq q := by
  simp [quaternionNorm, quaternionCoordinatesEquiv,
    InfoGeometry.Canonical.ZornMatrix.dot,
    Quaternion.normSq,
    Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star,
    Quaternion.re_star, Quaternion.re_mul]
  ring

theorem splitOctonionCanonicalZornEquiv_norm (X : SplitOctonion) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        (splitOctonionCanonicalZornEquiv X) = normSQ X := by
  change InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
      (cartesianZornLinearEquiv
        (quaternionCoordinatesEquiv X.a, quaternionCoordinatesEquiv X.b)) = normSQ X
  rw [detZ_cartesianZornLinearEquiv]
  rw [quaternionNorm_coordinates, quaternionNorm_coordinates]
  unfold normSQ
  rw [normSq_eq_re_mul_star, normSq_eq_re_mul_star]

theorem isHyperbolic_iff_canonicalZorn_det_pos (X : SplitOctonion) :
    isHyperbolic X ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        (splitOctonionCanonicalZornEquiv X) > 0 := by
  unfold isHyperbolic
  rw [splitOctonionCanonicalZornEquiv_norm]

theorem polarRho_eq_canonicalZorn_det_sqrt
    (X : SplitOctonion) (h : isHyperbolic X) :
    polarRho X h = Real.sqrt
      (InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        (splitOctonionCanonicalZornEquiv X)) := by
  unfold polarRho
  rw [splitOctonionCanonicalZornEquiv_norm]

def quaternionCoordinatesStar (q : QuaternionCoordinates) : QuaternionCoordinates :=
  (q.1, fun i => -q.2 i)

def splitOctonionCartesianMul (X Y : CartesianCoordinates) :
    CartesianCoordinates :=
  (quaternionCoordinatesMul X.1 Y.1 +
      quaternionCoordinatesMul (quaternionCoordinatesStar Y.2) X.2,
    quaternionCoordinatesMul Y.2 X.1 +
      quaternionCoordinatesMul X.2 (quaternionCoordinatesStar Y.1))

theorem splitOctonionCartesianEquiv_mul (X Y : SplitOctonion) :
    splitOctonionCartesianEquiv (X * Y) =
      splitOctonionCartesianMul
        (splitOctonionCartesianEquiv X) (splitOctonionCartesianEquiv Y) := by
  rw [splitOctonionCartesianEquiv_apply]
  apply Prod.ext
  · change quaternionCoordinatesEquiv (X.a * Y.a + star Y.b * X.b) = _
    rw [quaternionCoordinatesEquiv_add, quaternionCoordinatesEquiv_mul,
      quaternionCoordinatesEquiv_mul, quaternionCoordinatesEquiv_star]
    rfl
  · change quaternionCoordinatesEquiv (Y.b * X.a + X.b * star Y.a) = _
    rw [quaternionCoordinatesEquiv_add, quaternionCoordinatesEquiv_mul,
      quaternionCoordinatesEquiv_mul, quaternionCoordinatesEquiv_star]
    rfl

/-! The polar factorization transports through the genuine Cartesian
    multiplication law above.  This is deliberately stated for the pullback
    product, not for the non-multiplicative linear map into the canonical Zorn
    carrier. -/
theorem polar_decomposition_cartesian (X : SplitOctonion)
    (h : isHyperbolic X) (hb : X.b ≠ 0) :
    splitOctonionCartesianEquiv X =
      splitOctonionCartesianMul
        (splitOctonionCartesianEquiv
          ⟨polarRho X h • polarU X (a_ne_zero_of_isHyperbolic X h), 0⟩)
        (splitOctonionCartesianEquiv
          (expHyperbolic 1 (polarEta X h)
            (J_g (polarG X (a_ne_zero_of_isHyperbolic X h) hb)))) := by
  have hX := congrArg splitOctonionCartesianEquiv
    (polar_decomposition X h hb)
  rw [splitOctonionCartesianEquiv_mul] at hX
  exact hX

def quaternionImaginaryI : H := QuaternionAlgebra.mk 0 1 0 0

theorem splitOctonionCanonicalZornEquiv_not_mul :
    ∃ X Y : SplitOctonion,
      splitOctonionCanonicalZornEquiv (X * Y) ≠
        splitOctonionCanonicalZornEquiv X * splitOctonionCanonicalZornEquiv Y := by
  refine ⟨⟨0, 1⟩, ⟨0, quaternionImaginaryI⟩, ?_⟩
  intro h
  have hx := congrArg (fun Z : CanonicalZorn => Z.x 0) h
  norm_num [splitOctonionCanonicalZornEquiv, splitOctonionCartesianEquiv,
    splitOctonionPairEquiv, quaternionCoordinatesEquiv,
    cartesianZornLinearEquiv, SplitOctonion.instMul,
    InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.cross,
    InfoGeometry.Canonical.ZornMatrix.dot, quaternionImaginaryI] at hx

end InfoGeometry.Canonical.SplitOctonionQuaternionZornPolarBridge
