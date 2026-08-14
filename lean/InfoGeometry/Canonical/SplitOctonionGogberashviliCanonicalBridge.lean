import InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge
import InfoGeometry.Canonical.SplitOctonionSignalMultiplication
import InfoGeometry.Algebra.Zorn.CanonicalConjugation
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge

abbrev PaperZorn := InfoGeometry.Algebra.ZornMatrix ℝ
abbrev CanonicalZorn := InfoGeometry.Canonical.ZornMatrix ℝ

noncomputable def paperCanonicalLinearEquiv : PaperZorn ≃ₗ[ℝ] CanonicalZorn where
  toFun X := { a := X.a, b := X.b, x := X.v, y := X.w }
  invFun X := { a := X.a, v := X.x, w := X.y, b := X.b }
  left_inv X := by cases X; rfl
  right_inv X := by cases X; rfl
  map_add' X Y := by ext <;> rfl
  map_smul' r X := by ext <;> rfl

@[simp] theorem paperCanonicalLinearEquiv_a (X : PaperZorn) :
    (paperCanonicalLinearEquiv X).a = X.a := rfl

@[simp] theorem paperCanonicalLinearEquiv_b (X : PaperZorn) :
    (paperCanonicalLinearEquiv X).b = X.b := rfl

@[simp] theorem paperCanonicalLinearEquiv_x (X : PaperZorn) :
    (paperCanonicalLinearEquiv X).x = X.v := rfl

@[simp] theorem paperCanonicalLinearEquiv_y (X : PaperZorn) :
    (paperCanonicalLinearEquiv X).y = X.w := rfl

@[simp] theorem paperCanonicalLinearEquiv_mul (X Y : PaperZorn) :
    paperCanonicalLinearEquiv (X * Y) =
      paperCanonicalLinearEquiv X * paperCanonicalLinearEquiv Y := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [paperCanonicalLinearEquiv,
      InfoGeometry.Algebra.ZornMatrix.mul,
      InfoGeometry.Algebra.Vec3.dot,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot]
  · simp [paperCanonicalLinearEquiv,
      InfoGeometry.Algebra.ZornMatrix.mul,
      InfoGeometry.Algebra.Vec3.dot,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot]
    ring
  · funext i
    fin_cases i <;>
      simp [paperCanonicalLinearEquiv,
        InfoGeometry.Algebra.ZornMatrix.mul,
        InfoGeometry.Algebra.Vec3.add,
        InfoGeometry.Algebra.Vec3.sub,
        InfoGeometry.Algebra.Vec3.smul,
        InfoGeometry.Algebra.Vec3.cross,
        InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.cross]
    all_goals ring
  · funext i
    fin_cases i <;>
      simp [paperCanonicalLinearEquiv,
        InfoGeometry.Algebra.ZornMatrix.mul,
        InfoGeometry.Algebra.Vec3.add,
        InfoGeometry.Algebra.Vec3.smul,
        InfoGeometry.Algebra.Vec3.cross,
        InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.cross]
    all_goals ring

theorem paperCanonicalLinearEquiv_signalMul
    (c : ℝ) (hc : c ≠ 0) (s t :
      InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.SignalCoordinates) :
    paperCanonicalLinearEquiv
        (InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.toNativeZorn c
          (InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.signalMul c hc s t)) =
      paperCanonicalLinearEquiv
          (InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.toNativeZorn c s) *
        paperCanonicalLinearEquiv
          (InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.toNativeZorn c t) := by
  rw [InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.toNativeZorn_signalMul,
    paperCanonicalLinearEquiv_mul]

theorem paperCanonicalLinearEquiv_signalConj
    (c : ℝ) (s :
      InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.SignalCoordinates) :
    paperCanonicalLinearEquiv
        (InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.toNativeZorn c
          (InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.signalConj s)) =
      InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj
        (paperCanonicalLinearEquiv
          (InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.toNativeZorn c s)) := by
  rw [InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.toNativeZorn_signalConj]
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [paperCanonicalLinearEquiv,
      InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.signalNativeConj,
      InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.toNativeZorn,
      InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj,
      InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv,
      InfoGeometry.Algebra.ZornVectorMatrix.conj]
  · simp [paperCanonicalLinearEquiv,
      InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.signalNativeConj,
      InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.toNativeZorn,
      InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj,
      InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv,
      InfoGeometry.Algebra.ZornVectorMatrix.conj]
  · funext i
    fin_cases i <;>
      simp [paperCanonicalLinearEquiv,
        InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.signalNativeConj,
        InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.toNativeZorn,
        InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj,
        InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv,
        InfoGeometry.Algebra.ZornVectorMatrix.conj]
  · simp [paperCanonicalLinearEquiv,
      InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.signalNativeConj,
      InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.toNativeZorn,
      InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalConj,
      InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv,
      InfoGeometry.Algebra.ZornVectorMatrix.conj]

@[simp] theorem paperCanonicalLinearEquiv_norm (X : PaperZorn) :
    InfoGeometry.Algebra.ZornMatrix.zornNorm X =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        (paperCanonicalLinearEquiv X) := by
  simp [paperCanonicalLinearEquiv,
    InfoGeometry.Algebra.ZornMatrix.zornNorm,
    InfoGeometry.Algebra.Vec3.dot,
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
    InfoGeometry.Canonical.ZornMatrix.dot]

theorem paperNorm_eq_canonicalDet_of_signal
    (c : ℝ) (s : InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.SignalCoordinates) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        (paperCanonicalLinearEquiv
          (InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.toNativeZorn c s)) =
      InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.signalNorm c s := by
  rw [← paperCanonicalLinearEquiv_norm,
    InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge.native_zorn_norm_eq_signalNorm]

end InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge
