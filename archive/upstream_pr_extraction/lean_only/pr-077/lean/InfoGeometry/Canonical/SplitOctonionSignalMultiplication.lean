import InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge

/-!
# Pullback multiplication on split-octonion signal coordinates

For a nonzero speed parameter `c`, the signal-coordinate realization is an
actual coordinate equivalence with the native Zorn carrier.  Multiplication
on signal coordinates is therefore pulled back from native Zorn multiplication.
-/

namespace InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix

noncomputable section

theorem signalCoordinates_ext {s t : SignalCoordinates}
    (hω : s.omega = t.omega) (hlam : s.lambda = t.lambda)
    (hx : s.position = t.position) (ht : s.time = t.time) : s = t := by
  cases s
  cases t
  simp_all

def fromNativeZorn (c : ℝ) (hc : c ≠ 0) (X : ZornMatrix ℝ) : SignalCoordinates where
  omega := (X.a + X.b) / 2
  lambda := fun i => (X.v i + X.w i) / 2
  position := fun i => (X.w i - X.v i) / 2
  time := (X.a - X.b) / (2 * c)

theorem fromNativeZorn_toNativeZorn (c : ℝ) (hc : c ≠ 0)
    (s : SignalCoordinates) :
    fromNativeZorn c hc (toNativeZorn c s) = s := by
  cases s with
  | mk omega lambda position time =>
    apply signalCoordinates_ext
    · simp [fromNativeZorn, toNativeZorn]
    · funext i
      fin_cases i <;> simp [fromNativeZorn, toNativeZorn, Vec3.add, Vec3.sub]
    · funext i
      fin_cases i <;> simp [fromNativeZorn, toNativeZorn, Vec3.add, Vec3.sub]
    · simp [fromNativeZorn, toNativeZorn]
      field_simp [hc]
      ring

theorem toNativeZorn_fromNativeZorn (c : ℝ) (hc : c ≠ 0)
    (X : ZornMatrix ℝ) :
    toNativeZorn c (fromNativeZorn c hc X) = X := by
  apply ZornMatrix.ext
  · simp [toNativeZorn, fromNativeZorn]
    field_simp [hc]
    ring
  · funext i
    fin_cases i <;> simp [toNativeZorn, fromNativeZorn, Vec3.sub] <;> ring
  · funext i
    fin_cases i <;> simp [toNativeZorn, fromNativeZorn, Vec3.add] <;> ring
  · simp [toNativeZorn, fromNativeZorn]
    field_simp [hc]
    ring

noncomputable def signalToZornEquiv (c : ℝ) (hc : c ≠ 0) :
    SignalCoordinates ≃ ZornMatrix ℝ where
  toFun := toNativeZorn c
  invFun := fromNativeZorn c hc
  left_inv := fromNativeZorn_toNativeZorn c hc
  right_inv := toNativeZorn_fromNativeZorn c hc

def signalMul (c : ℝ) (hc : c ≠ 0)
    (s t : SignalCoordinates) : SignalCoordinates :=
  (signalToZornEquiv c hc).symm
    ((signalToZornEquiv c hc s) * (signalToZornEquiv c hc t))

def signalConj (s : SignalCoordinates) : SignalCoordinates where
  omega := s.omega
  lambda := fun i => -s.lambda i
  position := fun i => -s.position i
  time := -s.time

def signalNativeConj (X : ZornMatrix ℝ) : ZornMatrix ℝ where
  a := X.b
  v := fun i => -X.v i
  w := fun i => -X.w i
  b := X.a

theorem signalNativeConj_add (X Y : ZornMatrix ℝ) :
    signalNativeConj (X + Y) = signalNativeConj X + signalNativeConj Y := by
  apply ZornMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> simp [signalNativeConj, ZornMatrix.add, Vec3.add] <;> ring
  · funext i
    fin_cases i <;> simp [signalNativeConj, ZornMatrix.add, Vec3.add] <;> ring
  · rfl

theorem signalNativeConj_smul (r : ℝ) (X : ZornMatrix ℝ) :
    signalNativeConj (r • X) = r • signalNativeConj X := by
  apply ZornMatrix.ext
  · simp [signalNativeConj, ZornMatrix.smul]
  · funext i
    fin_cases i <;> simp [signalNativeConj, ZornMatrix.smul, Vec3.smul]
  · funext i
    fin_cases i <;> simp [signalNativeConj, ZornMatrix.smul, Vec3.smul]
  · simp [signalNativeConj, ZornMatrix.smul]

theorem signalNativeConj_norm (X : ZornMatrix ℝ) :
    zornNorm (signalNativeConj X) = zornNorm X := by
  simp [signalNativeConj, zornNorm, Vec3.dot]
  ring

theorem signalNativeConj_mul (X Y : ZornMatrix ℝ) :
    signalNativeConj (X * Y) = signalNativeConj Y * signalNativeConj X := by
  apply ZornMatrix.ext
  · simp [signalNativeConj, ZornMatrix.mul, Vec3.dot]
    ring
  · funext i
    fin_cases i <;>
      simp [signalNativeConj, ZornMatrix.mul, Vec3.dot, Vec3.cross,
        Vec3.add, Vec3.sub, Vec3.smul] <;>
      ring
  · funext i
    fin_cases i <;>
      simp [signalNativeConj, ZornMatrix.mul, Vec3.dot, Vec3.cross,
        Vec3.add, Vec3.sub, Vec3.smul] <;>
      ring
  · simp [signalNativeConj, ZornMatrix.mul, Vec3.dot]
    ring

theorem toNativeZorn_signalConj (c : ℝ) (s : SignalCoordinates) :
    toNativeZorn c (signalConj s) =
      signalNativeConj (toNativeZorn c s) := by
  apply ZornMatrix.ext
  · simp [toNativeZorn, signalConj, signalNativeConj]
    ring
  · funext i
    fin_cases i <;>
      simp [toNativeZorn, signalConj, signalNativeConj, Vec3.sub, Vec3.add] <;>
      ring
  · funext i
    fin_cases i <;>
      simp [toNativeZorn, signalConj, signalNativeConj, Vec3.sub, Vec3.add] <;>
      ring
  · simp [toNativeZorn, signalConj, signalNativeConj]

theorem signalNativeConj_involutive (X : ZornMatrix ℝ) :
    signalNativeConj (signalNativeConj X) = X := by
  apply ZornMatrix.ext
  · rfl
  · funext i
    simp [signalNativeConj]
  · funext i
    simp [signalNativeConj]
  · rfl

theorem signalConj_involutive (s : SignalCoordinates) :
    signalConj (signalConj s) = s := by
  apply signalCoordinates_ext
  · rfl
  · funext i
    simp [signalConj]
  · funext i
    simp [signalConj]
  · simp [signalConj]

theorem signalNorm_signalConj (c : ℝ) (s : SignalCoordinates) :
    signalNorm c (signalConj s) = signalNorm c s := by
  simp [signalNorm, signalConj]

theorem signalZeroNorm_conj_iff (c : ℝ) (s : SignalCoordinates) :
    IsZeroNorm c (signalConj s) ↔ IsZeroNorm c s := by
  simp [IsZeroNorm, signalNorm_signalConj]

theorem toNativeZorn_signalMul (c : ℝ) (hc : c ≠ 0)
    (s t : SignalCoordinates) :
    toNativeZorn c (signalMul c hc s t) =
      toNativeZorn c s * toNativeZorn c t := by
  exact (signalToZornEquiv c hc).apply_symm_apply _

theorem signalConj_signalMul (c : ℝ) (hc : c ≠ 0)
    (s t : SignalCoordinates) :
    signalConj (signalMul c hc s t) =
      signalMul c hc (signalConj t) (signalConj s) := by
  apply (signalToZornEquiv c hc).injective
  change toNativeZorn c (signalConj (signalMul c hc s t)) =
    toNativeZorn c (signalMul c hc (signalConj t) (signalConj s))
  rw [toNativeZorn_signalConj, toNativeZorn_signalMul,
    toNativeZorn_signalMul, toNativeZorn_signalConj,
    toNativeZorn_signalConj, signalNativeConj_mul]

theorem signalNorm_signalMul (c : ℝ) (hc : c ≠ 0)
    (s t : SignalCoordinates) :
    signalNorm c (signalMul c hc s t) =
      signalNorm c s * signalNorm c t := by
  rw [← native_zorn_norm_eq_signalNorm,
    ← native_zorn_norm_eq_signalNorm,
    ← native_zorn_norm_eq_signalNorm]
  rw [toNativeZorn_signalMul, zornNorm_mul]

end
end InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge
