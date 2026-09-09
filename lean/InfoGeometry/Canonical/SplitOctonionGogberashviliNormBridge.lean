import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Algebra.ZornVectorMatrix
import Mathlib.Tactic

/-!
# Split-octonion signal coordinates and the native Zorn norm

This owner formalizes the norm formula used in the split-octonion signal
coordinates of arXiv:1506.01012.  The embedding is into the repository's
native `InfoGeometry.Algebra.ZornMatrix` carrier; no second octonion carrier,
`G₂` action, or particle-physics interpretation is introduced.
-/

namespace InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge

noncomputable section

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix

/-- The four-coordinate packet used in the split-octonion signal ansatz. -/
structure SignalCoordinates where
  omega : ℝ
  lambda : Fin 3 → ℝ
  position : Fin 3 → ℝ
  time : ℝ

/-- Native Zorn realization with `a = ω + ct`, `b = ω - ct`,
and chiral vector slots `v = λ-x`, `w = λ+x`. -/
def toNativeZorn (c : ℝ) (s : SignalCoordinates) : ZornMatrix ℝ where
  a := s.omega + c * s.time
  v := Vec3.sub s.lambda s.position
  w := Vec3.add s.lambda s.position
  b := s.omega - c * s.time

/-- The split signature polynomial from equation (9) of the paper. -/
def signalNorm (c : ℝ) (s : SignalCoordinates) : ℝ :=
  s.omega ^ 2 - (s.lambda 0 ^ 2 + s.lambda 1 ^ 2 + s.lambda 2 ^ 2) +
    (s.position 0 ^ 2 + s.position 1 ^ 2 + s.position 2 ^ 2) -
    c ^ 2 * s.time ^ 2

/-! Direct realization in the linear native carrier used by the derivation
API.  This does not alter the older non-associative coordinate carrier. -/
def toNativeVectorZorn (c : ℝ) (s : SignalCoordinates) :
    InfoGeometry.Algebra.ZornVectorMatrix ℝ where
  a := s.omega + c * s.time
  v := fun i => s.lambda i - s.position i
  w := fun i => s.lambda i + s.position i
  b := s.omega - c * s.time

theorem native_vector_zorn_norm_eq_signalNorm (c : ℝ) (s : SignalCoordinates) :
    InfoGeometry.Algebra.ZornVectorMatrix.norm (toNativeVectorZorn c s) =
      signalNorm c s := by
    simp [toNativeVectorZorn, signalNorm,
      InfoGeometry.Algebra.ZornVectorMatrix.norm,
      InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three]
    ring

theorem native_zorn_norm_eq_signalNorm (c : ℝ) (s : SignalCoordinates) :
    zornNorm (toNativeZorn c s) = signalNorm c s := by
  simp [toNativeZorn, signalNorm, zornNorm, Vec3.dot, Vec3.add, Vec3.sub,
    Fin.sum_univ_three]
  ring

def IsZeroNorm (c : ℝ) (s : SignalCoordinates) : Prop :=
  signalNorm c s = 0

theorem isZeroNorm_iff_native_vector_zorn_norm_zero (c : ℝ) (s : SignalCoordinates) :
    IsZeroNorm c s ↔
      InfoGeometry.Algebra.ZornVectorMatrix.norm (toNativeVectorZorn c s) = 0 := by
  rw [IsZeroNorm, native_vector_zorn_norm_eq_signalNorm]

theorem isZeroNorm_iff_native_zorn_norm_zero (c : ℝ) (s : SignalCoordinates) :
    IsZeroNorm c s ↔ zornNorm (toNativeZorn c s) = 0 := by
  rw [IsZeroNorm, native_zorn_norm_eq_signalNorm]

end
end InfoGeometry.Canonical.SplitOctonionGogberashviliNormBridge
