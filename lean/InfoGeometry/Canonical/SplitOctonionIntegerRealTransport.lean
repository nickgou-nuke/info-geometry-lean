import InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge
import InfoGeometry.OperatorAlgebra.SplitOctonionG2TypeGenerators

/-!
# Integer split-octonion coordinates inside the real Paper-Zorn carrier

The explicit multiplication owner is integral, while the canonical Zorn
owners are real.  This file supplies the honest coordinate-casting embedding
between those carriers.  It is an embedding, not an equivalence: integral
coordinates do not exhaust the real carrier.
-/

namespace InfoGeometry.Canonical.SplitOctonionIntegerRealTransport

open InfoGeometry.Algebra
open InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.G2TypeGenerators

abbrev PaperZorn := InfoGeometry.Algebra.ZornMatrix ℝ
abbrev CanonicalZorn :=
  InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge.CanonicalZorn

def cast : SplitOct → PaperZorn := fun X =>
  { a := X.a
    v := ![(X.x0 : ℝ), (X.x1 : ℝ), (X.x2 : ℝ)]
    w := ![(X.y0 : ℝ), (X.y1 : ℝ), (X.y2 : ℝ)]
    b := X.b }

theorem cast_injective : Function.Injective cast := by
  intro X Y h
  have ha : (X.a : ℝ) = (Y.a : ℝ) := by
    simpa [cast] using congrArg (fun Z : PaperZorn => Z.a) h
  have hb : (X.b : ℝ) = (Y.b : ℝ) := by
    simpa [cast] using congrArg (fun Z : PaperZorn => Z.b) h
  have hx0 : (X.x0 : ℝ) = (Y.x0 : ℝ) := by
    simpa [cast] using congrArg (fun Z : PaperZorn => Z.v 0) h
  have hx1 : (X.x1 : ℝ) = (Y.x1 : ℝ) := by
    simpa [cast] using congrArg (fun Z : PaperZorn => Z.v 1) h
  have hx2 : (X.x2 : ℝ) = (Y.x2 : ℝ) := by
    simpa [cast] using congrArg (fun Z : PaperZorn => Z.v 2) h
  have hy0 : (X.y0 : ℝ) = (Y.y0 : ℝ) := by
    simpa [cast] using congrArg (fun Z : PaperZorn => Z.w 0) h
  have hy1 : (X.y1 : ℝ) = (Y.y1 : ℝ) := by
    simpa [cast] using congrArg (fun Z : PaperZorn => Z.w 1) h
  have hy2 : (X.y2 : ℝ) = (Y.y2 : ℝ) := by
    simpa [cast] using congrArg (fun Z : PaperZorn => Z.w 2) h
  apply SplitOct.ext
  · exact_mod_cast ha
  · exact_mod_cast hb
  · exact_mod_cast hx0
  · exact_mod_cast hx1
  · exact_mod_cast hx2
  · exact_mod_cast hy0
  · exact_mod_cast hy1
  · exact_mod_cast hy2

theorem cast_zero : cast (0 : SplitOct) = (0 : PaperZorn) := by
  ext <;> simp [cast, InfoGeometry.Algebra.ZornMatrix.zero]

theorem cast_add (X Y : SplitOct) : cast (X + Y) = cast X + cast Y := by
  cases X
  cases Y
  ext <;>
    simp [cast, InfoGeometry.Algebra.ZornMatrix.add,
      InfoGeometry.Algebra.Vec3.add]

theorem cast_mul (X Y : SplitOct) :
    cast (mulZ X Y) = cast X * cast Y := by
  cases X
  cases Y
  apply InfoGeometry.Algebra.ZornMatrix.ext
  · simp [cast, mulZ, InfoGeometry.Algebra.ZornMatrix.mul,
      InfoGeometry.Algebra.Vec3.dot]
  · funext i
    fin_cases i <;>
      simp [cast, mulZ, InfoGeometry.Algebra.ZornMatrix.mul,
        InfoGeometry.Algebra.Vec3.add, InfoGeometry.Algebra.Vec3.sub,
        InfoGeometry.Algebra.Vec3.smul, InfoGeometry.Algebra.Vec3.cross]
    all_goals ring
  · funext i
    fin_cases i <;>
      simp [cast, mulZ, InfoGeometry.Algebra.ZornMatrix.mul,
        InfoGeometry.Algebra.Vec3.add, InfoGeometry.Algebra.Vec3.smul,
        InfoGeometry.Algebra.Vec3.cross]
    all_goals ring
  · simp [cast, mulZ, InfoGeometry.Algebra.ZornMatrix.mul,
      InfoGeometry.Algebra.Vec3.dot]
    ring

theorem cast_tau :
    cast (tau X) =
      { a := (cast X).a
        v := ![(cast X).v 0, -(cast X).v 1, -(cast X).v 2]
        w := ![(cast X).w 0, -(cast X).w 1, -(cast X).w 2]
        b := (cast X).b } := by
  cases X
  ext <;> simp [cast, tau]

theorem cast_tau_mul (X Y : SplitOct) :
    cast (tau (mulZ X Y)) = cast (tau X) * cast (tau Y) := by
  rw [tau_mulZ, cast_mul]

noncomputable def canonicalCast (X : SplitOct) : CanonicalZorn :=
  paperCanonicalLinearEquiv (cast X)

theorem canonicalCast_mul (X Y : SplitOct) :
    canonicalCast (mulZ X Y) = canonicalCast X * canonicalCast Y := by
  unfold canonicalCast
  rw [cast_mul, paperCanonicalLinearEquiv_mul]

theorem canonicalCast_tau (X : SplitOct) :
    canonicalCast (tau X) =
      paperCanonicalLinearEquiv
        { a := (cast X).a
          v := ![(cast X).v 0, -(cast X).v 1, -(cast X).v 2]
          w := ![(cast X).w 0, -(cast X).w 1, -(cast X).w 2]
          b := (cast X).b } := by
  unfold canonicalCast
  rw [cast_tau]

theorem canonicalCast_injective : Function.Injective canonicalCast := by
  intro X Y h
  apply cast_injective
  apply paperCanonicalLinearEquiv.injective
  exact h

end InfoGeometry.Canonical.SplitOctonionIntegerRealTransport
