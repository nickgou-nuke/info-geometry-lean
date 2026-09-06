import InfoGeometry.Optics.Cl11SplitQuaternionConjugationSoldering
import InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

set_option autoImplicit false

/-!
# `Cl(1,1)` inside quaternionic split-octonion conjugation

This module closes the compatibility square between the existing native
fixed-colour `Cl(1,1)` packet, the canonical Zorn carrier, and its quaternionic
`(4+4)` coordinates.  No new multiplication is introduced.
-/

noncomputable section

namespace InfoGeometry.Optics.Cl11QuaternionTwistedConjugationBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Clifford.Cl11CoordinateAlgebra
open InfoGeometry.Canonical.SplitOctonionFixedColorCl11Bridge
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation
open InfoGeometry.Optics.Cl11SplitQuaternionConjugationSoldering
open InfoGeometry.Optics.Cl11SplitQuaternionQGTSoldering

/-- Coordinate-preserving passage from the older native Zorn carrier to the
canonical Zorn owner, factored through the existing vector-matrix bridge. -/
def nativeToCanonical (X : Native) :
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.CZ :=
  canonicalVectorEquiv.symm (toVectorMatrix X)

theorem nativeToCanonical_injective : Function.Injective nativeToCanonical := by
  intro X Y h
  apply toVectorMatrix_injective
  exact canonicalVectorEquiv.symm.injective h

@[simp] theorem nativeToCanonical_add (X Y : Native) :
    nativeToCanonical (X + Y) = nativeToCanonical X + nativeToCanonical Y := by
  apply canonicalVectorEquiv.injective
  rw [canonicalVectorEquiv_add]
  simp only [nativeToCanonical, Equiv.apply_symm_apply]
  apply InfoGeometry.Algebra.ZornVectorMatrix.ext
  · rfl
  · funext j
    fin_cases j <;> rfl
  · funext j
    fin_cases j <;> rfl
  · rfl

@[simp] theorem nativeToCanonical_nativeConjugate (X : Native) :
    nativeToCanonical (nativeConjugate X) =
      canonicalConj (nativeToCanonical X) := by
  apply canonicalVectorEquiv.injective
  simp [nativeToCanonical, canonicalConj]

@[simp] theorem nativeToCanonical_mul (X Y : Native) :
    nativeToCanonical (X * Y) = nativeToCanonical X * nativeToCanonical Y := by
  apply canonicalVectorEquiv.injective
  rw [canonicalVectorEquiv_mul]
  simp only [nativeToCanonical, Equiv.apply_symm_apply]
  exact toVectorMatrix_mul X Y

/-- The canonical determinant is the older native Zorn norm under the
coordinate-preserving bridge. -/
@[simp] theorem detZ_nativeToCanonical (X : Native) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (nativeToCanonical X) =
    InfoGeometry.Algebra.ZornMatrix.zornNorm X := by
    simp [nativeToCanonical, canonicalVectorEquiv, toVectorMatrix,
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
    InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3,
    InfoGeometry.Algebra.ZornMatrix.zornNorm,
    InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3,
    InfoGeometry.Canonical.ZornMatrix.dot,
    InfoGeometry.Algebra.Vec3.dot]

/-- A fixed-colour associative `Cl(1,1)` packet expressed in the global
quaternionic `(4+4)` coordinates of the split-octonion carrier. -/
def cl11Cartesian (i : Fin 3) (q : Cl11) : CartesianCoordinates :=
  cartesianZornLinearEquiv.symm
    (nativeToCanonical (cl11FixedColorSplitOctonion i q))

@[simp] theorem cl11_add_s (q r : Cl11) : (q + r).s = q.s + r.s := rfl
@[simp] theorem cl11_add_e1 (q r : Cl11) : (q + r).e1 = q.e1 + r.e1 := rfl
@[simp] theorem cl11_add_e2 (q r : Cl11) : (q + r).e2 = q.e2 + r.e2 := rfl
@[simp] theorem cl11_add_e12 (q r : Cl11) : (q + r).e12 = q.e12 + r.e12 := rfl

theorem cl11SplitQuaternionMatrix_add (q r : Cl11) :
    cl11SplitQuaternionMatrix (q + r) =
      cl11SplitQuaternionMatrix q + cl11SplitQuaternionMatrix r := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [cl11SplitQuaternionMatrix,
      InfoGeometry.Algebra.SplitQuaternionMatrices.splitQ_eq_matrix] <;>
    ring

theorem cl11FixedColorSplitOctonion_add (i : Fin 3) (q r : Cl11) :
    cl11FixedColorSplitOctonion i (q + r) =
      cl11FixedColorSplitOctonion i q + cl11FixedColorSplitOctonion i r := by
  unfold cl11FixedColorSplitOctonion
  rw [cl11SplitQuaternionMatrix_add,
    fixedColorReadout_add]

@[simp] theorem cartesianZorn_cl11Cartesian (i : Fin 3) (q : Cl11) :
    cartesianZornLinearEquiv (cl11Cartesian i q) =
      nativeToCanonical (cl11FixedColorSplitOctonion i q) := by
  exact cartesianZornLinearEquiv.apply_symm_apply _

@[simp] theorem cl11Cartesian_add (i : Fin 3) (q r : Cl11) :
    cl11Cartesian i (q + r) = cl11Cartesian i q + cl11Cartesian i r := by
  apply cartesianZornLinearEquiv.injective
  rw [map_add]
  simp only [cartesianZorn_cl11Cartesian]
  rw [cl11FixedColorSplitOctonion_add, nativeToCanonical_add]

/-- On every fixed-colour associative plane, the global split-octonion
twisted conjugation restricts exactly to `Cl(1,1)` Clifford conjugation. -/
theorem cartesianTwistedConj_cl11Cartesian (i : Fin 3) (q : Cl11) :
    cartesianTwistedConj (cl11Cartesian i q) =
      cl11Cartesian i (cliffordConjugate q) := by
  apply cartesianZornLinearEquiv.injective
  rw [cartesianZorn_intertwines_twistedConj]
  simp only [cartesianZorn_cl11Cartesian]
  rw [← nativeToCanonical_nativeConjugate,
    nativeConjugate_cl11FixedColorSplitOctonion]

/-- The global `(4,4)` form restricts to the split-quaternion `(2,2)` norm on
each fixed-colour `Cl(1,1)` plane. -/
theorem normDifference_cl11Cartesian (i : Fin 3) (q : Cl11) :
    quaternionNorm (cl11Cartesian i q).1 -
        quaternionNorm (cl11Cartesian i q).2 = splitNorm q := by
  calc
    quaternionNorm (cl11Cartesian i q).1 -
          quaternionNorm (cl11Cartesian i q).2 =
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
          InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
          (cartesianZornLinearEquiv (cl11Cartesian i q)) :=
      (detZ_cartesianZornLinearEquiv (cl11Cartesian i q)).symm
    _ = InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
          InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
          (nativeToCanonical (cl11FixedColorSplitOctonion i q)) := by
      rw [cartesianZorn_cl11Cartesian]
    _ = InfoGeometry.Algebra.ZornMatrix.zornNorm
          (cl11FixedColorSplitOctonion i q) :=
      detZ_nativeToCanonical _
    _ = splitNorm q := zornNorm_cl11FixedColorSplitOctonion i q

/-- Polarization of the global difference-of-quaternion-norm form. -/
def cartesianNormPolar (X Y : CartesianCoordinates) : ℝ :=
  (quaternionNorm (X + Y).1 - quaternionNorm (X + Y).2) -
    (quaternionNorm X.1 - quaternionNorm X.2) -
      (quaternionNorm Y.1 - quaternionNorm Y.2)

/-- The polarized global `(4,4)` form restricts to twice the native
`Cl(1,1)` Krein bilinear form, matching the unnormalized polarization
convention. -/
theorem cartesianNormPolar_cl11Cartesian
    (i : Fin 3) (q r : Cl11) :
    cartesianNormPolar (cl11Cartesian i q) (cl11Cartesian i r) =
      2 * kreinMetric q r := by
  unfold cartesianNormPolar
  rw [← cl11Cartesian_add,
    normDifference_cl11Cartesian,
    normDifference_cl11Cartesian,
    normDifference_cl11Cartesian]
  simp [splitNorm, kreinMetric]
  ring

/-- Conjugation and quadratic-form restriction in one reusable packet. -/
theorem cl11_twistedConjugation_norm_packet (i : Fin 3) (q : Cl11) :
    cartesianTwistedConj (cl11Cartesian i q) =
        cl11Cartesian i (cliffordConjugate q) ∧
      quaternionNorm (cl11Cartesian i q).1 -
          quaternionNorm (cl11Cartesian i q).2 = splitNorm q := by
  exact ⟨cartesianTwistedConj_cl11Cartesian i q,
    normDifference_cl11Cartesian i q⟩

/-- Two-vector metric packet: the involution, quadratic form, and polarized
bilinear form all restrict coherently to the same fixed-colour `Cl(1,1)`
plane. -/
theorem cl11_twistedConjugation_metric_packet
    (i : Fin 3) (q r : Cl11) :
    cartesianTwistedConj (cl11Cartesian i q) =
        cl11Cartesian i (cliffordConjugate q) ∧
      cartesianTwistedConj (cl11Cartesian i r) =
        cl11Cartesian i (cliffordConjugate r) ∧
      quaternionNorm (cl11Cartesian i q).1 -
          quaternionNorm (cl11Cartesian i q).2 = splitNorm q ∧
      cartesianNormPolar (cl11Cartesian i q) (cl11Cartesian i r) =
        2 * kreinMetric q r := by
  exact ⟨cartesianTwistedConj_cl11Cartesian i q,
    cartesianTwistedConj_cl11Cartesian i r,
    normDifference_cl11Cartesian i q,
    cartesianNormPolar_cl11Cartesian i q r⟩

end InfoGeometry.Optics.Cl11QuaternionTwistedConjugationBridge
