import InfoGeometry.Lie.SplitOctonionImaginaryAction
import InfoGeometry.Algebra.Zorn.Incidence
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Native Erlangen invariant for the split-Cayley null locus

The split-Cayley automorphism action preserves the imaginary square-zero locus.
This is derived from the native determinant/null-cone and quadratic identities;
no group-identification theorem is introduced here.
-/

namespace InfoGeometry.Lie.SplitOctonionErlangenInvariant

open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

noncomputable def canonicalDetQuadratic :
    QuadraticForm ℝ
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn :=
  QuadraticMap.ofPolar
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
    (by
      intro r X
      have ha : (r • X).a = r * X.a := by
        rw [Equiv.smul_def InfoGeometry.Canonical.ZornMatrix.coordEquiv]
        rfl
      have hb : (r • X).b = r * X.b := by
        rw [Equiv.smul_def InfoGeometry.Canonical.ZornMatrix.coordEquiv]
        rfl
      have hx (i : Fin 3) : (r • X).x i = r * X.x i := by
        rw [Equiv.smul_def InfoGeometry.Canonical.ZornMatrix.coordEquiv]
        rfl
      have hy (i : Fin 3) : (r • X).y i = r * X.y i := by
        rw [Equiv.smul_def InfoGeometry.Canonical.ZornMatrix.coordEquiv]
        rfl
      simp [InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
        InfoGeometry.Canonical.ZornMatrix.dot, ha, hb, hx, hy]
      ring)
    (by
      intro X Y Z
      simp [QuadraticMap.polar, InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
        InfoGeometry.Canonical.ZornMatrix.dot]
      ring)
    (by
      intro r X Y
      have ha : (r • X).a = r * X.a := by
        rw [Equiv.smul_def InfoGeometry.Canonical.ZornMatrix.coordEquiv]
        rfl
      have hb : (r • X).b = r * X.b := by
        rw [Equiv.smul_def InfoGeometry.Canonical.ZornMatrix.coordEquiv]
        rfl
      have hx (i : Fin 3) : (r • X).x i = r * X.x i := by
        rw [Equiv.smul_def InfoGeometry.Canonical.ZornMatrix.coordEquiv]
        rfl
      have hy (i : Fin 3) : (r • X).y i = r * X.y i := by
        rw [Equiv.smul_def InfoGeometry.Canonical.ZornMatrix.coordEquiv]
        rfl
      simp [QuadraticMap.polar, InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
        InfoGeometry.Canonical.ZornMatrix.dot, ha, hb, hx, hy,
        smul_eq_mul]
      ring)

theorem realZornCompositionAut_preserves_polar
    (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut)
    (X Y : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn) :
    polarZ ((φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) X)
        ((φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) Y) =
      polarZ X Y := by
  unfold polarZ
  rw [← map_add (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut)
      X Y,
    InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_preserves_det,
    InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_preserves_det,
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_preserves_det]

noncomputable def realZornCompositionAut_quadratic_isometry
    (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut) :
    canonicalDetQuadratic.IsometryEquiv canonicalDetQuadratic :=
  { (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) with
    map_app' := fun X =>
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_preserves_det φ X }

@[simp] theorem realZornCompositionAut_quadratic_map_app
    (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut)
    (X : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn) :
    canonicalDetQuadratic
        ((φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) X) =
      canonicalDetQuadratic X := by
  exact QuadraticMap.IsometryEquiv.map_app
    (realZornCompositionAut_quadratic_isometry φ) X

theorem realZornCompositionAut_preserves_incident
    (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut)
    (X Y : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn) :
    IncidentRep
        ((φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) X)
        ((φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) Y) ↔
      IncidentRep X Y := by
  unfold IncidentRep
  rw [realZornCompositionAut_preserves_polar]

theorem imaginaryAut_preserves_square_zero
    (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut)
    (X : Imaginary) :
    zMul (imaginaryAut φ X).1 (imaginaryAut φ X).1 = 0 ↔
      zMul X.1 X.1 = 0 := by
  rw [← mem_null_iff_square_zero, ← mem_null_iff_square_zero]
  exact imaginaryAut_preserves_null φ X

theorem imaginaryAut_preserves_polar
    (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut)
    (X Y : Imaginary) :
    polarZ (imaginaryAut φ X).1 (imaginaryAut φ Y).1 = polarZ X.1 Y.1 := by
  unfold polarZ
  calc
    _ = ZornMatrix.detZ
          ((φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) X.1 +
            (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) Y.1) -
        ZornMatrix.detZ ((φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) X.1) -
          ZornMatrix.detZ ((φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) Y.1) := by
      rfl
    _ = ZornMatrix.detZ
          ((φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut)
            (X.1 + Y.1)) -
        ZornMatrix.detZ ((φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) X.1) -
          ZornMatrix.detZ ((φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) Y.1) := by
      rw [map_add]
    _ = ZornMatrix.detZ (X.1 + Y.1) - ZornMatrix.detZ X.1 - ZornMatrix.detZ Y.1 := by
      rw [InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_preserves_det,
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_preserves_det,
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_preserves_det]

theorem imaginaryAut_preserves_incident
    (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut)
    (X Y : Imaginary) :
    IncidentRep (imaginaryAut φ X).1 (imaginaryAut φ Y).1 ↔
      IncidentRep X.1 Y.1 := by
  unfold IncidentRep
  rw [imaginaryAut_preserves_polar]


end InfoGeometry.Lie.SplitOctonionErlangenInvariant
