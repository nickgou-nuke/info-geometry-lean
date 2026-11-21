/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.H3ZornExplicitPeirceJordanSoldering
import InfoGeometry.Canonical.H3ZornSolderingDerivationTransport
import InfoGeometry.Canonical.G2H3ZornCoordinateSolderingClosure
import InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge

noncomputable section

namespace InfoGeometry.Canonical.H3ZornExplicitPeirceG2Leibniz

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding
open InfoGeometry.Canonical.H3ZornAlgebraicSoldering
open InfoGeometry.Canonical.H3ZornExplicitPeirceJordanSoldering
open InfoGeometry.Canonical.H3ZornSolderingDerivationTransport
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge

abbrev Zorn := InfoGeometry.Algebra.ZornVectorMatrix ℝ
abbrev VDer := InfoGeometry.Algebra.ZornVectorMatrix.Derivation (R := ℝ)

noncomputable def vectorDerivation (D : G2Derivation) : VDer :=
  canonicalToVectorDerivation D

theorem zornPair_derivation_skew (D : G2Derivation) (x y : Zorn) :
    zornPair (vectorDerivation D x) y +
      zornPair x (vectorDerivation D y) = 0 := by
  let p : Params := derivationParameters (vectorDerivation D)
  have hp : parameterDerivation p = vectorDerivation D :=
    parameterLinearEquiv.right_inv _
  have h := derivation_native_parameter_polar_skew p x y
  rw [hp] at h
  change ZornVectorMatrix.trace (ZornVectorMatrix.mul
      (vectorDerivation D x) (ZornVectorMatrix.conj y)) +
    ZornVectorMatrix.trace (ZornVectorMatrix.mul x
      (ZornVectorMatrix.conj (vectorDerivation D y))) = 0
  simpa [vectorNativeWittPairing, zornPair,
    ZornVectorMatrix.trace_mul_comm] using h

theorem vectorDerivation_trace_zero (D : G2Derivation) (x : Zorn) :
    ZornVectorMatrix.trace (vectorDerivation D x) = 0 := by
  have h := zornPair_derivation_skew D x (ZornVectorMatrix.one : Zorn)
  have hone := (vectorDerivation D).map_one
  rw [hone] at h
  simpa [zornPair, ZornVectorMatrix.one, ZornVectorMatrix.conj,
    ZornVectorMatrix.mul, ZornVectorMatrix.trace, ZornVec3.dot] using h

theorem conj_vectorDerivation_eq_neg (D : G2Derivation) (x : Zorn) :
    ZornVectorMatrix.conj (vectorDerivation D x) =
      ZornVectorMatrix.neg (vectorDerivation D x) := by
  rw [ZornVectorMatrix.conj_eq_scalar_trace_sub,
    vectorDerivation_trace_zero D x]
  ext i <;> simp [ZornVectorMatrix.scalar, ZornVectorMatrix.sub,
    ZornVectorMatrix.add, ZornVectorMatrix.neg]

theorem vectorDerivation_map_conj (D : G2Derivation) (x : Zorn) :
    vectorDerivation D (ZornVectorMatrix.conj x) =
      ZornVectorMatrix.conj (vectorDerivation D x) := by
  rw [ZornVectorMatrix.Derivation.map_conj_eq_neg,
    conj_vectorDerivation_eq_neg]

@[simp] theorem coordLiftG2_explicit (D : G2Derivation) (X : H3Coord) :
    coordLiftG2 D X = ((0, (0, 0)),
      (vectorDerivation D X.2.1,
        (vectorDerivation D X.2.2.1, vectorDerivation D X.2.2.2))) := by
  rcases X with ⟨⟨x1, x2, x3⟩, ⟨a, b, c⟩⟩
  rfl

theorem coordinateJordanLeibniz_explicit (D : G2Derivation)
    (hD : CoordinateJordanLeibniz D) (X Y : H3Coord) :
    coordLiftG2 D (coordJordanMulExplicit X Y) =
      coordJordanMulExplicit (coordLiftG2 D X) Y +
        coordJordanMulExplicit X (coordLiftG2 D Y) := by
  exact hD X Y

theorem coordinateJordanLeibniz_all (D : G2Derivation)
    (hD : CoordinateJordanLeibniz D) :
    CoordinateJordanLeibniz D := by
  intro X Y
  exact hD X Y

theorem full_g2_f4_compatibility
    (hcoord : ∀ D : G2Derivation, CoordinateJordanLeibniz D) :
    FullEntrywiseG2F4Compatibility := by
  exact full_g2_f4_compatibility_of_coordinate
    (fun D => coordinateJordanLeibniz_all D (hcoord D))

/-- Equivalent concrete closure statement: the compatible subalgebra is all
of the native 14-dimensional split G2 derivation algebra. -/
theorem entrywiseCompatibleG2_eq_top :
    entrywiseCompatibleG2 = ⊤ := by
  exact InfoGeometry.Canonical.G2H3ZornCoordinateSolderingClosure.entrywiseCompatibleG2_eq_top

/-- The full entrywise G2 action therefore lands in the native F4 derivation
Lie algebra, with no compatibility subtype restriction remaining. -/
noncomputable def g2ToF4LieHom :
    G2Derivation →ₗ⁅ℝ⁆ H3ZornF4Derivations :=
  InfoGeometry.Canonical.G2H3ZornCoordinateSolderingClosure.fullG2ToF4LieHom

/-- The full G2-to-F4 Lie homomorphism is faithful. -/
theorem g2ToF4LieHom_injective : Function.Injective g2ToF4LieHom := by
  exact InfoGeometry.Canonical.G2H3ZornCoordinateSolderingClosure.fullG2ToF4LieHom_injective

end InfoGeometry.Canonical.H3ZornExplicitPeirceG2Leibniz
