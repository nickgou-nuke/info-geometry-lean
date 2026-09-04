import Mathlib
import InfoGeometry.Canonical.H3ZornAlgebraicSolderingTransport
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
import InfoGeometry.Algebra.RealSplitOctZornAlignment

/-!
# Coordinate closure of the algebraic G2 -> H3Zorn soldering

This file keeps the only non-formal calculation at the split-octonion factor
level.  A native split-octonion derivation is transported to the maintained
`RealSplitOct` coordinate carrier, then applied entrywise to the three
Albert off-diagonal slots.  Multiplication, conjugation, and the polarized
trace pairing are transported from the existing Zorn derivation API.

The final H3 Jordan Leibniz theorem is obtained from the algebraic soldering
transport in `H3ZornAlgebraicSolderingTransport`; no 27-coordinate expansion
of the installed H3 product is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.G2H3ZornCoordinateSolderingClosure

open InfoGeometry.Algebra
open InfoGeometry.Algebra.RealSplitOctZornAlignment
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding
open InfoGeometry.Canonical.H3ZornAlgebraicSolderingTransport
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge

abbrev Dv (D : G2Derivation) := canonicalToVectorDerivation D

/-- Every canonical derivation output lies in the conjugation `-1` eigenspace.
This is read directly from the already-proved fourteen-parameter normal form:
the two scalar coordinates of `parameterAction` are exact negatives. -/
theorem vector_output_conj_eq_neg
    (D : G2Derivation) (X : VectorZorn) :
    ZornVectorMatrix.conj (Dv D X) = ZornVectorMatrix.neg (Dv D X) := by
  let d : ZornVectorMatrix.Derivation (R := ℝ) := Dv D
  let p : Params := derivationParameters d
  have hp : parameterDerivation p = d := parameterLinearEquiv.right_inv d
  have hx := congrArg (fun q : ZornVectorMatrix.Derivation (R := ℝ) => q X) hp
  change ZornVectorMatrix.conj (d X) = ZornVectorMatrix.neg (d X)
  rw [← hx]
  apply ZornVectorMatrix.ext
  · simp [parameterDerivation, parameterAction, ZornVectorMatrix.conj,
      ZornVectorMatrix.neg]
  · funext i
    fin_cases i <;>
      simp [parameterDerivation, parameterAction, ZornVectorMatrix.conj,
        ZornVectorMatrix.neg]
  · funext i
    fin_cases i <;>
      simp [parameterDerivation, parameterAction, ZornVectorMatrix.conj,
        ZornVectorMatrix.neg]
  · simp [parameterDerivation, parameterAction, ZornVectorMatrix.conj,
      ZornVectorMatrix.neg]

/-- Hence derivations commute with conjugation on the native Zorn carrier. -/
theorem vector_map_conj
    (D : G2Derivation) (X : VectorZorn) :
    Dv D (ZornVectorMatrix.conj X) =
      ZornVectorMatrix.conj (Dv D X) := by
  rw [ZornVectorMatrix.Derivation.map_conj_eq_neg]
  exact (vector_output_conj_eq_neg D X).symm

/-- Polarized split-octonion pairing skewness for the actual vector-Zorn
realization of a canonical derivation. -/
theorem vector_pair_skew
    (D : G2Derivation) (X Y : VectorZorn) :
    vectorNativeWittPairing (Dv D X) Y +
      vectorNativeWittPairing X (Dv D Y) = 0 := by
  let d : ZornVectorMatrix.Derivation (R := ℝ) := Dv D
  let p : Params := derivationParameters d
  have hp : parameterDerivation p = d := parameterLinearEquiv.right_inv d
  have h := derivation_native_parameter_polar_skew p X Y
  rw [hp] at h
  exact h

/-- The canonical derivation transported to the maintained explicit
`RealSplitOct` coordinate carrier. -/
noncomputable def splitOctEntryEnd (D : G2Derivation) :
    Module.End ℝ RealSplitOct where
  toFun X := fromZorn (Dv D (toZorn X))
  map_add' X Y := by
    rw [toZorn_add, (Dv D).map_add, fromZorn_add]
  map_smul' r X := by
    rw [toZorn_smul, (Dv D).map_smul, fromZorn_smul]

/-- Factor-level Leibniz is just the native Zorn derivation law transported
through the multiplicative split-octonion soldering. -/
theorem splitOctEntryEnd_mul
    (D : G2Derivation) (X Y : RealSplitOct) :
    splitOctEntryEnd D (RealSplitOct.mul X Y) =
      RealSplitOct.mul (splitOctEntryEnd D X) Y +
        RealSplitOct.mul X (splitOctEntryEnd D Y) := by
  change fromZorn (Dv D (toZorn (RealSplitOct.mul X Y))) = _
  rw [toZorn_mul, (Dv D).map_mul', fromZorn_add,
    fromZorn_mul, fromZorn_mul, fromZorn_toZorn, fromZorn_toZorn]

/-- The transported factor derivation commutes with conjugation. -/
theorem splitOctEntryEnd_conj
    (D : G2Derivation) (X : RealSplitOct) :
    splitOctEntryEnd D (RealSplitOct.conj X) =
      RealSplitOct.conj (splitOctEntryEnd D X) := by
  change fromZorn (Dv D (toZorn (RealSplitOct.conj X))) = _
  rw [toZorn_conj, vector_map_conj, fromZorn_conj]

/-- Symmetric scalar pairing appearing in every diagonal Albert readout. -/
def splitOctPair (X Y : RealSplitOct) : ℝ :=
  (RealSplitOct.mul X (RealSplitOct.conj Y)).a +
    (RealSplitOct.mul Y (RealSplitOct.conj X)).a

/-- The explicit symmetric scalar pairing is the native Zorn trace pairing. -/
theorem splitOctPair_eq_native (X Y : RealSplitOct) :
    splitOctPair X Y = vectorNativeWittPairing (toZorn X) (toZorn Y) := by
  simp [splitOctPair, vectorNativeWittPairing, toZorn,
    RealSplitOct.mul, RealSplitOct.conj,
    ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVectorMatrix.conj,
    ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- Infinitesimal invariance of the scalar pairing under every native G2
factor derivation. -/
theorem splitOctPair_skew
    (D : G2Derivation) (X Y : RealSplitOct) :
    splitOctPair (splitOctEntryEnd D X) Y +
      splitOctPair X (splitOctEntryEnd D Y) = 0 := by
  rw [splitOctPair_eq_native, splitOctPair_eq_native]
  change vectorNativeWittPairing
      (toZorn (fromZorn (Dv D (toZorn X)))) (toZorn Y) +
    vectorNativeWittPairing (toZorn X)
      (toZorn (fromZorn (Dv D (toZorn Y)))) = 0
  rw [toZorn_fromZorn, toZorn_fromZorn]
  exact vector_pair_skew D (toZorn X) (toZorn Y)

/-- Entrywise coordinate action on the explicit real Albert carrier. -/
noncomputable def coordinateG2End (D : G2Derivation) :
    Module.End ℝ RealAlbertMatrix where
  toFun X :=
    { α₁ := 0
      α₂ := 0
      α₃ := 0
      z₁ := splitOctEntryEnd D X.z₁
      z₂ := splitOctEntryEnd D X.z₂
      z₃ := splitOctEntryEnd D X.z₃ }
  map_add' X Y := by
    apply RealAlbertMatrix.ext <;> simp [splitOctEntryEnd]
  map_smul' r X := by
    apply RealAlbertMatrix.ext <;> simp [splitOctEntryEnd]

/-- The coordinate entrywise action obeys the Albert Jordan Leibniz rule.
The proof uses only factor multiplication, conjugation, and the polarized
pairing; it does not expand the 27 scalar coordinates. -/
theorem coordinateG2End_is_derivation (D : G2Derivation) :
    CoordinateJordanDerivation (coordinateG2End D) := by
  intro X Y
  apply RealAlbertMatrix.ext
  · change 0 = _
    simp [RealAlbertMatrix.mul, coordinateG2End, splitOctPair]
    have h3 := splitOctPair_skew D X.z₃ Y.z₃
    have h2 := splitOctPair_skew D X.z₂ Y.z₂
    dsimp [splitOctPair] at h3 h2
    linarith
  · change 0 = _
    simp [RealAlbertMatrix.mul, coordinateG2End, splitOctPair]
    have h3 := splitOctPair_skew D X.z₃ Y.z₃
    have h1 := splitOctPair_skew D X.z₁ Y.z₁
    dsimp [splitOctPair] at h3 h1
    linarith
  · change 0 = _
    simp [RealAlbertMatrix.mul, coordinateG2End, splitOctPair]
    have h2 := splitOctPair_skew D X.z₂ Y.z₂
    have h1 := splitOctPair_skew D X.z₁ Y.z₁
    dsimp [splitOctPair] at h2 h1
    linarith
  · change splitOctEntryEnd D (RealAlbertMatrix.mul X Y).z₁ = _
    rw [_root_.rsm_mul_z1]
    simp only [map_add, map_smul, splitOctEntryEnd_mul,
      splitOctEntryEnd_conj]
    simp [RealAlbertMatrix.mul, coordinateG2End]
    module
  · change splitOctEntryEnd D (RealAlbertMatrix.mul X Y).z₂ = _
    rw [_root_.rsm_mul_z2]
    simp only [map_add, map_smul, splitOctEntryEnd_mul,
      splitOctEntryEnd_conj]
    simp [RealAlbertMatrix.mul, coordinateG2End]
    module
  · change splitOctEntryEnd D (RealAlbertMatrix.mul X Y).z₃ = _
    rw [_root_.rsm_mul_z3]
    simp only [map_add, map_smul, splitOctEntryEnd_mul,
      splitOctEntryEnd_conj]
    simp [RealAlbertMatrix.mul, coordinateG2End]
    module

/-- The explicit coordinate action is exactly the existing raw `liftG2End`
after algebraic soldering. -/
theorem coordinateG2End_solders (D : G2Derivation) :
    transportCoordinateEnd (coordinateG2End D) = liftG2End D := by
  apply LinearMap.ext
  intro X
  apply H3Zorn.ext_h3
  · simp [transportCoordinateEnd, coordinateG2End, h3Soldering_apply,
      liftG2End]
  · simp [transportCoordinateEnd, coordinateG2End, h3Soldering_apply,
      liftG2End]
  · simp [transportCoordinateEnd, coordinateG2End, h3Soldering_apply,
      liftG2End]
  · simp [transportCoordinateEnd, coordinateG2End, h3Soldering_apply,
      liftG2End, splitOctEntryEnd, RealAlbertH3ZornCarrierAlignment.fromH3]
  · simp [transportCoordinateEnd, coordinateG2End, h3Soldering_apply,
      liftG2End, splitOctEntryEnd, RealAlbertH3ZornCarrierAlignment.fromH3]
  · simp [transportCoordinateEnd, coordinateG2End, h3Soldering_apply,
      liftG2End, splitOctEntryEnd, RealAlbertH3ZornCarrierAlignment.fromH3]

/-- The formerly conditional compatible G2 subalgebra is the entire native
split-octonion derivation algebra. -/
theorem entrywiseCompatibleG2_eq_top : entrywiseCompatibleG2 = ⊤ := by
  exact entrywiseCompatibleG2_eq_top_of_algebraic_soldering
    coordinateG2End coordinateG2End_is_derivation coordinateG2End_solders

/-- Full faithful native G2 -> F4 Lie embedding obtained by restricting the
existing raw entrywise representation to the now-proved total compatibility. -/
noncomputable def fullG2ToF4LieHom :
    G2Derivation →ₗ⁅ℝ⁆ H3ZornF4Derivations := by
  let E : G2Derivation ≃ₗ⁅ℝ⁆ entrywiseCompatibleG2 :=
    LieEquiv.ofEq entrywiseCompatibleG2_eq_top |>.symm.trans
      (LieEquiv.topEquiv : (⊤ : LieSubalgebra ℝ G2Derivation) ≃ₗ⁅ℝ⁆ G2Derivation) |>.symm
  exact compatibleG2ToF4LieHom.comp E.toLieHom

end InfoGeometry.Canonical.G2H3ZornCoordinateSolderingClosure
