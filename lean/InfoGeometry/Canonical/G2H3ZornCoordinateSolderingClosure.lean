import Mathlib
import InfoGeometry.Canonical.H3ZornAlgebraicSolderingTransport
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
import InfoGeometry.Algebra.RealSplitOctZornAlignment
import InfoGeometry.Canonical.RealSplitOctZornAPI

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
open InfoGeometry.Canonical.RealSplitOctZornAPI
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
  change ZornVectorMatrix.conj (d X) = ZornVectorMatrix.neg (d X)
  rw [← hp]
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
    change fromZorn ((Dv D) (toZorn (X + Y))) = _
    rw [toZorn_add_apply]
    change fromZorn ((Dv D) (ZornVectorMatrix.add (toZorn X) (toZorn Y))) = _
    rw [(Dv D).map_add']
    change fromZorn ((Dv D) (toZorn X) + (Dv D) (toZorn Y)) = _
    rw [fromZorn_add_apply]
  map_smul' r X := by
    change fromZorn ((Dv D) (toZorn (r • X))) = _
    rw [toZorn_smul_apply]
    change fromZorn ((Dv D) (ZornVectorMatrix.smul r (toZorn X))) = _
    rw [(Dv D).map_smul']
    change fromZorn (r • (Dv D) (toZorn X)) = _
    rw [fromZorn_smul_apply]
    rfl

/-- Factor-level Leibniz is just the native Zorn derivation law transported
through the multiplicative split-octonion soldering. -/
theorem splitOctEntryEnd_mul
    (D : G2Derivation) (X Y : RealSplitOct) :
    splitOctEntryEnd D (RealSplitOct.mul X Y) =
      RealSplitOct.mul (splitOctEntryEnd D X) Y +
        RealSplitOct.mul X (splitOctEntryEnd D Y) := by
  change fromZorn ((Dv D) (toZorn (RealSplitOct.mul X Y))) = _
  rw [toZorn_mul_apply]
  rw [(Dv D).map_mul']
  change fromZorn (ZornVectorMatrix.mul ((Dv D) (toZorn X)) (toZorn Y) +
                   ZornVectorMatrix.mul (toZorn X) ((Dv D) (toZorn Y))) = _
  rw [fromZorn_add_apply, fromZorn_mul_apply, fromZorn_mul_apply]
  rw [fromZorn_toZorn, fromZorn_toZorn]
  rfl

/-- The transported factor derivation commutes with conjugation. -/
theorem splitOctEntryEnd_conj
    (D : G2Derivation) (X : RealSplitOct) :
    splitOctEntryEnd D (RealSplitOct.conj X) =
      RealSplitOct.conj (splitOctEntryEnd D X) := by
  change fromZorn ((Dv D) (toZorn (RealSplitOct.conj X))) = _
  rw [toZorn_conj_apply]
  rw [vector_map_conj]
  rw [fromZorn_conj_apply]
  rfl

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
    apply RealAlbertMatrix.ext
    · change 0 = 0 + 0; ring
    · change 0 = 0 + 0; ring
    · change 0 = 0 + 0; ring
    · exact map_add (splitOctEntryEnd D) X.z₁ Y.z₁
    · exact map_add (splitOctEntryEnd D) X.z₂ Y.z₂
    · exact map_add (splitOctEntryEnd D) X.z₃ Y.z₃
  map_smul' r X := by
    apply RealAlbertMatrix.ext
    · change 0 = r * 0; ring
    · change 0 = r * 0; ring
    · change 0 = r * 0; ring
    · exact map_smul (splitOctEntryEnd D) r X.z₁
    · exact map_smul (splitOctEntryEnd D) r X.z₂
    · exact map_smul (splitOctEntryEnd D) r X.z₃

@[simp] lemma smul_eq_smul (r : ℝ) (X : RealSplitOct) : RealSplitOct.smul r X = r • X := rfl

@[simp] lemma add_z1 (M₁ M₂ : RealAlbertMatrix) : (M₁ + M₂).z₁ = M₁.z₁ + M₂.z₁ := rfl
@[simp] lemma add_z2 (M₁ M₂ : RealAlbertMatrix) : (M₁ + M₂).z₂ = M₁.z₂ + M₂.z₂ := rfl
@[simp] lemma add_z3 (M₁ M₂ : RealAlbertMatrix) : (M₁ + M₂).z₃ = M₁.z₃ + M₂.z₃ := rfl

lemma mul_alpha1 (X Y : RealAlbertMatrix) :
    (RealAlbertMatrix.mul X Y).α₁ =
      X.α₁ * Y.α₁ + (1/2 : ℝ) * (splitOctPair X.z₃ Y.z₃ + splitOctPair X.z₂ Y.z₂) := by
  dsimp [RealAlbertMatrix.mul, splitOctPair, RealSplitOct.mul, RealSplitOct.conj]
  ring

lemma mul_alpha2 (X Y : RealAlbertMatrix) :
    (RealAlbertMatrix.mul X Y).α₂ =
      X.α₂ * Y.α₂ + (1/2 : ℝ) * (splitOctPair X.z₃ Y.z₃ + splitOctPair X.z₁ Y.z₁) := by
  dsimp [RealAlbertMatrix.mul, splitOctPair, RealSplitOct.mul, RealSplitOct.conj]
  ring

lemma mul_alpha3 (X Y : RealAlbertMatrix) :
    (RealAlbertMatrix.mul X Y).α₃ =
      X.α₃ * Y.α₃ + (1/2 : ℝ) * (splitOctPair X.z₂ Y.z₂ + splitOctPair X.z₁ Y.z₁) := by
  dsimp [RealAlbertMatrix.mul, splitOctPair, RealSplitOct.mul, RealSplitOct.conj]
  ring

/-- The coordinate entrywise action obeys the Albert Jordan Leibniz rule.
The proof uses only factor multiplication, conjugation, and the polarized
pairing; it does not expand the 27 scalar coordinates. -/
theorem coordinateG2End_is_derivation (D : G2Derivation) :
    CoordinateJordanDerivation (coordinateG2End D) := by
  intro X Y
  apply RealAlbertMatrix.ext
  · change 0 = (RealAlbertMatrix.mul (coordinateG2End D X) Y).α₁ +
               (RealAlbertMatrix.mul X (coordinateG2End D Y)).α₁
    rw [mul_alpha1, mul_alpha1]
    have h3 := splitOctPair_skew D X.z₃ Y.z₃
    have h2 := splitOctPair_skew D X.z₂ Y.z₂
    dsimp [coordinateG2End]
    linarith
  · change 0 = (RealAlbertMatrix.mul (coordinateG2End D X) Y).α₂ +
               (RealAlbertMatrix.mul X (coordinateG2End D Y)).α₂
    rw [mul_alpha2, mul_alpha2]
    have h3 := splitOctPair_skew D X.z₃ Y.z₃
    have h1 := splitOctPair_skew D X.z₁ Y.z₁
    dsimp [coordinateG2End]
    linarith
  · change 0 = (RealAlbertMatrix.mul (coordinateG2End D X) Y).α₃ +
               (RealAlbertMatrix.mul X (coordinateG2End D Y)).α₃
    rw [mul_alpha3, mul_alpha3]
    have h2 := splitOctPair_skew D X.z₂ Y.z₂
    have h1 := splitOctPair_skew D X.z₁ Y.z₁
    dsimp [coordinateG2End]
    linarith
  · change splitOctEntryEnd D (RealAlbertMatrix.mul X Y).z₁ = _
    rw [_root_.rsm_mul_z1]
    simp only [smul_eq_smul, map_add, map_smul, splitOctEntryEnd_mul,
      splitOctEntryEnd_conj]
    simp [RealAlbertMatrix.mul, coordinateG2End, add_z1]
    module
  · change splitOctEntryEnd D (RealAlbertMatrix.mul X Y).z₂ = _
    rw [_root_.rsm_mul_z2]
    simp only [smul_eq_smul, map_add, map_smul, splitOctEntryEnd_mul,
      splitOctEntryEnd_conj]
    simp [RealAlbertMatrix.mul, coordinateG2End, add_z2]
    module
  · change splitOctEntryEnd D (RealAlbertMatrix.mul X Y).z₃ = _
    rw [_root_.rsm_mul_z3]
    simp only [smul_eq_smul, map_add, map_smul, splitOctEntryEnd_mul,
      splitOctEntryEnd_conj]
    simp [RealAlbertMatrix.mul, coordinateG2End, add_z3]
    module

/-- The inverse of the algebraic soldering is the maintained `fromH3`
coordinate readback. -/
@[simp] theorem h3Soldering_symm_apply (X : H3Zorn ℝ) :
    h3Soldering.symm X =
      RealAlbertH3ZornCarrierAlignment.fromH3 X := by
  apply h3Soldering.injective
  rw [h3Soldering.apply_symm_apply, h3Soldering_apply]
  exact (RealAlbertH3ZornCarrierAlignment.equiv.apply_symm_apply X).symm

/-- The explicit coordinate action is exactly the existing raw `liftG2End`
after algebraic soldering. -/
theorem coordinateG2End_solders (D : G2Derivation) :
    transportCoordinateEnd (coordinateG2End D) = liftG2End D := by
  apply LinearMap.ext
  intro X
  apply H3Zorn.ext_h3
  · rfl
  · rfl
  · rfl
  · simp [transportCoordinateEnd, coordinateG2End, h3Soldering_apply,
      h3Soldering_symm_apply, liftG2End, splitOctEntryEnd,
      RealAlbertH3ZornCarrierAlignment.fromH3]
    dsimp [RealAlbertH3ZornCarrierAlignment.toH3]
    rw [toZorn_fromZorn, toZorn_fromZorn]
  · simp [transportCoordinateEnd, coordinateG2End, h3Soldering_apply,
      h3Soldering_symm_apply, liftG2End, splitOctEntryEnd,
      RealAlbertH3ZornCarrierAlignment.fromH3]
    dsimp [RealAlbertH3ZornCarrierAlignment.toH3]
    rw [toZorn_fromZorn, toZorn_fromZorn]
  · simp [transportCoordinateEnd, coordinateG2End, h3Soldering_apply,
      h3Soldering_symm_apply, liftG2End, splitOctEntryEnd,
      RealAlbertH3ZornCarrierAlignment.fromH3]
    dsimp [RealAlbertH3ZornCarrierAlignment.toH3]
    rw [toZorn_fromZorn, toZorn_fromZorn]

/-- The formerly conditional compatible G2 subalgebra is the entire native
split-octonion derivation algebra. -/
theorem entrywiseCompatibleG2_eq_top : entrywiseCompatibleG2 = ⊤ := by
  exact entrywiseCompatibleG2_eq_top_of_algebraic_soldering
    coordinateG2End coordinateG2End_is_derivation coordinateG2End_solders

/-- Full native G2 -> F4 Lie homomorphism. -/
noncomputable def fullG2ToF4LieHom :
    G2Derivation →ₗ⁅ℝ⁆ H3ZornF4Derivations where
  toFun D :=
    ⟨liftG2End D, by
      have hmem : D ∈ entrywiseCompatibleG2 := by
        rw [entrywiseCompatibleG2_eq_top]
        exact LieSubalgebra.mem_top D
      exact hmem⟩
  map_add' D E := by
    apply Subtype.ext
    exact liftG2End_add D E
  map_smul' r D := by
    apply Subtype.ext
    exact liftG2End_smul r D
  map_lie' := by
    intro D E
    apply Subtype.ext
    exact liftG2End_lie D E

/-- The full soldered G2 -> F4 map remains faithful. -/
theorem fullG2ToF4LieHom_injective : Function.Injective fullG2ToF4LieHom := by
  intro D E h
  apply liftG2End_injective
  have hval : (fullG2ToF4LieHom D).1 = (fullG2ToF4LieHom E).1 := congrArg Subtype.val h
  exact hval

end InfoGeometry.Canonical.G2H3ZornCoordinateSolderingClosure
