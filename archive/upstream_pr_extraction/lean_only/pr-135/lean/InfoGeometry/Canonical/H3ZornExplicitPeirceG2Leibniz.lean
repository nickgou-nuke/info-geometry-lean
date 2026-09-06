import Mathlib
import InfoGeometry.Canonical.H3ZornExplicitPeirceJordanSoldering
import InfoGeometry.Canonical.H3ZornSolderingDerivationTransport
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

/-- The vector-Zorn realization of a native canonical split-octonion derivation. -/
noncomputable def vectorDerivation (D : G2Derivation) : VDer :=
  canonicalToVectorDerivation D

/-- The native polar form is skew under every split-octonion derivation.
This is the exact infinitesimal preservation law needed by the three diagonal
Peirce coordinates. -/
theorem zornPair_derivation_skew
    (D : G2Derivation) (x y : Zorn) :
    zornPair (vectorDerivation D x) y +
      zornPair x (vectorDerivation D y) = 0 := by
  let Dv : VDer := vectorDerivation D
  let p : Params := derivationParameters Dv
  have hp : parameterDerivation p = Dv := parameterLinearEquiv.right_inv Dv
  have h := derivation_native_parameter_polar_skew p x y
  rw [hp] at h
  change
    ZornVectorMatrix.trace
        (ZornVectorMatrix.mul (Dv x) (ZornVectorMatrix.conj y)) +
      ZornVectorMatrix.trace
        (ZornVectorMatrix.mul x (ZornVectorMatrix.conj (Dv y))) = 0
  simpa [vectorNativeWittPairing, zornPair,
    ZornVectorMatrix.trace_mul_comm] using h

/-- Derivation outputs have zero scalar Zorn trace.  This follows from polar
skewness against the unit together with `D(1)=0`; no coordinate expansion is
needed. -/
theorem vectorDerivation_trace_zero
    (D : G2Derivation) (x : Zorn) :
    ZornVectorMatrix.trace (vectorDerivation D x) = 0 := by
  have h := zornPair_derivation_skew D x (ZornVectorMatrix.one : Zorn)
  simpa [vectorDerivation, zornPair, ZornVectorMatrix.one,
    ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.trace,
    ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross] using h

/-- Hence every derivation output lies in the imaginary conjugation eigenspace. -/
theorem conj_vectorDerivation_eq_neg
    (D : G2Derivation) (x : Zorn) :
    ZornVectorMatrix.conj (vectorDerivation D x) =
      ZornVectorMatrix.neg (vectorDerivation D x) := by
  rw [ZornVectorMatrix.conj_eq_scalar_trace_sub,
    vectorDerivation_trace_zero D x]
  ext i <;>
    simp [ZornVectorMatrix.scalar, ZornVectorMatrix.sub,
      ZornVectorMatrix.add, ZornVectorMatrix.neg, ZornVectorMatrix.zero]

/-- On derivation images, applying the derivation to a conjugate is the same
as conjugating the derivation image. -/
theorem vectorDerivation_map_conj
    (D : G2Derivation) (x : Zorn) :
    vectorDerivation D (ZornVectorMatrix.conj x) =
      ZornVectorMatrix.conj (vectorDerivation D x) := by
  rw [ZornVectorMatrix.Derivation.map_conj_eq_neg,
    conj_vectorDerivation_eq_neg]

/-- The pulled-back G2 action has the expected literal Peirce-coordinate
readback: it kills the three scalar rails and acts on each Zorn rail. -/
@[simp] theorem coordLiftG2_explicit
    (D : G2Derivation) (X : H3Coord) :
    coordLiftG2 D X =
      ((0, (0, 0)),
        (vectorDerivation D X.2.1,
          (vectorDerivation D X.2.2.1,
            vectorDerivation D X.2.2.2))) := by
  rcases X with ⟨⟨x1, x2, x3⟩, ⟨a, b, c⟩⟩
  rfl

/-- Main non-tautological coordinate theorem: the entrywise split-G2 action
satisfies Leibniz for the independently defined explicit Peirce/Zorn Jordan
product.  The diagonal coordinates close by polar skewness; the three
cyclic off-diagonal coordinates close by native Zorn Leibniz and conjugation
compatibility. -/
theorem coordinateJordanLeibniz_explicit
    (D : G2Derivation) (X Y : H3Coord) :
    coordLiftG2 D (coordJordanMulExplicit X Y) =
      coordJordanMulExplicit (coordLiftG2 D X) Y +
        coordJordanMulExplicit X (coordLiftG2 D Y) := by
  rcases X with ⟨⟨x1, x2, x3⟩, ⟨a, b, c⟩⟩
  rcases Y with ⟨⟨y1, y2, y3⟩, ⟨d, e, f⟩⟩
  let Dv : VDer := vectorDerivation D
  have had := zornPair_derivation_skew D a d
  have hbe := zornPair_derivation_skew D b e
  have hcf := zornPair_derivation_skew D c f
  apply Prod.ext
  · apply Prod.ext
    · simp only [coordLiftG2_explicit, coordJordanMulExplicit, Prod.fst,
        Prod.snd, zero_add]
      dsimp [Dv] at had hcf ⊢
      linarith
    · apply Prod.ext
      · simp only [coordLiftG2_explicit, coordJordanMulExplicit, Prod.fst,
          Prod.snd, zero_add]
        dsimp [Dv] at had hbe ⊢
        linarith
      · simp only [coordLiftG2_explicit, coordJordanMulExplicit, Prod.fst,
          Prod.snd, zero_add]
        dsimp [Dv] at hbe hcf ⊢
        linarith
  · apply Prod.ext
    · simp only [coordLiftG2_explicit, coordJordanMulExplicit, Prod.fst,
        Prod.snd]
      change Dv
          ((1 / 2 : ℝ) •
            (((x1 + x2) • d + (y1 + y2) • a) +
              ZornVectorMatrix.mul (ZornVectorMatrix.conj c)
                (ZornVectorMatrix.conj e) +
              ZornVectorMatrix.mul (ZornVectorMatrix.conj f)
                (ZornVectorMatrix.conj b))) = _
      simp only [Dv.map_smul', Dv.map_add', Dv.map_mul',
        vectorDerivation_map_conj D]
      module
    · apply Prod.ext
      · simp only [coordLiftG2_explicit, coordJordanMulExplicit, Prod.fst,
          Prod.snd]
        change Dv
            ((1 / 2 : ℝ) •
              (((x2 + x3) • e + (y2 + y3) • b) +
                ZornVectorMatrix.mul (ZornVectorMatrix.conj a)
                  (ZornVectorMatrix.conj f) +
                ZornVectorMatrix.mul (ZornVectorMatrix.conj d)
                  (ZornVectorMatrix.conj c))) = _
        simp only [Dv.map_smul', Dv.map_add', Dv.map_mul',
          vectorDerivation_map_conj D]
        module
      · simp only [coordLiftG2_explicit, coordJordanMulExplicit, Prod.fst,
          Prod.snd]
        change Dv
            ((1 / 2 : ℝ) •
              (((x3 + x1) • f + (y3 + y1) • c) +
                ZornVectorMatrix.mul (ZornVectorMatrix.conj b)
                  (ZornVectorMatrix.conj d) +
                ZornVectorMatrix.mul (ZornVectorMatrix.conj e)
                  (ZornVectorMatrix.conj a))) = _
        simp only [Dv.map_smul', Dv.map_add', Dv.map_mul',
          vectorDerivation_map_conj D]
        module

/-- The old coordinate predicate follows because the explicit product has
already been proved equal to the pullback product. -/
theorem coordinateJordanLeibniz_all (D : G2Derivation) :
    CoordinateJordanLeibniz D := by
  intro X Y
  rw [← coordJordanMulExplicit_eq_coordJordanMul]
  rw [← coordJordanMulExplicit_eq_coordJordanMul]
  rw [← coordJordanMulExplicit_eq_coordJordanMul]
  exact coordinateJordanLeibniz_explicit D X Y

/-- Every native split-octonion derivation is entrywise compatible with the
installed split-Albert Jordan product. -/
theorem full_g2_f4_compatibility : FullEntrywiseG2F4Compatibility := by
  exact full_g2_f4_compatibility_of_coordinate coordinateJordanLeibniz_all

/-- Equivalent concrete closure statement: the compatible subalgebra is all
of the native 14-dimensional split G2 derivation algebra. -/
theorem entrywiseCompatibleG2_eq_top :
    entrywiseCompatibleG2 = ⊤ :=
  full_g2_f4_compatibility

/-- The full entrywise G2 action therefore lands in the native F4 derivation
Lie algebra, with no compatibility subtype restriction remaining. -/
noncomputable def g2ToF4LieHom :
    G2Derivation →ₗ⁅ℝ⁆ H3ZornF4Derivations :=
  compatibleG2ToF4LieHom.comp
    (LieSubalgebra.equivOfEq entrywiseCompatibleG2_eq_top).symm.toLieHom

/-- The full G2-to-F4 Lie homomorphism is faithful. -/
theorem g2ToF4LieHom_injective : Function.Injective g2ToF4LieHom := by
  intro D E h
  apply liftG2End_injective
  exact congrArg (fun T : H3ZornF4Derivations => (T.1 : Module.End ℝ H3)) h

end InfoGeometry.Canonical.H3ZornExplicitPeirceG2Leibniz
