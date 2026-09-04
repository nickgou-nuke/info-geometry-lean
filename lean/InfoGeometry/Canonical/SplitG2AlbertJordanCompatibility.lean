import Mathlib
import InfoGeometry.Canonical.SplitG2AlbertEntrywiseLift
import InfoGeometry.Algebra.H3ZornCoordinateReadback
import InfoGeometry.Algebra.ZornDerivationBridge
import InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge

noncomputable section

namespace InfoGeometry.Canonical.SplitG2AlbertJordanCompatibility

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
open InfoGeometry.Canonical.H3ZornAlgebraicSoldering
open InfoGeometry.Canonical.SplitG2AlbertEntrywiseLift

abbrev G2Der := canonicalZornDerivations
abbrev Zorn := ZornVectorMatrix ℝ
abbrev H3 := H3Zorn ℝ

private abbrev vDer (D : G2Der) : ZornVectorMatrix.Derivation (R := ℝ) :=
  canonicalToVectorDerivation D

/-- Every split-octonion derivation has trace-zero output.  This is read from
    the already-certified 14-parameter normal form rather than added as a new
    axiom about composition algebras. -/
theorem zornDerivation_output_trace_zero (D : G2Der) (X : Zorn) :
    ZornVectorMatrix.trace (vDer D X) = 0 := by
  let p : Params := derivationParameters (vDer D)
  have hp : parameterDerivation p = vDer D := parameterLinearEquiv.right_inv (vDer D)
  rw [← hp]
  rcases X with ⟨a,v,w,b⟩
  simp [vDer, parameterDerivation, parameterAction, ZornVectorMatrix.trace]
  ring

/-- Consequently a derivation output lies in the imaginary conjugation
    eigenspace. -/
theorem zornDerivation_output_conj_eq_neg (D : G2Der) (X : Zorn) :
    ZornVectorMatrix.conj (vDer D X) = ZornVectorMatrix.neg (vDer D X) := by
  rw [ZornVectorMatrix.conj_eq_scalar_trace_sub,
    zornDerivation_output_trace_zero]
  simp [ZornVectorMatrix.scalar, ZornVectorMatrix.sub,
    ZornVectorMatrix.zero, ZornVectorMatrix.neg]

/-- The native Zorn polar pairing is infinitesimally invariant under every
    canonical split-octonion derivation, written in the orientation used by
    the split-Albert trace pairing. -/
theorem zornDerivation_tracePair_skew
    (D : G2Der) (X Y : Zorn) :
    ZornVectorMatrix.trace
        (ZornVectorMatrix.mul (vDer D X) (ZornVectorMatrix.conj Y)) +
      ZornVectorMatrix.trace
        (ZornVectorMatrix.mul X (ZornVectorMatrix.conj (vDer D Y))) = 0 := by
  have h := derivation_native_witt_skew D
    (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.symm X)
    (InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv.symm Y)
  simpa [nativeCanonicalWittPairing, vDer,
    canonicalToVectorDerivation_apply,
    ZornVectorMatrix.trace_mul_comm] using h

/-- The entrywise Albert lift has zero linear trace because it fixes all three
    diagonal scalar coordinates. -/
@[simp] theorem liftG2End_linearTrace_zero (D : G2Der) (X : H3) :
    H3Zorn.linearTrace (liftG2End D X) = 0 := by
  rfl

/-- The Albert trace bilinear form is infinitesimally invariant under the
    entrywise `G2` action. -/
theorem liftG2End_traceBilin_skew (D : G2Der) (X Y : H3) :
    H3Zorn.traceBilin (liftG2End D X) Y +
      H3Zorn.traceBilin X (liftG2End D Y) = 0 := by
  have ha := zornDerivation_tracePair_skew D X.a Y.a
  have hb := zornDerivation_tracePair_skew D X.b Y.b
  have hc := zornDerivation_tracePair_skew D X.c Y.c
  simp [H3Zorn.traceBilin, liftG2End, vDer] at ha hb hc ⊢
  linarith

/-- Differentiated quadratic-adjoint law.  This is the only place where the
    six Peirce lanes are inspected.  It uses the native Zorn Leibniz law,
    trace-zero/conjugation output, and the invariant polar pairing; no
    27-coordinate basis expansion is used. -/
theorem liftG2End_adjointQuad (D : G2Der) (X : H3) :
    liftG2End D (H3Zorn.adjointQuad X) =
      H3Zorn.crossProduct (liftG2End D X) X := by
  let d := vDer D
  have hca := zornDerivation_output_conj_eq_neg D X.a
  have hcb := zornDerivation_output_conj_eq_neg D X.b
  have hcc := zornDerivation_output_conj_eq_neg D X.c
  have hpa := zornDerivation_tracePair_skew D X.a X.a
  have hpb := zornDerivation_tracePair_skew D X.b X.b
  have hpc := zornDerivation_tracePair_skew D X.c X.c
  apply H3Zorn.ext_h3
  · simp [H3Zorn.crossProduct, H3Zorn.adjointQuad, liftG2End,
      ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj,
      hpb, d]
  · simp [H3Zorn.crossProduct, H3Zorn.adjointQuad, liftG2End,
      ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj,
      hpc, d]
  · simp [H3Zorn.crossProduct, H3Zorn.adjointQuad, liftG2End,
      ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj,
      hpa, d]
  · change d
        (ZornVectorMatrix.sub
          (ZornVectorMatrix.mul (ZornVectorMatrix.conj X.c)
            (ZornVectorMatrix.conj X.b))
          (ZornVectorMatrix.smul X.α₃ X.a)) = _
    rw [map_sub, d.map_mul]
    simp only [map_smul, ZornVectorMatrix.Derivation.map_conj_eq_neg]
    simp [H3Zorn.crossProduct, H3Zorn.adjointQuad, liftG2End,
      ZornVectorMatrix.conj_add, ZornVectorMatrix.add_mul,
      ZornVectorMatrix.mul_add, ZornVectorMatrix.sub_eq_add_neg,
      hcb, hcc, d]
    module
  · change d
        (ZornVectorMatrix.sub
          (ZornVectorMatrix.mul (ZornVectorMatrix.conj X.a)
            (ZornVectorMatrix.conj X.c))
          (ZornVectorMatrix.smul X.α₁ X.b)) = _
    rw [map_sub, d.map_mul]
    simp only [map_smul, ZornVectorMatrix.Derivation.map_conj_eq_neg]
    simp [H3Zorn.crossProduct, H3Zorn.adjointQuad, liftG2End,
      ZornVectorMatrix.conj_add, ZornVectorMatrix.add_mul,
      ZornVectorMatrix.mul_add, ZornVectorMatrix.sub_eq_add_neg,
      hca, hcc, d]
    module
  · change d
        (ZornVectorMatrix.sub
          (ZornVectorMatrix.mul (ZornVectorMatrix.conj X.b)
            (ZornVectorMatrix.conj X.a))
          (ZornVectorMatrix.smul X.α₂ X.c)) = _
    rw [map_sub, d.map_mul]
    simp only [map_smul, ZornVectorMatrix.Derivation.map_conj_eq_neg]
    simp [H3Zorn.crossProduct, H3Zorn.adjointQuad, liftG2End,
      ZornVectorMatrix.conj_add, ZornVectorMatrix.add_mul,
      ZornVectorMatrix.mul_add, ZornVectorMatrix.sub_eq_add_neg,
      hca, hcb, d]
    module

/-- The Freudenthal cross product satisfies the Leibniz rule under the
    entrywise split-`G2` action. -/
theorem liftG2End_crossProduct (D : G2Der) (X Y : H3) :
    liftG2End D (H3Zorn.crossProduct X Y) =
      H3Zorn.crossProduct (liftG2End D X) Y +
        H3Zorn.crossProduct X (liftG2End D Y) := by
  rw [H3Zorn.crossProduct, map_sub, map_sub,
    liftG2End_adjointQuad, liftG2End_adjointQuad,
    liftG2End_adjointQuad]
  rw [map_add]
  rw [H3Zorn.crossProduct_add_left, H3Zorn.crossProduct_add_right]
  rw [H3Zorn.crossProduct_symm (liftG2End D Y) X]
  abel

/-- The scalar coefficient created by differentiating the cross-product trace
    vanishes. -/
theorem liftG2End_crossProduct_linearTrace_sum_zero
    (D : G2Der) (X Y : H3) :
    H3Zorn.linearTrace (H3Zorn.crossProduct (liftG2End D X) Y) +
      H3Zorn.linearTrace (H3Zorn.crossProduct X (liftG2End D Y)) = 0 := by
  rw [H3Zorn.linearTrace_crossProduct, H3Zorn.linearTrace_crossProduct]
  rw [liftG2End_linearTrace_zero, liftG2End_linearTrace_zero]
  have h := liftG2End_traceBilin_skew D X Y
  linarith

/-- Main target: every canonical split-octonion derivation acts entrywise as a
    derivation of the installed split-Albert Jordan product. -/
theorem liftG2End_isJordanDerivation (D : G2Der) :
    H3ZornJordanDerivation (liftG2End D) := by
  intro X Y
  rw [← candidateJordanMul_eq_mul, ← candidateJordanMul_eq_mul,
    ← candidateJordanMul_eq_mul]
  rw [candidateJordanMul_trace_formula, candidateJordanMul_trace_formula,
    candidateJordanMul_trace_formula]
  rw [map_smul, map_add, map_add, map_sub, map_add,
    liftG2End_crossProduct]
  simp only [liftG2End_linearTrace_zero, zero_smul]
  have htrace := liftG2End_crossProduct_linearTrace_sum_zero D X Y
  apply H3Zorn.ext_h3 <;>
    simp [H3Zorn.linearTrace, H3Zorn.add_readback, H3Zorn.sub_readback,
      H3Zorn.smul_readback, liftG2End, htrace] <;>
    module

/-- The source-coordinate Leibniz proposition identified by the algebraic
    soldering layer is therefore unconditional. -/
theorem entrywiseCoordJordanCompatible_all (D : G2Der) :
    EntrywiseCoordJordanCompatible D := by
  intro X Y
  apply h3Soldering.injective
  rw [h3Soldering_jordan_intertwines]
  rw [h3Soldering_entrywise_intertwines,
    h3Soldering_entrywise_intertwines,
    h3Soldering_entrywise_intertwines]
  simpa [candidateJordanMul_eq_mul] using
    liftG2End_isJordanDerivation D (h3Soldering X) (h3Soldering Y)

/-- The coordinate compatibility subspace is all of split `G2(2)`. -/
def entrywiseCompatibleG2 : Submodule ℝ G2Der :=
  ⊤

@[simp] theorem entrywiseCompatibleG2_eq_top : entrywiseCompatibleG2 = ⊤ := rfl

/-- The algebraic soldering witness is now unconditional. -/
noncomputable def unconditionalG2F4Soldering : G2F4Soldering :=
  g2F4SolderingOfCoord entrywiseCoordJordanCompatible_all

/-- Unconditional injective Lie embedding `g2(2) -> f4(4)` on the native
    split-octonion/split-Albert carriers. -/
noncomputable def g2ToF4 : G2Der →ₗ⁅ℝ⁆ H3ZornF4Derivations :=
  g2ToF4LieHom unconditionalG2F4Soldering

@[simp] theorem g2ToF4_injective : Function.Injective g2ToF4 :=
  g2ToF4LieHom_injective unconditionalG2F4Soldering

/-- The embedded split `G2` subalgebra has exact real dimension 14. -/
theorem g2ToF4_range_finrank :
    Module.finrank ℝ (LinearMap.range g2ToF4) = 14 :=
  InfoGeometry.Canonical.SplitG2AlbertEntrywiseLift.g2ToF4_range_finrank
    unconditionalG2F4Soldering

end InfoGeometry.Canonical.SplitG2AlbertJordanCompatibility
