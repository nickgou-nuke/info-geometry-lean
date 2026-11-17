/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.CanonicalConjugation
import InfoGeometry.Lie.SplitOctonionEllPolarization
import InfoGeometry.Canonical.ZornPolarizationMetricBridge
import InfoGeometry.Canonical.ParaComplexNeutralForm
import Mathlib.LinearAlgebra.BilinearForm.Hom

/-!
# Scalar-potential obstructions on the actual split-octonion carrier

The scalar trace of a conjugate sandwich is the split norm times the scalar
trace of its middle argument. In particular it vanishes for a skew-conjugate
middle argument. This statement concerns a scalar readout; it does not identify
the two parenthesized carrier products.

The existing normalized coordinate polar form is transported to the canonical
Zorn carrier. The existing left action of `lUnit` supplies its anti-isometric
involution. Instantiating the existing neutral-form theorem proves that the
symmetric cross pairing of its Peirce projections is half the split norm,
with the nonzero value `1 / 2` at the identity. No new splitting is defined.

Finally, a concrete associator has two arguments inside the existing
split-quaternion core and its third argument outside. Membership of the first
argument alone therefore does not make ambient associator channels vanish.
These are finite algebraic statements, not a manifold or Hessian construction.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Lie.SplitOctonionScalarPotentialObstruction

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Canonical.ZornVectorMatrixExplicit
open InfoGeometry.Canonical.ZornPolarizationMetricBridge
open InfoGeometry.Canonical.ParaComplexConnection
open InfoGeometry.Canonical.ParaComplexNeutralForm

/-- Scalar trace can be reassociated, although the underlying products need not agree. -/
theorem sandwich_trace_reassociate (X K : CanonicalZorn) :
    realZornTrace ((X * K) * canonicalConj X) =
      realZornTrace (X * (K * canonicalConj X)) := by
  change InfoGeometry.Algebra.ZornVectorMatrix.trace
      (canonicalVectorEquiv ((X * K) * canonicalConj X)) =
    InfoGeometry.Algebra.ZornVectorMatrix.trace
      (canonicalVectorEquiv (X * (K * canonicalConj X)))
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_canonicalConj]
  exact InfoGeometry.Algebra.ZornVectorMatrix.trace_mul_assoc _ _ _

/-- The exact scalar sandwich identity, with no invertibility or unit-norm premise. -/
theorem sandwich_trace (X K : CanonicalZorn) :
    realZornTrace ((X * K) * canonicalConj X) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 X *
        realZornTrace K := by
  rw [← InfoGeometry.Lie.SplitOctonionImaginaryAction.vector_norm_eq_canonical_det]
  change InfoGeometry.Algebra.ZornVectorMatrix.trace
      (canonicalVectorEquiv ((X * K) * canonicalConj X)) =
    InfoGeometry.Algebra.ZornVectorMatrix.norm (canonicalVectorEquiv X) *
      InfoGeometry.Algebra.ZornVectorMatrix.trace (canonicalVectorEquiv K)
  simp only [canonicalVectorEquiv_mul, canonicalVectorEquiv_canonicalConj]
  rw [InfoGeometry.Algebra.ZornVectorMatrix.trace_mul_comm
    (InfoGeometry.Algebra.ZornVectorMatrix.mul
      (canonicalVectorEquiv X) (canonicalVectorEquiv K))
    (InfoGeometry.Algebra.ZornVectorMatrix.conj (canonicalVectorEquiv X))]
  rw [← InfoGeometry.Algebra.ZornVectorMatrix.trace_mul_assoc,
    InfoGeometry.Algebra.ZornVectorMatrix.conj_norm_identity_right,
    InfoGeometry.Algebra.ZornVectorMatrix.scalar_mul,
    InfoGeometry.Algebra.ZornVectorMatrix.trace_smul]

/-- A skew-conjugate middle argument has zero scalar sandwich trace. -/
theorem sandwich_trace_eq_zero_of_skew_conj (X K : CanonicalZorn)
    (hK : canonicalConj K = -K) :
    realZornTrace ((X * K) * canonicalConj X) = 0 := by
  have h := congrArg realZornTrace hK
  change K.b + K.a = -K.a + -K.b at h
  have htrace : realZornTrace K = 0 := by
    unfold realZornTrace
    linarith
  rw [sandwich_trace, htrace, mul_zero]

/-- The other bracketing has the same vanishing scalar readout. -/
theorem sandwich_trace_right_eq_zero_of_skew_conj (X K : CanonicalZorn)
    (hK : canonicalConj K = -K) :
    realZornTrace (X * (K * canonicalConj X)) = 0 := by
  rw [← sandwich_trace_reassociate]
  exact sandwich_trace_eq_zero_of_skew_conj X K hK

/-- The proposed scalar potential with the distinguished split axis is identically zero. -/
theorem ell_sandwich_scalar_eq_zero (X : CanonicalZorn) :
    realZornTrace ((X * lUnit) * canonicalConj X) / 2 = 0 := by
  rw [sandwich_trace]
  simp [realZornTrace, lUnit]

/-- Transport the existing normalized polar form, preserving its exact normalization. -/
def neutralForm : LinearMap.BilinForm ℝ CanonicalZorn :=
  polarForm.comp
    (InfoGeometry.Canonical.ZornMatrix.coordLinearEquiv :
      CanonicalZorn ≃ₗ[ℝ] ZornCoord).toLinearMap
    (InfoGeometry.Canonical.ZornMatrix.coordLinearEquiv :
      CanonicalZorn ≃ₗ[ℝ] ZornCoord).toLinearMap

@[simp] theorem neutralForm_apply (X Y : CanonicalZorn) :
    neutralForm X Y = polarPair
      (InfoGeometry.Canonical.ZornMatrix.coordLinearEquiv X)
      (InfoGeometry.Canonical.ZornMatrix.coordLinearEquiv Y) := rfl

/-- The transported form is the actual conjugate-product scalar pairing. -/
theorem neutralForm_eq_scalar_trace (X Y : CanonicalZorn) :
    neutralForm X Y = realZornTrace (X * canonicalConj Y) / 2 := by
  simp [neutralForm_apply, polarPair, zornA, zornB, zornX, zornY, dot3,
    realZornTrace, canonicalConj, canonicalVectorEquiv,
    InfoGeometry.Algebra.ZornVectorMatrix.conj,
    InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot]
  ring

@[simp] theorem neutralForm_self (X : CanonicalZorn) :
    neutralForm X X = InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 X := by
  rw [neutralForm_apply, polarPair_self]
  rfl

/-- Left multiplication by the existing split axis reverses the neutral metric. -/
theorem neutralForm_ellLeftMul (X Y : CanonicalZorn) :
    neutralForm (ellLeftMul X) (ellLeftMul Y) = -neutralForm X Y := by
  simp [neutralForm_apply, polarPair, zornA, zornB, zornX, zornY, dot3,
    ellLeftMul_apply, lUnit, InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross,
    smul_eq_mul]
  ring

/-- Package the already proved full-carrier involution for the existing Peirce API. -/
def ellParaComplex : ParaComplexStructure CanonicalZorn where
  tau := ellLeftMul
  tau_sq X := congrArg (fun f : Module.End ℝ CanonicalZorn => f X) ellLeftMul_sq

/-- Concrete neutral data: both laws are proved for the actual form and multiplication. -/
def ellNeutralDatum : Datum ellParaComplex where
  form := neutralForm
  symmetric X Y := polarPair_symm _ _
  anti_isometry := neutralForm_ellLeftMul

/-- The positive eigenspace is isotropic for the full normalized split form. -/
theorem neutralForm_plus_isotropic {X Y : CanonicalZorn}
    (hX : X ∈ plusEigenspace ellParaComplex)
    (hY : Y ∈ plusEigenspace ellParaComplex) : neutralForm X Y = 0 :=
  plus_isotropic ellParaComplex neutralForm
    (antiCompatible_of_anti_isometry ellParaComplex ellNeutralDatum) hX hY

/-- The negative eigenspace is isotropic for the same form. -/
theorem neutralForm_minus_isotropic {X Y : CanonicalZorn}
    (hX : X ∈ minusEigenspace ellParaComplex)
    (hY : Y ∈ minusEigenspace ellParaComplex) : neutralForm X Y = 0 :=
  minus_isotropic ellParaComplex neutralForm
    (antiCompatible_of_anti_isometry ellParaComplex ellNeutralDatum) hX hY

/-- The symmetric cross potential is half the split norm, not identically zero. -/
theorem cross_pairing_eq_half_norm (X : CanonicalZorn) :
    neutralForm (peircePlus ellParaComplex X) (peirceMinus ellParaComplex X) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 X / 2 := by
  have h := form_self_eq_two_mul_cross_pairing ellParaComplex ellNeutralDatum X
  change neutralForm X X =
    2 * neutralForm (peircePlus ellParaComplex X) (peirceMinus ellParaComplex X) at h
  rw [neutralForm_self] at h
  linarith

/-- A concrete nonzero value of the cross potential. -/
theorem cross_pairing_one :
    neutralForm (peircePlus ellParaComplex (1 : CanonicalZorn))
      (peirceMinus ellParaComplex (1 : CanonicalZorn)) = 1 / 2 := by
  rw [cross_pairing_eq_half_norm]
  norm_num [InfoGeometry.Algebra.Zorn.ZornMatrix.detZ, realCrossProduct3,
    InfoGeometry.Canonical.ZornMatrix.dot]

/-- Antisymmetrizing the scalar conjugate pairing instead gives zero. -/
theorem antisymmetric_scalar_pairing_eq_zero (X Y : CanonicalZorn) :
    realZornTrace (X * canonicalConj Y) / 2 -
      realZornTrace (Y * canonicalConj X) / 2 = 0 := by
  rw [← neutralForm_eq_scalar_trace X Y, ← neutralForm_eq_scalar_trace Y X]
  exact sub_eq_zero.mpr (ellNeutralDatum.symmetric X Y)

/-- An explicit ambient associator, with the orientation fixed by the native cross product. -/
theorem core_ambient_associator :
    (lUnit * kUnit) * InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (1 : Fin 3) -
      lUnit * (kUnit * InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (1 : Fin 3)) =
        (-2 : ℝ) • InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis (2 : Fin 3) := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · norm_num [kUnit_def, lUnit, InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
      InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
      InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply]
  · norm_num [kUnit_def, lUnit, InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
      InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
      InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply]
  · funext i
    fin_cases i <;>
      norm_num [kUnit_def, lUnit, InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
        InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
        InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply]
  · funext i
    fin_cases i <;>
      norm_num [kUnit_def, lUnit, InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis,
        InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis,
        InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply]

theorem core_ambient_associator_ne_zero :
    (lUnit * kUnit) * InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (1 : Fin 3) -
      lUnit * (kUnit * InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (1 : Fin 3)) ≠ 0 := by
  rw [core_ambient_associator]
  intro h
  have hy := congrArg (fun X : CanonicalZorn => X.y 2) h
  norm_num [InfoGeometry.Canonical.ZornMatrix.chiralLowerBasis] at hy

/-- The third argument of the witness lies outside the actual associative core. -/
theorem chiralUpper_one_not_mem_core :
    InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (1 : Fin 3) ∉ coreSubmodule := by
  intro h
  apply core_ambient_associator_ne_zero
  exact sub_eq_zero.mpr
    (InfoGeometry.Algebra.Zorn.SplitQuaternionCore.assoc _ _ _ l_mem_core k_mem_core h)

/-- Even two core arguments do not kill an associator with an ambient third argument. -/
theorem associative_core_does_not_kill_ambient_channels :
    ∃ v a b : CanonicalZorn, v ∈ coreSubmodule ∧ a ∈ coreSubmodule ∧
      b ∉ coreSubmodule ∧ (v * a) * b - v * (a * b) ≠ 0 :=
  ⟨lUnit, kUnit, InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (1 : Fin 3),
    l_mem_core, k_mem_core, chiralUpper_one_not_mem_core, core_ambient_associator_ne_zero⟩

end InfoGeometry.Lie.SplitOctonionScalarPotentialObstruction
