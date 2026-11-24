/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornCl44Triality
import InfoGeometry.Canonical.ZornSignedConvention
import InfoGeometry.Canonical.ZornPolarizationMetricBridge
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# The canonical Zorn primal-dual splitting and its doubled CAR action

The existing `nullFourSplit` is transported through the native Zorn coordinate
equivalence.  The same spatial sign change on both halves makes the first
half agree with `ZornSignedConvention.primal`; the second half then consists
of coefficients of the signed lower ladders.  Thus the quadratic form is
the positive evaluation pairing `p(q)`.  The raw lower coordinates in
`ZornSignedConvention.dual` require three spatial sign reversals.

All subspaces live in the existing canonical Zorn carrier, all Clifford
operators act on its existing `DiracSpinor16`, and the dual is Mathlib's
`Module.Dual`.  The involutive exchange is the existing `fundamental`
symmetry.  It preserves the quadratic form and reverses the canonical skew
form; it is distinct from a signed quarter-turn whose square is `-1`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornCl44PrimalDual

open ZornMatrix ZornClifford ZornCl44Triality
open InfoGeometry.Clifford.NeutralPhaseSpaceCore

/-- The repository's existing four-coordinate real vector space. -/
abbrev Four := InfoGeometry.Algebra.FiniteSpin.Vec4R

/-- Change the three spatial signs while joining a scalar and a three-vector. -/
private def signedFourCoordinates : (ℝ × (Fin 3 → ℝ)) ≃ₗ[ℝ] Four where
  toFun u := ![u.1, -u.2 0, -u.2 1, -u.2 2]
  invFun q := (q 0, ![-q 1, -q 2, -q 3])
  left_inv u := by
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp
  right_inv q := by
    funext i
    fin_cases i <;> simp
  map_add' u v := by
    funext i
    fin_cases i <;> simp [add_comm]
  map_smul' r u := by
    funext i
    fin_cases i <;> simp

/-- The positive-pairing Witt coordinates, obtained from the existing splitting. -/
def wittCoordinates : ZornMatrix ℝ ≃ₗ[ℝ] (Four × Four) :=
  coordLinearEquiv.trans
    (ZornPolarizationMetricBridge.nullFourSplit.trans
      (signedFourCoordinates.prodCongr signedFourCoordinates))

@[simp] theorem wittCoordinates_apply (z : ZornMatrix ℝ) :
    wittCoordinates z =
      (![z.a, -z.x 0, -z.x 1, -z.x 2],
        ![z.b, z.y 0, z.y 1, z.y 2]) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [wittCoordinates, signedFourCoordinates,
      ZornPolarizationMetricBridge.nullFourSplit,
      ZornVectorMatrixExplicit.zornA, ZornVectorMatrixExplicit.zornB,
      ZornVectorMatrixExplicit.zornX, ZornVectorMatrixExplicit.zornY]

@[simp] theorem wittCoordinates_symm_apply (q p : Four) :
    wittCoordinates.symm (q, p) =
      ⟨q 0, p 0, -![q 1, q 2, q 3], ![p 1, p 2, p 3]⟩ := by
  apply wittCoordinates.injective
  rw [wittCoordinates.apply_symm_apply, wittCoordinates_apply]
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp

/-- The native duality equivalence associated with the standard finite basis. -/
def coordinateDual : Four ≃ₗ[ℝ] Module.Dual ℝ Four :=
  (Pi.basisFun ℝ (Fin 4)).toDualEquiv

theorem coordinateDual_apply (p q : Four) :
    coordinateDual p q = ∑ i : Fin 4, p i * q i := by
  have h := (Pi.basisFun ℝ (Fin 4)).sum_dual_apply_smul_coord (coordinateDual p)
  have hq := congrArg (fun f : Module.Dual ℝ Four => f q) h
  simpa only [coordinateDual, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.Basis.toDualEquiv_apply, Module.Basis.toDual_apply_left, Module.Basis.coord_apply,
    Pi.basisFun_repr, smul_eq_mul] using hq.symm

theorem coordinateDual_symm (p q : Four) :
    coordinateDual p q = coordinateDual q p := by
  rw [coordinateDual_apply, coordinateDual_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- The canonical Zorn carrier as an actual vector-plus-algebraic-dual carrier. -/
def neutralCoordinates : ZornMatrix ℝ ≃ₗ[ℝ] PhaseSpaceCarrier Four :=
  wittCoordinates.trans ((LinearEquiv.refl ℝ Four).prodCongr coordinateDual)

@[simp] theorem neutralCoordinates_apply (z : ZornMatrix ℝ) :
    neutralCoordinates z =
      ((wittCoordinates z).1, coordinateDual (wittCoordinates z).2) := rfl

/-- The existing Zorn norm becomes evaluation, with no factor two. -/
theorem norm_eq_evaluation (z : ZornMatrix ℝ) :
    zornNorm z = coordinateDual (wittCoordinates z).2 (wittCoordinates z).1 := by
  calc
    zornNorm z = ZornVectorMatrixExplicit.zornNorm (coordLinearEquiv z) := rfl
    _ = (ZornPolarizationMetricBridge.nullFourSplit (coordLinearEquiv z)).1.1 *
          (ZornPolarizationMetricBridge.nullFourSplit (coordLinearEquiv z)).2.1 +
        ZornVectorMatrixExplicit.dot3
          (ZornPolarizationMetricBridge.nullFourSplit (coordLinearEquiv z)).1.2
          (ZornPolarizationMetricBridge.nullFourSplit (coordLinearEquiv z)).2.2 :=
      ZornPolarizationMetricBridge.norm_in_nullFourSplit _
    _ = coordinateDual (wittCoordinates z).2 (wittCoordinates z).1 := by
      rw [coordinateDual_apply, wittCoordinates_apply]
      simp [ZornPolarizationMetricBridge.nullFourSplit,
        ZornVectorMatrixExplicit.dot3,
        ZornVectorMatrixExplicit.zornA, ZornVectorMatrixExplicit.zornB,
        ZornVectorMatrixExplicit.zornX, ZornVectorMatrixExplicit.zornY,
        Fin.sum_univ_succ]
      ring

theorem neutralCoordinates_preserves_form (z : ZornMatrix ℝ) :
    canonicalNeutralFormUnscaled (neutralCoordinates z) = zornNorm z := by
  rw [canonicalNeutralFormUnscaled_apply, neutralCoordinates_apply]
  exact (norm_eq_evaluation z).symm

/-- The linear coordinate equivalence is a quadratic isometry. -/
def zornNeutralIsometry :
    (zornNorm (R := ℝ)).IsometryEquiv
      (canonicalNeutralFormUnscaled (E := Four)) where
  toLinearEquiv := neutralCoordinates
  map_app' := neutralCoordinates_preserves_form

/-- The primal null plane, bundled using the native product inclusion. -/
def primalInclusion : Four →ₗ[ℝ] ZornMatrix ℝ :=
  wittCoordinates.symm.toLinearMap.comp (LinearMap.inl ℝ Four Four)

/-- The dual null plane uses signed-ladder coefficients, not raw lower coordinates. -/
def dualInclusion : Four →ₗ[ℝ] ZornMatrix ℝ :=
  wittCoordinates.symm.toLinearMap.comp (LinearMap.inr ℝ Four Four)

@[simp] theorem wittCoordinates_primalInclusion (q : Four) :
    wittCoordinates (primalInclusion q) = (q, 0) := by
  exact wittCoordinates.apply_symm_apply (q, 0)

@[simp] theorem wittCoordinates_dualInclusion (p : Four) :
    wittCoordinates (dualInclusion p) = (0, p) := by
  exact wittCoordinates.apply_symm_apply (0, p)

@[simp] theorem primalInclusion_coordinates (q : Four) :
    primalInclusion q = ⟨q 0, 0, -![q 1, q 2, q 3], 0⟩ := by
  change wittCoordinates.symm (q, 0) = _
  rw [wittCoordinates_symm_apply]
  apply ZornMatrix.ext
  · rfl
  · rfl
  · rfl
  · funext i
    fin_cases i <;> simp

@[simp] theorem dualInclusion_coordinates (p : Four) :
    dualInclusion p = ⟨0, p 0, 0, ![p 1, p 2, p 3]⟩ := by
  change wittCoordinates.symm (0, p) = _
  rw [wittCoordinates_symm_apply]
  apply ZornMatrix.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> simp
  · rfl

/-- The first null inclusion agrees with the previously audited primal vector. -/
theorem primalInclusion_eq_primal (q : Four) :
    primalInclusion q = ZornSignedConvention.primal q := by
  rw [primalInclusion_coordinates]
  apply ZornMatrix.ext <;>
    simp [ZornSignedConvention.primal, ZornSignedConvention.signedCoordinates]

/-- Raw lower coordinates and coefficients of the signed lower ladders differ spatially. -/
theorem dualInclusion_eq_raw_dual (p : Four) :
    dualInclusion p = ZornSignedConvention.dual ![p 0, -p 1, -p 2, -p 3] := by
  rw [dualInclusion_coordinates]
  apply ZornMatrix.ext
  · rfl
  · rfl
  · simp [ZornSignedConvention.dual, ZornSignedConvention.signedCoordinates]
  · funext i
    fin_cases i <;>
      simp [ZornSignedConvention.dual, ZornSignedConvention.signedCoordinates]

theorem primal_dual_decomposition (z : ZornMatrix ℝ) :
    primalInclusion (wittCoordinates z).1 +
      dualInclusion (wittCoordinates z).2 = z := by
  apply wittCoordinates.injective
  rw [map_add, wittCoordinates_primalInclusion, wittCoordinates_dualInclusion]
  exact Prod.ext (add_zero _) (zero_add _)

theorem primalInclusion_injective : Function.Injective primalInclusion := by
  intro q r h
  simpa only [wittCoordinates_primalInclusion] using
    congrArg (fun z : ZornMatrix ℝ => (wittCoordinates z).1) h

theorem dualInclusion_injective : Function.Injective dualInclusion := by
  intro p r h
  simpa only [wittCoordinates_dualInclusion] using
    congrArg (fun z : ZornMatrix ℝ => (wittCoordinates z).2) h

def primalSubspace : Submodule ℝ (ZornMatrix ℝ) := LinearMap.range primalInclusion

def dualSubspace : Submodule ℝ (ZornMatrix ℝ) := LinearMap.range dualInclusion

theorem primal_dual_isCompl : IsCompl primalSubspace dualSubspace := by
  have h : IsCompl (LinearMap.range (LinearMap.inl ℝ Four Four))
      (LinearMap.range (LinearMap.inr ℝ Four Four)) :=
    LinearMap.isCompl_range_inl_inr
  have hm := (Submodule.orderIsoMapComap wittCoordinates.symm).isCompl h
  change IsCompl
    ((LinearMap.range (LinearMap.inl ℝ Four Four)).map wittCoordinates.symm.toLinearMap)
    ((LinearMap.range (LinearMap.inr ℝ Four Four)).map wittCoordinates.symm.toLinearMap) at hm
  simpa only [primalSubspace, dualSubspace, primalInclusion, dualInclusion,
    LinearMap.range_comp] using hm

theorem primalSubspace_finrank : Module.finrank ℝ primalSubspace = 4 := by
  change Module.finrank ℝ (LinearMap.range primalInclusion) = 4
  rw [LinearMap.finrank_range_of_inj primalInclusion_injective]
  simp [Four, InfoGeometry.Algebra.FiniteSpin.Vec4R]

theorem dualSubspace_finrank : Module.finrank ℝ dualSubspace = 4 := by
  change Module.finrank ℝ (LinearMap.range dualInclusion) = 4
  rw [LinearMap.finrank_range_of_inj dualInclusion_injective]
  simp [Four, InfoGeometry.Algebra.FiniteSpin.Vec4R]

@[simp] theorem norm_primalInclusion (q : Four) : zornNorm (primalInclusion q) = 0 := by
  rw [norm_eq_evaluation, wittCoordinates_primalInclusion]
  simp

@[simp] theorem norm_dualInclusion (p : Four) : zornNorm (dualInclusion p) = 0 := by
  rw [norm_eq_evaluation, wittCoordinates_dualInclusion]
  simp

theorem primalSubspace_isotropic (z : ZornMatrix ℝ) (hz : z ∈ primalSubspace) :
    zornNorm z = 0 := by
  rcases hz with ⟨q, rfl⟩
  exact norm_primalInclusion q

theorem dualSubspace_isotropic (z : ZornMatrix ℝ) (hz : z ∈ dualSubspace) :
    zornNorm z = 0 := by
  rcases hz with ⟨p, rfl⟩
  exact norm_dualInclusion p

theorem primal_pairing_zero (q r : Four) :
    zornBilin (primalInclusion q) (primalInclusion r) = 0 := by
  rw [zornBilin_apply, primalInclusion_coordinates, primalInclusion_coordinates]
  simp [dot]

theorem dual_pairing_zero (p r : Four) :
    zornBilin (dualInclusion p) (dualInclusion r) = 0 := by
  rw [zornBilin_apply, dualInclusion_coordinates, dualInclusion_coordinates]
  simp [dot]

theorem mixed_pairing (q p : Four) :
    2 * zornBilin (primalInclusion q) (dualInclusion p) = coordinateDual p q := by
  rw [zornBilin_apply, primalInclusion_coordinates, dualInclusion_coordinates,
    coordinateDual_apply]
  simp [dot, Fin.sum_univ_succ]
  ring

/-- The true doubled Clifford operators for the primal labels. -/
def gammaPrimal : Four →ₗ[ℝ] Module.End ℝ (DiracSpinor16 (R := ℝ)) :=
  diracGammaLinear.comp primalInclusion

/-- The true doubled Clifford operators for the dual labels. -/
def gammaDual : Four →ₗ[ℝ] Module.End ℝ (DiracSpinor16 (R := ℝ)) :=
  diracGammaLinear.comp dualInclusion

@[simp] theorem gammaPrimal_apply (q : Four) :
    gammaPrimal q = diracGamma (primalInclusion q) := rfl

@[simp] theorem gammaDual_apply (p : Four) :
    gammaDual p = diracGamma (dualInclusion p) := rfl

theorem gammaPrimal_sq (q : Four) : gammaPrimal q * gammaPrimal q = 0 := by
  rw [gammaPrimal_apply, diracGamma_square, norm_primalInclusion, zero_smul]

theorem gammaDual_sq (p : Four) : gammaDual p * gammaDual p = 0 := by
  rw [gammaDual_apply, diracGamma_square, norm_dualInclusion, zero_smul]

theorem gammaPrimal_anticommute (q r : Four) :
    gammaPrimal q * gammaPrimal r + gammaPrimal r * gammaPrimal q = 0 := by
  simp only [gammaPrimal_apply, diracGamma_anticommutator, primal_pairing_zero,
    mul_zero, zero_smul]

theorem gammaDual_anticommute (p r : Four) :
    gammaDual p * gammaDual r + gammaDual r * gammaDual p = 0 := by
  simp only [gammaDual_apply, diracGamma_anticommutator, dual_pairing_zero,
    mul_zero, zero_smul]

/-- Mixed CAR with evaluation coefficient, as required by `Q(q,p) = p(q)`. -/
theorem gamma_mixed_CAR (q p : Four) :
    gammaPrimal q * gammaDual p + gammaDual p * gammaPrimal q =
      coordinateDual p q • (1 : Module.End ℝ (DiracSpinor16 (R := ℝ))) := by
  simpa only [gammaPrimal_apply, gammaDual_apply, mixed_pairing] using
    diracGamma_anticommutator (primalInclusion q) (dualInclusion p)

/-- The standard four primal/dual pairs have coefficient `δᵢⱼ`, not `2δᵢⱼ`. -/
theorem gamma_basis_mixed_CAR (i j : Fin 4) :
    gammaPrimal (Pi.basisFun ℝ (Fin 4) i) * gammaDual (Pi.basisFun ℝ (Fin 4) j) +
      gammaDual (Pi.basisFun ℝ (Fin 4) j) * gammaPrimal (Pi.basisFun ℝ (Fin 4) i) =
      (if i = j then (1 : ℝ) else 0) •
        (1 : Module.End ℝ (DiracSpinor16 (R := ℝ))) := by
  rw [gamma_mixed_CAR]
  simp only [coordinateDual, Module.Basis.toDualEquiv_apply,
    Module.Basis.toDual_apply, eq_comm]

/-- The existing fundamental symmetry transported to the canonical Zorn carrier. -/
def reciprocity : ZornMatrix ℝ ≃ₗ[ℝ] ZornMatrix ℝ :=
  coordLinearEquiv.trans
    (ZornPolarizationMetricBridge.fundamental.trans coordLinearEquiv.symm)

@[simp] theorem reciprocity_apply (z : ZornMatrix ℝ) :
    reciprocity z = ⟨z.b, z.a, -z.y, -z.x⟩ := rfl

theorem wittCoordinates_reciprocity (z : ZornMatrix ℝ) :
    wittCoordinates (reciprocity z) = ((wittCoordinates z).2, (wittCoordinates z).1) := by
  simp [wittCoordinates_apply, reciprocity_apply]

theorem reciprocity_sq (z : ZornMatrix ℝ) : reciprocity (reciprocity z) = z := by
  apply coordLinearEquiv.injective
  change ZornPolarizationMetricBridge.fundamental
      (ZornPolarizationMetricBridge.fundamental (coordLinearEquiv z)) = coordLinearEquiv z
  exact ZornPolarizationMetricBridge.fundamental_sq _

theorem reciprocity_preserves_norm (z : ZornMatrix ℝ) :
    zornNorm (reciprocity z) = zornNorm z := by
  change ZornVectorMatrixExplicit.zornNorm
      (ZornPolarizationMetricBridge.fundamental (coordLinearEquiv z)) =
    ZornVectorMatrixExplicit.zornNorm (coordLinearEquiv z)
  exact ZornPolarizationMetricBridge.fundamental_norm _

/-- Multiplicativity is transported from the existing coordinate symmetry. -/
theorem reciprocity_mul (z w : ZornMatrix ℝ) :
    reciprocity (z * w) = reciprocity z * reciprocity w := by
  apply coordLinearEquiv.injective
  change ZornPolarizationMetricBridge.fundamental
      (ZornVectorMatrixExplicit.zornMul (coordLinearEquiv z) (coordLinearEquiv w)) =
    ZornVectorMatrixExplicit.zornMul
      (ZornPolarizationMetricBridge.fundamental (coordLinearEquiv z))
      (ZornPolarizationMetricBridge.fundamental (coordLinearEquiv w))
  exact ZornPolarizationMetricBridge.fundamental_mul _ _

/-- Pull back the native evaluation skew form to the canonical Zorn carrier. -/
def zornOmega : LinearMap.BilinForm ℝ (ZornMatrix ℝ) :=
  (neutralOmega (E := Four)).compl₁₂ neutralCoordinates.toLinearMap
    neutralCoordinates.toLinearMap

theorem zornOmega_apply (z w : ZornMatrix ℝ) :
    zornOmega z w =
      coordinateDual (wittCoordinates w).2 (wittCoordinates z).1 -
        coordinateDual (wittCoordinates z).2 (wittCoordinates w).1 := by
  exact neutralOmega_apply (neutralCoordinates z) (neutralCoordinates w)

/-- Unsigned exchange reverses the canonical skew form. -/
theorem reciprocity_reverses_omega (z w : ZornMatrix ℝ) :
    zornOmega (reciprocity z) (reciprocity w) = -zornOmega z w := by
  simp only [zornOmega_apply, wittCoordinates_reciprocity]
  rw [coordinateDual_symm (wittCoordinates w).1 (wittCoordinates z).2,
    coordinateDual_symm (wittCoordinates z).1 (wittCoordinates w).2]
  ring

/-- The signed Born quarter-turn `(q,p) ↦ (p,-q)` in the same native splitting. -/
def bornQuarterTurn : ZornMatrix ℝ ≃ₗ[ℝ] ZornMatrix ℝ :=
  wittCoordinates.trans
    ((LinearEquiv.prodComm ℝ Four Four).trans
      (((LinearEquiv.refl ℝ Four).prodCongr (LinearEquiv.neg ℝ)).trans
        wittCoordinates.symm))

theorem wittCoordinates_bornQuarterTurn (z : ZornMatrix ℝ) :
    wittCoordinates (bornQuarterTurn z) =
      ((wittCoordinates z).2, -(wittCoordinates z).1) := by
  change wittCoordinates
      (wittCoordinates.symm ((wittCoordinates z).2, -(wittCoordinates z).1)) = _
  exact wittCoordinates.apply_symm_apply _

/-- The quarter-turn is the unsigned exchange followed by the native para-involution. -/
theorem neutralCoordinates_bornQuarterTurn (z : ZornMatrix ℝ) :
    neutralCoordinates (bornQuarterTurn z) =
      neutralParaInvolution (neutralCoordinates (reciprocity z)) := by
  simp only [neutralCoordinates_apply, wittCoordinates_bornQuarterTurn,
    neutralParaInvolution_apply, wittCoordinates_reciprocity, map_neg]

theorem bornQuarterTurn_sq (z : ZornMatrix ℝ) :
    bornQuarterTurn (bornQuarterTurn z) = -z := by
  apply wittCoordinates.injective
  rw [wittCoordinates_bornQuarterTurn, wittCoordinates_bornQuarterTurn, map_neg]
  exact Prod.ext rfl rfl

theorem bornQuarterTurn_reverses_norm (z : ZornMatrix ℝ) :
    zornNorm (bornQuarterTurn z) = -zornNorm z := by
  calc
    zornNorm (bornQuarterTurn z) =
        coordinateDual (-(wittCoordinates z).1) (wittCoordinates z).2 := by
      rw [norm_eq_evaluation, wittCoordinates_bornQuarterTurn]
    _ = -coordinateDual (wittCoordinates z).1 (wittCoordinates z).2 := by
      rw [map_neg, LinearMap.neg_apply]
    _ = -coordinateDual (wittCoordinates z).2 (wittCoordinates z).1 := by
      rw [coordinateDual_symm]
    _ = -zornNorm z := by rw [norm_eq_evaluation]

theorem bornQuarterTurn_preserves_omega (z w : ZornMatrix ℝ) :
    zornOmega (bornQuarterTurn z) (bornQuarterTurn w) = zornOmega z w := by
  simp only [zornOmega_apply, wittCoordinates_bornQuarterTurn,
    map_neg, LinearMap.neg_apply]
  rw [coordinateDual_symm (wittCoordinates w).1 (wittCoordinates z).2,
    coordinateDual_symm (wittCoordinates z).1 (wittCoordinates w).2]
  ring

end InfoGeometry.Canonical.ZornCl44PrimalDual
