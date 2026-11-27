/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GradedCliffordOperatorRepresentation
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.NormNum

/-!
# The algebraic Atiyah--Bott--Shapiro symbol

For a real graded Clifford representation, the grading eigenspaces are the
actual even and odd submodules. Clifford multiplication exchanges them.
Whenever `Q v ≠ 0`, multiplication by `-v` defines a linear equivalence from
the odd submodule to the even submodule. Its inverse is multiplication by
`-(Q v)⁻¹ • v`; in particular, the inverse is multiplication by `v` when
`Q v = -1`.

This is the fiberwise algebraic construction in Atiyah--Bott--Shapiro,
*Clifford Modules*, §11, printed page 25. Continuity, vector bundles, relative
K-theory, and the ABS comparison isomorphism are separate constructions.
The hypothesis uses the quadratic value, so it also states the correct
boundary for indefinite forms with nonzero null vectors.
-/

noncomputable section

namespace InfoGeometry.Canonical.AtiyahBottShapiroSymbol

open CliffordAlgebra
open PinOperatorFamilyBridge

variable {M W : Type*}
variable [AddCommGroup M] [Module ℝ M] [AddCommGroup W] [Module ℝ W]
variable {Q : QuadraticForm ℝ M}
variable (ρ : GradedCliffordOperatorRepresentation
  (R := ℝ) (M := M) (W := W) (Q := Q))

/-- The even part is the actual `+1` eigenspace of the grading. -/
abbrev evenSpace : Submodule ℝ W := ρ.grading.eigenspace (1 : ℝ)

/-- The odd part is the actual `-1` eigenspace of the grading. -/
abbrev oddSpace : Submodule ℝ W := ρ.grading.eigenspace (-1 : ℝ)

@[simp] theorem mem_evenSpace_iff (w : W) :
    w ∈ evenSpace ρ ↔ ρ.grading w = w := by
  simp [evenSpace]

@[simp] theorem mem_oddSpace_iff (w : W) :
    w ∈ oddSpace ρ ↔ ρ.grading w = -w := by
  simp [oddSpace]

/-- Over the reals, an involutive grading gives complementary even and odd submodules. -/
theorem isCompl_evenSpace_oddSpace : IsCompl (evenSpace ρ) (oddSpace ρ) := by
  constructor
  · exact ρ.grading.disjoint_genEigenspace (by norm_num : (1 : ℝ) ≠ -1) 1 1
  · rw [codisjoint_iff_le_sup]
    intro w _
    apply Submodule.mem_sup.mpr
    refine ⟨(2 : ℝ)⁻¹ • (w + ρ.grading w), ?_,
      (2 : ℝ)⁻¹ • (w - ρ.grading w), ?_, ?_⟩
    · rw [mem_evenSpace_iff]
      simp only [map_smul, map_add, ρ.grading_grading_apply, add_comm]
    · rw [mem_oddSpace_iff]
      simp only [map_smul, map_sub, ρ.grading_grading_apply, smul_sub]
      abel
    · calc
        (2 : ℝ)⁻¹ • (w + ρ.grading w) + (2 : ℝ)⁻¹ • (w - ρ.grading w) =
            (2 : ℝ)⁻¹ • ((w + ρ.grading w) + (w - ρ.grading w)) :=
          (smul_add _ _ _).symm
        _ = (2 : ℝ)⁻¹ • ((2 : ℝ) • w) := by
          congr 1
          rw [two_smul]
          abel
        _ = w := by norm_num [smul_smul]

/-- The carrier is the product of its actual grading submodules. -/
def gradingDecomposition : W ≃ₗ[ℝ] evenSpace ρ × oddSpace ρ :=
  (Submodule.prodEquivOfIsCompl (evenSpace ρ) (oddSpace ρ)
    (isCompl_evenSpace_oddSpace ρ)).symm

/-- Recombining the grading components is ordinary vector addition. -/
@[simp] theorem gradingDecomposition_symm_apply (w : evenSpace ρ × oddSpace ρ) :
    (gradingDecomposition ρ).symm w = (w.1 : W) + (w.2 : W) := rfl

/-- The operator square is derived from the native Clifford relation. -/
theorem generator_sq_apply (v : M) (w : W) :
    ρ.representation (ι Q v) (ρ.representation (ι Q v) w) = Q v • w := by
  simpa only [Module.End.mul_apply, Algebra.algebraMap_eq_smul_one,
    LinearMap.smul_apply, Module.End.one_apply] using
    congrArg (fun T : Module.End ℝ W => T w)
      (CliffordAlgebra.comp_ι_sq_scalar ρ.representation v)

/-- Pointwise oddness is a specialization of the proved full covariance. -/
theorem grading_generator_apply (v : M) (w : W) :
    ρ.grading (ρ.representation (ι Q v) w) =
      -(ρ.representation (ι Q v) (ρ.grading w)) := by
  simpa only [CliffordAlgebra.involute_ι, map_neg, LinearMap.neg_apply] using
    ρ.grading_representation_apply (ι Q v) w

/-- A Clifford vector takes odd vectors to the even submodule. -/
theorem generator_mem_evenSpace (v : M) {w : W} (hw : w ∈ oddSpace ρ) :
    ρ.representation (ι Q v) w ∈ evenSpace ρ := by
  rw [mem_evenSpace_iff, grading_generator_apply,
    (mem_oddSpace_iff ρ w).mp hw, map_neg, neg_neg]

/-- A Clifford vector takes even vectors to the odd submodule. -/
theorem generator_mem_oddSpace (v : M) {w : W} (hw : w ∈ evenSpace ρ) :
    ρ.representation (ι Q v) w ∈ oddSpace ρ := by
  rw [mem_oddSpace_iff, grading_generator_apply,
    (mem_evenSpace_iff ρ w).mp hw]

/-- The ABS sign convention: multiplication by `-v`, from odd to even. -/
def symbol (v : M) : oddSpace ρ →ₗ[ℝ] evenSpace ρ where
  toFun w := ⟨-(ρ.representation (ι Q v) w),
    (evenSpace ρ).neg_mem (generator_mem_evenSpace ρ v w.property)⟩
  map_add' w z := by
    apply Subtype.ext
    exact (-ρ.representation (ι Q v)).map_add w z
  map_smul' r w := by
    apply Subtype.ext
    exact (-ρ.representation (ι Q v)).map_smul r w

@[simp] theorem symbol_apply (v : M) (w : oddSpace ρ) :
    (symbol ρ v w : W) = -(ρ.representation (ι Q v) w) := rfl

/-- The reverse linear map, with the quadratic normalization required for an inverse. -/
def inverseSymbol (v : M) : evenSpace ρ →ₗ[ℝ] oddSpace ρ where
  toFun w := ⟨-(Q v)⁻¹ • ρ.representation (ι Q v) w,
    (oddSpace ρ).smul_mem _ (generator_mem_oddSpace ρ v w.property)⟩
  map_add' w z := by
    apply Subtype.ext
    exact (-(Q v)⁻¹ • ρ.representation (ι Q v)).map_add w z
  map_smul' r w := by
    apply Subtype.ext
    exact (-(Q v)⁻¹ • ρ.representation (ι Q v)).map_smul r w

@[simp] theorem inverseSymbol_apply (v : M) (w : evenSpace ρ) :
    (inverseSymbol ρ v w : W) = -(Q v)⁻¹ • ρ.representation (ι Q v) w := rfl

/-- The two sign-sensitive maps compose to the identity on the odd part. -/
theorem inverseSymbol_symbol (v : M) (hv : Q v ≠ 0) (w : oddSpace ρ) :
    inverseSymbol ρ v (symbol ρ v w) = w := by
  apply Subtype.ext
  change -(Q v)⁻¹ • ρ.representation (ι Q v) (-(ρ.representation (ι Q v) w)) = w
  rw [map_neg, neg_smul_neg, generator_sq_apply, smul_smul, inv_mul_cancel₀ hv, one_smul]

/-- The two sign-sensitive maps compose to the identity on the even part. -/
theorem symbol_inverseSymbol (v : M) (hv : Q v ≠ 0) (w : evenSpace ρ) :
    symbol ρ v (inverseSymbol ρ v w) = w := by
  apply Subtype.ext
  change -(ρ.representation (ι Q v) (-(Q v)⁻¹ • ρ.representation (ι Q v) w)) = w
  rw [map_smul, neg_smul, neg_neg, generator_sq_apply,
    smul_smul, inv_mul_cancel₀ hv, one_smul]

/-- The actual ABS linear equivalence at every vector of nonzero quadratic value. -/
def symbolEquiv (v : M) (hv : Q v ≠ 0) : oddSpace ρ ≃ₗ[ℝ] evenSpace ρ where
  toLinearMap := symbol ρ v
  invFun := inverseSymbol ρ v
  left_inv := inverseSymbol_symbol ρ v hv
  right_inv := symbol_inverseSymbol ρ v hv

@[simp] theorem symbolEquiv_apply (v : M) (hv : Q v ≠ 0) (w : oddSpace ρ) :
    (symbolEquiv ρ v hv w : W) = -(ρ.representation (ι Q v) w) := rfl

@[simp] theorem symbolEquiv_symm_apply (v : M) (hv : Q v ≠ 0) (w : evenSpace ρ) :
    ((symbolEquiv ρ v hv).symm w : W) =
      -(Q v)⁻¹ • ρ.representation (ι Q v) w := rfl

/-- On the negative unit sphere, the inverse has the opposite sign to the symbol. -/
theorem symbolEquiv_symm_apply_of_neg_one (v : M) (hv : Q v ≠ 0)
    (hunit : Q v = -1) (w : evenSpace ρ) :
    ((symbolEquiv ρ v hv).symm w : W) = ρ.representation (ι Q v) w := by
  simp [hunit]

/-- For an anisotropic form, every nonzero vector supplies the symbol equivalence. -/
def symbolEquivOfAnisotropic (hQ : Q.Anisotropic) (v : M) (hv : v ≠ 0) :
    oddSpace ρ ≃ₗ[ℝ] evenSpace ρ :=
  symbolEquiv ρ v (fun h => hv (hQ v h))

/-- A non-null Clifford vector pairs the two finite grading dimensions. -/
theorem finrank_oddSpace_eq_evenSpace [FiniteDimensional ℝ W]
    (v : M) (hv : Q v ≠ 0) :
    Module.finrank ℝ (oddSpace ρ) = Module.finrank ℝ (evenSpace ρ) :=
  (symbolEquiv ρ v hv).finrank_eq

end InfoGeometry.Canonical.AtiyahBottShapiroSymbol
