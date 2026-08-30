import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationExponential
import InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Algebra.Zorn.Basic
import InfoGeometry.Canonical.SplitOctonionAutomorphism

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationExponential
open InfoGeometry.Lie.CanonicalZornDerivationOneParameterGroup
open InfoGeometry.Canonical
open InfoGeometry.Algebra.Zorn

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ

lemma one_a : (1 : CZ).a = 1 := rfl
lemma one_b : (1 : CZ).b = 1 := rfl
lemma one_x (i : Fin 3) : (1 : CZ).x i = 0 := rfl
lemma one_y (i : Fin 3) : (1 : CZ).y i = 0 := rfl

theorem zorn_mul_one (Z : CZ) : Z * 1 = Z := by
  apply ZornMatrix.ext
  · simp [ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot, one_a, one_b, one_x, one_y]
  · simp [ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot, one_a, one_b, one_x, one_y]
  · ext i; fin_cases i <;> simp [ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.cross, one_a, one_b, one_x, one_y]
  · ext i; fin_cases i <;> simp [ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.cross, one_a, one_b, one_x, one_y]

theorem zorn_one_mul (Z : CZ) : 1 * Z = Z := by
  apply ZornMatrix.ext
  · simp [ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot, one_a, one_b, one_x, one_y]
  · simp [ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot, one_a, one_b, one_x, one_y]
  · ext i; fin_cases i <;> simp [ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.cross, one_a, one_b, one_x, one_y]
  · ext i; fin_cases i <;> simp [ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.cross, one_a, one_b, one_x, one_y]

/-- Every derivation exponential fixes the Zorn multiplicative unit. -/
@[simp]
theorem zornFlow_fixes_one
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowLinearEquiv D.1 t (1 : CZ) = 1 := by
  have h_mul := zornFlow_map_mul D.1 D.2 t ((zornFlowLinearEquiv D.1 t).symm (1 : CZ)) (1 : CZ)
  rw [LinearEquiv.apply_symm_apply] at h_mul
  rw [zorn_mul_one] at h_mul
  rw [LinearEquiv.apply_symm_apply] at h_mul
  have h_one : (1 : CZ) = (1 : CZ) * zornFlowLinearEquiv D.1 t (1 : CZ) := h_mul
  rw [zorn_one_mul] at h_one
  exact h_one.symm

/--
The exponential flow of a canonical Zorn derivation, regarded as an element
of the repository-owned native real split-octonion automorphism group.
-/
noncomputable def zornFlowRealAut
    (D : canonicalZornDerivations)
    (t : ℝ) : RealSplitOctonionAut :=
  ⟨zornFlowLinearEquiv D.1 t, by
    constructor
    · -- Preserves the unit
      exact zornFlow_fixes_one D t
    · -- Preserves multiplication
      intro X Y
      exact zornFlow_map_mul D.1 D.2 t X Y⟩

/-- The underlying linear equivalence is exactly the exponential Zorn flow. -/
@[simp]
theorem zornFlowRealAut_coe
    (D : canonicalZornDerivations)
    (t : ℝ) :
    ((zornFlowRealAut D t : RealSplitOctonionAut) :
      SplitOctonionAutCandidate ℝ) =
      zornFlowLinearEquiv D.1 t := by
  rfl

/-- Pointwise readback of the native automorphism into the exponential flow. -/
@[simp]
theorem zornFlowRealAut_apply
    (D : canonicalZornDerivations)
    (t : ℝ)
    (X : CZ) :
    ((zornFlowRealAut D t : RealSplitOctonionAut) :
      SplitOctonionAutCandidate ℝ) X =
      zornFlowLinearEquiv D.1 t X := by
  rfl

/-- Every derivation exponential preserves the full nonassociative Zorn product. -/
theorem zornFlow_preserves_mul
    (D : canonicalZornDerivations)
    (t : ℝ)
    (X Y : CZ) :
    zornFlowLinearEquiv D.1 t (X * Y) =
      zornFlowLinearEquiv D.1 t X *
        zornFlowLinearEquiv D.1 t Y := by
  exact zornFlow_map_mul D.1 D.2 t X Y

/--
The exponential of every canonical derivation lands in the exact native
real split-octonion automorphism subgroup.
-/
theorem canonical_derivation_exponential_lands_in_realAut
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowLinearEquiv D.1 t ∈
      splitOctonionAutSubgroup (R := ℝ) := by
  exact (zornFlowRealAut D t).property

/-!
## Invariant consequences
-/

/-- The finite derivation flow preserves the canonical Zorn determinant. -/
@[simp]
theorem zornFlow_preserves_detZ
    (D : canonicalZornDerivations)
    (t : ℝ)
    (X : CZ) :
    ZornMatrix.detZ (zornFlowLinearEquiv D.1 t X) =
      ZornMatrix.detZ X := by
  simpa using
    (RealSplitOctonionAut.preserves_detZ (zornFlowRealAut D t) X)

/-- The finite derivation flow preserves the canonical split null cone. -/
@[simp]
theorem zornFlow_preserves_null
    (D : canonicalZornDerivations)
    (t : ℝ)
    (X : CZ) :
    ZornMatrix.IsNull (zornFlowLinearEquiv D.1 t X) ↔
      ZornMatrix.IsNull X := by
  simpa using
    (RealSplitOctonionAut.preserves_null (zornFlowRealAut D t) X)

/-!
## One-parameter group in the native real automorphism group
-/

/-- Time zero gives the identity native real split-octonion automorphism. -/
@[simp]
theorem zornFlowRealAut_zero
    (D : canonicalZornDerivations) :
    zornFlowRealAut D 0 = (1 : RealSplitOctonionAut) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change zornFlowLinearEquiv D.1 0 X = X
  exact zornFlowLinearEquiv_zero_apply D.1 X

/--
The native real automorphism flow satisfies the additive time-composition law.
-/
theorem zornFlowRealAut_add
    (D : canonicalZornDerivations)
    (s t : ℝ) :
    zornFlowRealAut D (s + t) =
      zornFlowRealAut D s * zornFlowRealAut D t := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change
    zornFlowLinearEquiv D.1 (s + t) X =
      zornFlowLinearEquiv D.1 s
        (zornFlowLinearEquiv D.1 t X)
  exact zornFlow_add_apply D s t X

/-- Negative time is the inverse in the native real automorphism group. -/
@[simp]
theorem zornFlowRealAut_neg
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowRealAut D (-t) =
      (zornFlowRealAut D t)⁻¹ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change (zornFlowLinearEquiv D.1 (-t)) X = (zornFlowLinearEquiv D.1 t).symm X
  apply (zornFlowLinearEquiv D.1 t).injective
  rw [LinearEquiv.apply_symm_apply]
  exact zornFlow_apply_neg_flow D t X

/--
The canonical derivation exponential as a genuine one-parameter subgroup of
the repository-owned native real split-octonion automorphism group.
-/
noncomputable def zornFlowRealAutGroupHom
    (D : canonicalZornDerivations) :
    Multiplicative ℝ →* RealSplitOctonionAut where
  toFun τ := zornFlowRealAut D τ.toAdd
  map_one' := zornFlowRealAut_zero D
  map_mul' σ τ := zornFlowRealAut_add D σ.toAdd τ.toAdd

@[simp]
theorem zornFlowRealAutGroupHom_apply
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowRealAutGroupHom D (Multiplicative.ofAdd t) =
      zornFlowRealAut D t := by
  rfl

/-- Zero time maps to the identity automorphism. -/
@[simp]
theorem zornFlowRealAutGroupHom_zero
    (D : canonicalZornDerivations) :
    zornFlowRealAutGroupHom D (Multiplicative.ofAdd 0) = 1 := by
  exact map_one (zornFlowRealAutGroupHom D)

/-- Additive time becomes composition in the native automorphism group. -/
theorem zornFlowRealAutGroupHom_add
    (D : canonicalZornDerivations)
    (s t : ℝ) :
    zornFlowRealAutGroupHom D (Multiplicative.ofAdd (s + t)) =
      zornFlowRealAutGroupHom D (Multiplicative.ofAdd s) *
        zornFlowRealAutGroupHom D (Multiplicative.ofAdd t) := by
  exact map_mul (zornFlowRealAutGroupHom D)
    (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)

/-- Negative time becomes the group inverse. -/
@[simp]
theorem zornFlowRealAutGroupHom_neg
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowRealAutGroupHom D (Multiplicative.ofAdd (-t)) =
      (zornFlowRealAutGroupHom D (Multiplicative.ofAdd t))⁻¹ := by
  exact map_inv (zornFlowRealAutGroupHom D) (Multiplicative.ofAdd t)

/-!
## Time-one exponential and complete packet
-/

/-- The time-one derivation exponential in the native real automorphism group. -/
noncomputable def zornDerivationExpRealAut
    (D : canonicalZornDerivations) :
    RealSplitOctonionAut :=
  zornFlowRealAut D 1

theorem zornDerivationExpRealAut_apply
    (D : canonicalZornDerivations)
    (X : CZ) :
    ((zornDerivationExpRealAut D : RealSplitOctonionAut) :
      SplitOctonionAutCandidate ℝ) X =
      (zornFlowMulEquiv D 1).toEquiv X := by
  rfl

/-- The time-one exponential preserves the Zorn determinant. -/
@[simp]
theorem zornDerivationExpRealAut_preserves_detZ
    (D : canonicalZornDerivations)
    (X : CZ) :
    ZornMatrix.detZ (((zornDerivationExpRealAut D : RealSplitOctonionAut) : SplitOctonionAutCandidate ℝ) X) =
      ZornMatrix.detZ X := by
  simp

/-- Complete theorem-safe finite automorphism packet for a canonical derivation. -/
theorem canonical_derivation_realAut_packet
    (D : canonicalZornDerivations)
    (s t : ℝ)
    (X Y : CZ) :
    zornFlowLinearEquiv D.1 t (1 : CZ) = 1 ∧
      zornFlowLinearEquiv D.1 t (X * Y) =
        zornFlowLinearEquiv D.1 t X *
          zornFlowLinearEquiv D.1 t Y ∧
      ZornMatrix.detZ (zornFlowLinearEquiv D.1 t X) =
        ZornMatrix.detZ X ∧
      zornFlowRealAut D (s + t) =
        zornFlowRealAut D s * zornFlowRealAut D t ∧
      zornFlowRealAut D (-t) =
        (zornFlowRealAut D t)⁻¹ := by
  exact ⟨
    zornFlow_fixes_one D t,
    zornFlow_preserves_mul D t X Y,
    zornFlow_preserves_detZ D t X,
    zornFlowRealAut_add D s t,
    zornFlowRealAut_neg D t⟩

end InfoGeometry.Lie.CanonicalZornDerivationRealAutBridge

end noncomputable section
