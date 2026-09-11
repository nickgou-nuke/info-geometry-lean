import InfoGeometry.Lie.ContinuousDerivationExponential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
import InfoGeometry.Canonical.ZornSpinor
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornDerivationExponential

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
open InfoGeometry.Lie.ContinuousDerivationExponential
open InfoGeometry.Lie.CanonicalZornDerivation

abbrev CZ := InfoGeometry.Lie.CanonicalZornDerivation.CZ
abbrev EndCZ := InfoGeometry.Lie.CanonicalZornDerivation.EndCZ
abbrev V8 := InfoGeometry.Algebra.FiniteSpin.Vec8R

variable {R : Type*} [CommRing R]

theorem zorn_mul_add (z1 z2 z3 : ZornMatrix R) : z1 * (z2 + z3) = z1 * z2 + z1 * z3 := by
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, add_def]; ring
  · simp [mul_def, mul, dot, add_def]; ring
  · ext i; fin_cases i <;> simp [mul_def, mul, cross, add_def, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, smul_eq_mul] <;> ring
  · ext i; fin_cases i <;> simp [mul_def, mul, cross, add_def, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, smul_eq_mul] <;> ring

theorem zorn_add_mul (z1 z2 z3 : ZornMatrix R) : (z1 + z2) * z3 = z1 * z3 + z2 * z3 := by
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, add_def]; ring
  · simp [mul_def, mul, dot, add_def]; ring
  · ext i; fin_cases i <;> simp [mul_def, mul, cross, add_def, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, smul_eq_mul] <;> ring
  · ext i; fin_cases i <;> simp [mul_def, mul, cross, add_def, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, smul_eq_mul] <;> ring

theorem zorn_mul_smul (r : R) (z1 z2 : ZornMatrix R) : z1 * (r • z2) = r • (z1 * z2) := by
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, smul_a, smul_b, smul_x, smul_y]; ring
  · simp [mul_def, mul, dot, smul_a, smul_b, smul_x, smul_y]; ring
  · ext i; fin_cases i <;> simp [mul_def, mul, cross, smul_a, smul_b, smul_x, smul_y, Matrix.vecHead, Matrix.vecTail, smul_eq_mul, Pi.smul_apply] <;> ring
  · ext i; fin_cases i <;> simp [mul_def, mul, cross, smul_a, smul_b, smul_x, smul_y, Matrix.vecHead, Matrix.vecTail, smul_eq_mul, Pi.smul_apply] <;> ring

theorem zorn_smul_mul (r : R) (z1 z2 : ZornMatrix R) : (r • z1) * z2 = r • (z1 * z2) := by
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, smul_a, smul_b, smul_x, smul_y]; ring
  · simp [mul_def, mul, dot, smul_a, smul_b, smul_x, smul_y]; ring
  · ext i; fin_cases i <;> simp [mul_def, mul, cross, smul_a, smul_b, smul_x, smul_y, Matrix.vecHead, Matrix.vecTail, smul_eq_mul, Pi.smul_apply] <;> ring
  · ext i; fin_cases i <;> simp [mul_def, mul, cross, smul_a, smul_b, smul_x, smul_y, Matrix.vecHead, Matrix.vecTail, smul_eq_mul, Pi.smul_apply] <;> ring

def coordMulLinear :
    V8 →ₗ[ℝ] V8 →ₗ[ℝ] V8 where
  toFun u :=
    {
      toFun := fun v => coordLE (coordLE.symm u * coordLE.symm v)
      map_add' := by
        intro v w
        change coordLE (coordLE.symm u * (coordLE.symm (v + w))) = coordLE (coordLE.symm u * coordLE.symm v) + coordLE (coordLE.symm u * coordLE.symm w)
        rw [map_add, zorn_mul_add, map_add]
      map_smul' := by
        intro r v
        change coordLE (coordLE.symm u * (coordLE.symm (r • v))) = r • coordLE (coordLE.symm u * coordLE.symm v)
        rw [map_smul, zorn_mul_smul, map_smul]
    }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    change coordLE (coordLE.symm (u + v) * coordLE.symm w) = coordLE (coordLE.symm u * coordLE.symm w) + coordLE (coordLE.symm v * coordLE.symm w)
    rw [map_add, zorn_add_mul, map_add]
  map_smul' r u := by
    apply LinearMap.ext
    intro v
    change coordLE (coordLE.symm (r • u) * coordLE.symm v) = r • coordLE (coordLE.symm u * coordLE.symm v)
    rw [map_smul, zorn_smul_mul, map_smul]

def coordMulLinearMap :
    V8 →ₗ[ℝ] (V8 →L[ℝ] V8) where
  toFun u := LinearMap.toContinuousLinearMap (coordMulLinear u)
  map_add' u v := by
    simp only [map_add]
  map_smul' r u := by
    simp only [map_smul, RingHom.id_apply]

noncomputable def coordMul :
    V8 →L[ℝ] V8 →L[ℝ] V8 :=
  LinearMap.toContinuousLinearMap coordMulLinearMap

@[simp]
theorem coordMul_apply (u v : V8) :
    coordMul u v = coordLE (coordLE.symm u * coordLE.symm v) := rfl

@[simp]
theorem coordMul_coordLE (X Y : CZ) :
    coordMul (coordLE X) (coordLE Y) = coordLE (X * Y) := by
  simp [coordMul_apply]

def coordEndLinear (D : EndCZ) : Module.End ℝ V8 :=
  (coordLE : CZ →ₗ[ℝ] V8).comp (D.comp (coordLE.symm : V8 →ₗ[ℝ] CZ))

noncomputable def coordEnd (D : EndCZ) : V8 →L[ℝ] V8 :=
  LinearMap.toContinuousLinearMap (coordEndLinear D)

@[simp]
theorem coordEnd_apply (D : EndCZ) (u : V8) :
    coordEnd D u = coordLE (D (coordLE.symm u)) := rfl

@[simp]
theorem coordEnd_apply_coordLE (D : EndCZ) (X : CZ) :
    coordEnd D (coordLE X) = coordLE (D X) := by
  simp [coordEnd, coordEndLinear]

@[simp]
theorem coordEnd_zero : coordEnd (0 : EndCZ) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  simp [coordEnd, coordEndLinear]

@[simp]
theorem coordEnd_add (D E : EndCZ) : coordEnd (D + E) = coordEnd D + coordEnd E := by
  apply ContinuousLinearMap.ext
  intro u
  change coordLE ((D + E) (coordLE.symm u)) = coordLE (D (coordLE.symm u)) + coordLE (E (coordLE.symm u))
  rw [LinearMap.add_apply, map_add]

@[simp]
theorem coordEnd_smul (r : ℝ) (D : EndCZ) : coordEnd (r • D) = r • coordEnd D := by
  apply ContinuousLinearMap.ext
  intro u
  change coordLE ((r • D) (coordLE.symm u)) = r • coordLE (D (coordLE.symm u))
  rw [LinearMap.smul_apply, map_smul]

@[simp]
theorem coordEnd_neg (D : EndCZ) : coordEnd (-D) = -(coordEnd D) := by
  apply ContinuousLinearMap.ext
  intro u
  change coordLE ((-D) (coordLE.symm u)) = -coordLE (D (coordLE.symm u))
  rw [LinearMap.neg_apply, map_neg]

theorem coordEnd_isDerivation (D : EndCZ) (hD : InfoGeometry.Lie.CanonicalZornDerivation.IsDerivation D) :
    InfoGeometry.Lie.ContinuousDerivationExponential.IsDerivation coordMul (coordEnd D) := by
  intro u v
  simp only [coordEnd_apply, coordMul_apply, LinearEquiv.symm_apply_apply]
  rw [hD, map_add]

noncomputable def coordFlow (D : EndCZ) (t : ℝ) : V8 →L[ℝ] V8 :=
  flow (coordEnd D) t

@[simp]
theorem coordFlow_zero (D : EndCZ) : coordFlow D 0 = 1 := by
  simp [coordFlow]

theorem coordFlow_map_mul (D : EndCZ) (hD : InfoGeometry.Lie.CanonicalZornDerivation.IsDerivation D)
    (t : ℝ) (u v : V8) :
    coordFlow D t (coordMul u v) = coordMul (coordFlow D t u) (coordFlow D t v) := by
  exact flow_map_mul coordMul (coordEnd D) (coordEnd_isDerivation D hD) t u v

noncomputable def zornFlowLinearEquiv (D : EndCZ) (t : ℝ) : CZ ≃ₗ[ℝ] CZ :=
  coordLE.trans ((flowLinearEquiv (coordEnd D) t).trans coordLE.symm)

@[simp]
theorem zornFlowLinearEquiv_apply (D : EndCZ) (t : ℝ) (X : CZ) :
    zornFlowLinearEquiv D t X = coordLE.symm (flow (coordEnd D) t (coordLE X)) := rfl

@[simp]
theorem coordLE_zornFlowLinearEquiv (D : EndCZ) (t : ℝ) (X : CZ) :
    coordLE (zornFlowLinearEquiv D t X) = flow (coordEnd D) t (coordLE X) := by
  simp [zornFlowLinearEquiv]

@[simp]
theorem zornFlowLinearEquiv_zero_apply (D : EndCZ) (X : CZ) :
    zornFlowLinearEquiv D 0 X = X := by
  apply coordLE.injective
  simp

@[simp]
theorem zornFlowLinearEquiv_neg_apply (D : EndCZ) (t : ℝ) (X : CZ) :
    zornFlowLinearEquiv (-D) t (zornFlowLinearEquiv D t X) = X := by
  apply coordLE.injective
  simp only [coordLE_zornFlowLinearEquiv, coordEnd_neg]
  exact flow_neg_apply_flow (coordEnd D) t (coordLE X)

@[simp]
theorem zornFlowLinearEquiv_apply_neg (D : EndCZ) (t : ℝ) (X : CZ) :
    zornFlowLinearEquiv D t (zornFlowLinearEquiv (-D) t X) = X := by
  apply coordLE.injective
  simp only [coordLE_zornFlowLinearEquiv, coordEnd_neg]
  exact flow_apply_flow_neg (coordEnd D) t (coordLE X)

theorem zornFlow_map_mul (D : EndCZ) (hD : InfoGeometry.Lie.CanonicalZornDerivation.IsDerivation D)
    (t : ℝ) (X Y : CZ) :
    zornFlowLinearEquiv D t (X * Y) = zornFlowLinearEquiv D t X * zornFlowLinearEquiv D t Y := by
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv, ← coordMul_coordLE X Y,
      ← coordMul_coordLE (zornFlowLinearEquiv D t X) (zornFlowLinearEquiv D t Y),
      coordLE_zornFlowLinearEquiv, coordLE_zornFlowLinearEquiv]
  exact coordFlow_map_mul D hD t (coordLE X) (coordLE Y)

theorem zornFlowLinearEquiv_add_apply (D : EndCZ) (s t : ℝ) (X : CZ) :
    zornFlowLinearEquiv D (s + t) X = zornFlowLinearEquiv D s (zornFlowLinearEquiv D t X) := by
  apply coordLE.injective
  simp only [coordLE_zornFlowLinearEquiv]
  exact flow_add_apply (coordEnd D) s t (coordLE X)

noncomputable def zornFlowMulEquiv (D : canonicalZornDerivations) (t : ℝ) : CZ ≃* CZ where
  toEquiv := (zornFlowLinearEquiv D.1 t).toEquiv
  map_mul' := by
    intro X Y
    exact zornFlow_map_mul D.1 D.2 t X Y

@[simp]
theorem zornFlowMulEquiv_apply (D : canonicalZornDerivations) (t : ℝ) (X : CZ) :
    zornFlowMulEquiv D t X = zornFlowLinearEquiv D.1 t X := rfl

@[simp]
theorem zornFlowMulEquiv_zero_apply (D : canonicalZornDerivations) (X : CZ) :
    zornFlowMulEquiv D 0 X = X := by
  simp [zornFlowMulEquiv]

theorem zornFlowMulEquiv_add_apply (D : canonicalZornDerivations) (s t : ℝ) (X : CZ) :
    zornFlowMulEquiv D (s + t) X = zornFlowMulEquiv D s (zornFlowMulEquiv D t X) := by
  exact zornFlowLinearEquiv_add_apply D.1 s t X

noncomputable def zornDerivationExpAutomorphism (D : canonicalZornDerivations) : CZ ≃* CZ :=
  zornFlowMulEquiv D 1

theorem zornDerivationExpAutomorphism_map_mul (D : canonicalZornDerivations) (X Y : CZ) :
    zornDerivationExpAutomorphism D (X * Y) =
      zornDerivationExpAutomorphism D X * zornDerivationExpAutomorphism D Y := by
  exact map_mul (zornDerivationExpAutomorphism D) X Y

theorem canonical_derivation_exponential_packet (D : canonicalZornDerivations) (t : ℝ) (X Y : CZ) :
    zornFlowMulEquiv D t (X * Y) = zornFlowMulEquiv D t X * zornFlowMulEquiv D t Y := by
  exact map_mul (zornFlowMulEquiv D t) X Y

/-! Algebraic relations transported by the multiplicative flow. -/

def zornAnticommutator (X Y : CZ) : CZ := X * Y + Y * X

theorem zornFlow_map_anticommutator
    (D : canonicalZornDerivations) (t : ℝ) (X Y : CZ) :
    zornFlowLinearEquiv D.1 t (zornAnticommutator X Y) =
      zornAnticommutator (zornFlowLinearEquiv D.1 t X)
        (zornFlowLinearEquiv D.1 t Y) := by
  change zornFlowLinearEquiv D.1 t (X * Y + Y * X) =
    zornFlowLinearEquiv D.1 t X * zornFlowLinearEquiv D.1 t Y +
      zornFlowLinearEquiv D.1 t Y * zornFlowLinearEquiv D.1 t X
  rw [(zornFlowLinearEquiv D.1 t).map_add,
    zornFlow_map_mul D.1 D.2 t X Y,
    zornFlow_map_mul D.1 D.2 t Y X]

theorem zornFlow_preserves_nilpotent
    (D : canonicalZornDerivations) (t : ℝ) (X : CZ)
    (hX : X * X = 0) :
    zornFlowLinearEquiv D.1 t X * zornFlowLinearEquiv D.1 t X = 0 := by
  rw [← zornFlow_map_mul D.1 D.2 t X X, hX]
  exact (zornFlowLinearEquiv D.1 t).map_zero

theorem zornFlow_preserves_idempotent
    (D : canonicalZornDerivations) (t : ℝ) (X : CZ)
    (hX : X * X = X) :
    zornFlowLinearEquiv D.1 t X * zornFlowLinearEquiv D.1 t X =
      zornFlowLinearEquiv D.1 t X := by
  rw [← zornFlow_map_mul D.1 D.2 t X X, hX]

theorem zornFlow_preserves_anticommutator_eq
    (D : canonicalZornDerivations) (t : ℝ) (X Y C : CZ)
    (hXY : zornAnticommutator X Y = C) :
    zornAnticommutator (zornFlowLinearEquiv D.1 t X)
        (zornFlowLinearEquiv D.1 t Y) =
      zornFlowLinearEquiv D.1 t C := by
  rw [← zornFlow_map_anticommutator D t X Y, hXY]

theorem canonical_derivation_fixes_scalar_unit
    (D : canonicalZornDerivations) (c : ℝ) :
    D.1 (c • (1 : CZ)) = 0 := by
  rw [map_smul]
  have h := D.2 1 1
  simp only [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_one,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.one_mul] at h
  have hone : D.1 (1 : CZ) = 0 := by
    have hcancel : (0 : CZ) = D.1 (1 : CZ) :=
      add_left_cancel (by simpa using h)
    exact hcancel.symm
  rw [hone, smul_zero]

/-- If `D X = 0`, then the Zorn flow fixes `X`: `Φ_t X = X`. -/
theorem zornFlowLinearEquiv_fixed_of_derivation_eq_zero
    (D : EndCZ)
    (X : CZ)
    (hX : D X = 0)
    (t : ℝ) :
    zornFlowLinearEquiv D t X = X := by
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv]
  have hcoord : coordEnd D (coordLE X) = 0 := by
    rw [coordEnd_apply_coordLE, hX, map_zero]
  exact flow_apply_eq_self_of_apply_eq_zero (coordEnd D) (coordLE X) hcoord t

end InfoGeometry.Lie.CanonicalZornDerivationExponential

end noncomputable section
