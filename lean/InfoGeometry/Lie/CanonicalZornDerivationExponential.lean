import InfoGeometry.Lie.ContinuousDerivationExponential
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
import InfoGeometry.Canonical.ZornCliffordRepresentation
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Group.End

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornDerivationExponential

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
open InfoGeometry.Lie.ContinuousDerivationExponential
open InfoGeometry.Lie.CanonicalZornDerivation

abbrev V8 := Fin 8 → ℝ

def coordLEFun : CZ → V8 := fun X => fun i =>
  match i with
  | ⟨0, _⟩ => X.a
  | ⟨1, _⟩ => X.b
  | ⟨2, _⟩ => X.x 0
  | ⟨3, _⟩ => X.x 1
  | ⟨4, _⟩ => X.x 2
  | ⟨5, _⟩ => X.y 0
  | ⟨6, _⟩ => X.y 1
  | ⟨7, _⟩ => X.y 2

def coordLEFunInv : V8 → CZ := fun v =>
  {
    a := v 0,
    b := v 1,
    x := fun j => v ⟨j.1 + 2, by omega⟩,
    y := fun j => v ⟨j.1 + 5, by omega⟩
  }

noncomputable def coordLE : CZ ≃ V8 where
  toFun := coordLEFun
  invFun := coordLEFunInv
  left_inv := by
    intro X; cases X
    ext
    · rfl
    · rfl
    · rename_i j; fin_cases j <;> rfl
    · rename_i j; fin_cases j <;> rfl
  right_inv := by
    intro v; funext i; fin_cases i <;> rfl

theorem coordLE_add (X Y : CZ) :
    coordLE (X + Y) = coordLE X + coordLE Y := by
  ext i; fin_cases i <;> rfl

theorem coordLE_smul (r : ℝ) (X : CZ) :
    coordLE (r • X) = r • coordLE X := by
  ext i; fin_cases i <;> rfl

theorem coordLE_symm_add (u v : V8) :
    coordLE.symm (u + v) = coordLE.symm u + coordLE.symm v := by
  apply coordLE.injective
  rw [coordLE.apply_symm_apply, coordLE_add, coordLE.apply_symm_apply, coordLE.apply_symm_apply]

theorem coordLE_symm_smul (r : ℝ) (u : V8) :
    coordLE.symm (r • u) = r • coordLE.symm u := by
  apply coordLE.injective
  rw [coordLE.apply_symm_apply, coordLE_smul, coordLE.apply_symm_apply]

theorem mul_linear_add (u v w : V8) :
    coordLE (coordLE.symm u * coordLE.symm (v + w)) =
      coordLE (coordLE.symm u * coordLE.symm v) + coordLE (coordLE.symm u * coordLE.symm w) := by
  rw [coordLE_symm_add, InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_add, coordLE_add]

theorem mul_linear_smul (u : V8) (r : ℝ) (v : V8) :
    coordLE (coordLE.symm u * coordLE.symm (r • v)) =
      r • coordLE (coordLE.symm u * coordLE.symm v) := by
  rw [coordLE_symm_smul, InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul, coordLE_smul]

theorem mul_linear_left_add (u v w : V8) :
    coordLE (coordLE.symm (u + v) * coordLE.symm w) =
      coordLE (coordLE.symm u * coordLE.symm w) + coordLE (coordLE.symm v * coordLE.symm w) := by
  rw [coordLE_symm_add, InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.add_mul, coordLE_add]

theorem mul_linear_left_smul (r : ℝ) (u w : V8) :
    coordLE (coordLE.symm (r • u) * coordLE.symm w) =
      r • coordLE (coordLE.symm u * coordLE.symm w) := by
  rw [coordLE_symm_smul, InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.smul_mul, coordLE_smul]

def coordMulLinear :
    V8 →ₗ[ℝ] V8 →ₗ[ℝ] V8 where
  toFun u :=
    {
      toFun := fun v => coordLE (coordLE.symm u * coordLE.symm v)
      map_add' := fun v w => mul_linear_add u v w
      map_smul' := fun r v => mul_linear_smul u r v
    }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    exact mul_linear_left_add u v w
  map_smul' := by
    intro r u
    apply LinearMap.ext
    intro w
    exact mul_linear_left_smul r u w

noncomputable def coordMul :
    V8 →L[ℝ] V8 →L[ℝ] V8 :=
  LinearMap.toContinuousLinearMap {
    toFun := fun u => LinearMap.toContinuousLinearMap (coordMulLinear u)
    map_add' := by
      intro u v
      apply ContinuousLinearMap.ext
      intro w
      exact mul_linear_left_add u v w
    map_smul' := by
      intro r u
      apply ContinuousLinearMap.ext
      intro w
      exact mul_linear_left_smul r u w
  }

@[simp]
theorem coordMul_apply (u v : V8) :
    coordMul u v = coordLE (coordLE.symm u * coordLE.symm v) := rfl

@[simp]
theorem coordMul_coordLE (X Y : CZ) :
    coordMul (coordLE X) (coordLE Y) = coordLE (X * Y) := by
  simp [coordMul_apply]

noncomputable def coordLELinearEquiv : CZ ≃ₗ[ℝ] V8 where
  toEquiv := coordLE
  map_add' := coordLE_add
  map_smul' := coordLE_smul

abbrev coordLELin : CZ ≃ₗ[ℝ] V8 := coordLELinearEquiv

@[simp]
theorem coordLE_symm_apply_apply (X : CZ) :
    coordLE.symm (coordLE X) = X :=
  coordLE.left_inv X

def coordEndLinear (D : EndCZ) : V8 →ₗ[ℝ] V8 :=
  (coordLELin : CZ →ₗ[ℝ] V8).comp (D.comp (coordLELin.symm : V8 →ₗ[ℝ] CZ))

noncomputable def coordEnd (D : EndCZ) : V8 →L[ℝ] V8 :=
  LinearMap.toContinuousLinearMap (coordEndLinear D)

@[simp]
theorem coordEnd_apply (D : EndCZ) (u : V8) :
    coordEnd D u = coordLE (D (coordLE.symm u)) := rfl

@[simp]
theorem coordEnd_coordLE (D : EndCZ) (X : CZ) :
    coordEnd D (coordLE X) = coordLE (D X) := by
  simp [coordEnd_apply]

@[simp]
theorem coordEnd_zero : coordEnd (0 : EndCZ) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  ext i
  fin_cases i <;> rfl

@[simp]
theorem coordEnd_add (D E : EndCZ) :
    coordEnd (D + E) = coordEnd D + coordEnd E := by
  apply ContinuousLinearMap.ext
  intro u
  ext i
  fin_cases i <;> rfl

@[simp]
theorem coordEnd_smul (r : ℝ) (D : EndCZ) :
    coordEnd (r • D) = r • coordEnd D := by
  apply ContinuousLinearMap.ext
  intro u
  ext i
  fin_cases i <;> rfl

@[simp]
theorem coordEnd_neg (D : EndCZ) :
    coordEnd (-D) = -(coordEnd D) := by
  apply ContinuousLinearMap.ext
  intro u
  ext i
  fin_cases i <;> rfl

theorem coordEnd_isDerivation (D : EndCZ) (hD : IsDerivation D) :
    ContinuousDerivationExponential.IsDerivation coordMul (coordEnd D) := by
  intro u v
  change coordLE (D (coordLE.symm (coordLE (coordLE.symm u * coordLE.symm v)))) =
    coordLE (coordLE.symm (coordLE (D (coordLE.symm u))) * coordLE.symm v) +
      coordLE (coordLE.symm u * coordLE.symm (coordLE (D (coordLE.symm v))))
  rw [coordLE_symm_apply_apply, coordLE_symm_apply_apply, coordLE_symm_apply_apply]
  rw [hD (coordLE.symm u) (coordLE.symm v), coordLE_add]

noncomputable def coordFlow (D : EndCZ) (t : ℝ) : V8 →L[ℝ] V8 :=
  flow (coordEnd D) t

@[simp]
theorem coordFlow_zero (D : EndCZ) :
    coordFlow D 0 = 1 := by
  simp [coordFlow]

@[simp]
theorem coordFlow_neg_generator (D : EndCZ) (t : ℝ) :
    coordFlow (-D) t = coordFlow D (-t) := by
  simp [coordFlow, coordEnd_neg]

theorem coordFlow_add_apply (D : EndCZ) (s t : ℝ) (u : V8) :
    coordFlow D (s + t) u = coordFlow D s (coordFlow D t u) := by
  simpa [coordFlow] using flow_add_apply (coordEnd D) s t u

@[simp]
theorem coordFlow_neg_apply_flow (D : EndCZ) (t : ℝ) (u : V8) :
    coordFlow (-D) t (coordFlow D t u) = u := by
  dsimp [coordFlow]
  have h₁ : coordEnd (-D) = -(coordEnd D) := coordEnd_neg D
  rw [h₁]
  exact flow_neg_apply_flow (coordEnd D) t u

@[simp]
theorem coordFlow_apply_neg_flow (D : EndCZ) (t : ℝ) (u : V8) :
    coordFlow D t (coordFlow (-D) t u) = u := by
  dsimp [coordFlow]
  have h₁ : coordEnd (-D) = -(coordEnd D) := coordEnd_neg D
  rw [h₁]
  exact flow_apply_flow_neg (coordEnd D) t u

theorem coordFlow_map_mul
    (D : EndCZ)
    (hD : IsDerivation D)
    (t : ℝ)
    (u v : V8) :
    coordFlow D t (coordMul u v) =
      coordMul (coordFlow D t u) (coordFlow D t v) := by
  simpa [coordFlow] using
    flow_map_mul
      coordMul
      (coordEnd D)
      (coordEnd_isDerivation D hD)
      t
      u
      v

noncomputable def zornFlowLinearEquiv
    (D : EndCZ)
    (t : ℝ) :
    CZ ≃ₗ[ℝ] CZ :=
  (coordLELin.trans (flowLinearEquiv (coordEnd D) t)).trans coordLELin.symm

@[simp]
theorem zornFlowLinearEquiv_apply (D : EndCZ) (t : ℝ) (X : CZ) :
    zornFlowLinearEquiv D t X =
      coordLE.symm (flow (coordEnd D) t (coordLE X)) := by
  rfl

@[simp]
theorem coordLE_zornFlowLinearEquiv (D : EndCZ) (t : ℝ) (X : CZ) :
    coordLE (zornFlowLinearEquiv D t X) =
      flow (coordEnd D) t (coordLE X) := by
  simp [zornFlowLinearEquiv_apply]

@[simp]
theorem zornFlowLinearEquiv_zero_apply (D : EndCZ) (X : CZ) :
    zornFlowLinearEquiv D 0 X = X := by
  simp [zornFlowLinearEquiv_apply]

@[simp]
theorem zornFlowLinearEquiv_zero (D : EndCZ) :
    zornFlowLinearEquiv D 0 = 1 := by
  apply LinearEquiv.ext
  intro X
  exact zornFlowLinearEquiv_zero_apply D X

theorem zornFlowLinearEquiv_add_apply (D : EndCZ) (s t : ℝ) (X : CZ) :
    zornFlowLinearEquiv D (s + t) X =
      zornFlowLinearEquiv D s (zornFlowLinearEquiv D t X) := by
  apply coordLE.injective
  simp only [coordLE_zornFlowLinearEquiv]
  exact flow_add_apply (coordEnd D) s t (coordLE X)

@[simp]
theorem zornFlowLinearEquiv_neg_generator (D : EndCZ) (t : ℝ) :
    zornFlowLinearEquiv (-D) t = zornFlowLinearEquiv D (-t) := by
  apply LinearEquiv.ext
  intro X
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv, coordLE_zornFlowLinearEquiv, coordEnd_neg]
  have h := flow_neg_generator (coordEnd D) t
  rw [h]
  <;> simp [coordLE_zornFlowLinearEquiv]
  <;> rfl

@[simp]
theorem zornFlowLinearEquiv_neg_apply (D : EndCZ) (t : ℝ) (X : CZ) :
    zornFlowLinearEquiv (-D) t (zornFlowLinearEquiv D t X) = X := by
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv, coordLE_zornFlowLinearEquiv, coordEnd_neg]
  exact flow_neg_apply_flow (coordEnd D) t (coordLE X)

@[simp]
theorem zornFlowLinearEquiv_apply_neg (D : EndCZ) (t : ℝ) (X : CZ) :
    zornFlowLinearEquiv D t (zornFlowLinearEquiv (-D) t X) = X := by
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv, coordLE_zornFlowLinearEquiv, coordEnd_neg]
  exact flow_apply_flow_neg (coordEnd D) t (coordLE X)

theorem zornFlowLinearEquiv_neg_eq_symm
    (D : EndCZ)
    (t : ℝ) :
    zornFlowLinearEquiv D (-t) =
      (zornFlowLinearEquiv D t).symm := by
  rw [← zornFlowLinearEquiv_neg_generator D t]
  apply LinearEquiv.ext
  intro X
  apply
    (zornFlowLinearEquiv D t).injective
  rw [LinearEquiv.apply_symm_apply]
  exact
    zornFlowLinearEquiv_apply_neg
      D
      t
      X

@[simp]
theorem zornFlowLinearEquiv_neg_apply_symm
    (D : EndCZ)
    (t : ℝ)
    (X : CZ) :
    zornFlowLinearEquiv D t
        (zornFlowLinearEquiv D (-t) X) =
      X := by
  have h : zornFlowLinearEquiv D (-t) = (zornFlowLinearEquiv D t).symm := by
    rw [zornFlowLinearEquiv_neg_eq_symm]
  rw [h]
  exact LinearEquiv.apply_symm_apply (zornFlowLinearEquiv D t) X

theorem zornFlow_map_mul
    (D : EndCZ)
    (hD : IsDerivation D)
    (t : ℝ)
    (X Y : CZ) :
    zornFlowLinearEquiv D t (X * Y) =
      zornFlowLinearEquiv D t X *
        zornFlowLinearEquiv D t Y := by
  apply coordLE.injective
  simp only [coordLE_zornFlowLinearEquiv, ← coordMul_coordLE]
  exact flow_map_mul coordMul (coordEnd D) (coordEnd_isDerivation D hD) t (coordLE X) (coordLE Y)

private theorem zorn_one_mul (X : CZ) : (1 : CZ) * X = X := by
  rcases X with ⟨a, b, x, y⟩
  have h1 : (1 : CZ) = { a := 1, b := 1, x := 0, y := 0 } := rfl
  rw [h1]
  ext
  · simp [mul_def, mul, dot, cross]
  · simp [mul_def, mul, dot, cross]
  · rename_i i; fin_cases i <;> simp [mul_def, mul, dot, cross]
  · rename_i i; fin_cases i <;> simp [mul_def, mul, dot, cross]

private theorem zorn_mul_one (X : CZ) : X * (1 : CZ) = X := by
  rcases X with ⟨a, b, x, y⟩
  have h1 : (1 : CZ) = { a := 1, b := 1, x := 0, y := 0 } := rfl
  rw [h1]
  ext
  · simp [mul_def, mul, dot, cross]
  · simp [mul_def, mul, dot, cross]
  · rename_i i; fin_cases i <;> simp [mul_def, mul, dot, cross]
  · rename_i i; fin_cases i <;> simp [mul_def, mul, dot, cross]

@[simp]
theorem zornFlow_map_one
    (D : EndCZ)
    (hD : IsDerivation D)
    (t : ℝ) :
    zornFlowLinearEquiv D t (1 : CZ) = 1 := by
  let y : CZ := (zornFlowLinearEquiv D t).symm 1
  have hy : zornFlowLinearEquiv D t y = (1 : CZ) := by
    dsimp [y]
    exact (zornFlowLinearEquiv D t).apply_symm_apply 1
  have hm := zornFlow_map_mul D hD t (1 : CZ) y
  rw [zorn_one_mul, hy, zorn_mul_one] at hm
  exact hm.symm

noncomputable def zornFlowMulEquiv
    (D : canonicalZornDerivations)
    (t : ℝ) :
    CZ ≃* CZ where
  toEquiv := (zornFlowLinearEquiv D.1 t).toEquiv
  map_mul' := by
    intro X Y
    exact zornFlow_map_mul D.1 D.2 t X Y

@[simp]
theorem zornFlowMulEquiv_apply
    (D : canonicalZornDerivations)
    (t : ℝ)
    (X : CZ) :
    zornFlowMulEquiv D t X = zornFlowLinearEquiv D.1 t X := rfl

@[simp]
theorem zornFlowMulEquiv_zero_apply
    (D : canonicalZornDerivations)
    (X : CZ) :
    zornFlowMulEquiv D 0 X = X := by
  change zornFlowLinearEquiv D.1 0 X = X
  exact zornFlowLinearEquiv_zero_apply D.1 X

@[simp]
theorem zornFlowMulEquiv_map_one
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowMulEquiv D t (1 : CZ) = 1 := by
  change zornFlowLinearEquiv D.1 t (1 : CZ) = 1
  exact zornFlow_map_one D.1 D.2 t

theorem zornFlowMulEquiv_add_apply
    (D : canonicalZornDerivations)
    (s t : ℝ)
    (X : CZ) :
    zornFlowMulEquiv D (s + t) X =
      zornFlowMulEquiv D s
        (zornFlowMulEquiv D t X) :=
  zornFlowLinearEquiv_add_apply D.1 s t X

noncomputable def zornDerivationExpAutomorphism
    (D : canonicalZornDerivations) : CZ ≃* CZ :=
  zornFlowMulEquiv D 1

theorem zornDerivationExpAutomorphism_map_mul
    (D : canonicalZornDerivations)
    (X Y : CZ) :
    zornDerivationExpAutomorphism D (X * Y) =
      zornDerivationExpAutomorphism D X *
        zornDerivationExpAutomorphism D Y :=
  map_mul (zornDerivationExpAutomorphism D) X Y

@[simp]
theorem zornDerivationExpAutomorphism_map_one
    (D : canonicalZornDerivations) :
    zornDerivationExpAutomorphism D (1 : CZ) = 1 :=
  zornFlowMulEquiv_map_one D 1

theorem canonical_derivation_exponential_full_packet
    (D : canonicalZornDerivations)
    (s t : ℝ)
    (X Y : CZ) :
    zornFlowMulEquiv D t (1 : CZ) = 1 ∧
      zornFlowMulEquiv D t (X * Y) =
        zornFlowMulEquiv D t X * zornFlowMulEquiv D t Y ∧
      zornFlowLinearEquiv D.1 (s + t) X =
        zornFlowLinearEquiv D.1 s (zornFlowLinearEquiv D.1 t X) ∧
      zornFlowLinearEquiv (-D.1) t (zornFlowLinearEquiv D.1 t X) = X :=
  ⟨zornFlowMulEquiv_map_one D t,
   map_mul (zornFlowMulEquiv D t) X Y,
   zornFlowLinearEquiv_add_apply D.1 s t X,
   zornFlowLinearEquiv_neg_apply D.1 t X⟩

end InfoGeometry.Lie.CanonicalZornDerivationExponential
