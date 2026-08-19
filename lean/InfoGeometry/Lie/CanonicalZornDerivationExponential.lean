import InfoGeometry.Lie.ContinuousDerivationExponential
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
import InfoGeometry.Canonical.ZornCliffordRepresentation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Group.End

/-!
# Exponentiating canonical Zorn derivations

This module specializes the generic continuous-derivation exponential theorem
to the canonical real Zorn split-octonion carrier.

The nonassociative Zorn product is transported through the repository-owned
linear equivalence

`coordLE : ZornMatrix ℝ ≃ₗ[ℝ] (Fin 8 → ℝ)`.

The coordinate carrier is finite-dimensional.  Hence linear maps out of it are
continuous.  We use that fact twice to turn the algebraic bilinear Zorn product
into the curried continuous bilinear map required by
`ContinuousDerivationExponential`.

No associativity hypothesis on the Zorn product is used.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornDerivationExponential

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal

namespace CDE := InfoGeometry.Lie.ContinuousDerivationExponential
namespace CZD := InfoGeometry.Lie.CanonicalZornDerivation

abbrev CZ := CZD.CZ
abbrev EndCZ := CZD.EndCZ
abbrev V8 := Fin 8 → ℝ

/-!
## Continuous coordinate realization
-/

/-- Zorn multiplication transported algebraically to the coordinate carrier. -/
def coordMulLinear : V8 →ₗ[ℝ] V8 →ₗ[ℝ] V8 where
  toFun u :=
    { toFun := fun v => coordLE (coordLE.symm u * coordLE.symm v)
      map_add' := by
        intro v w
        rw [map_add, mul_add', map_add]
      map_smul' := by
        intro r v
        rw [map_smul, mul_smul', map_smul] }
  map_add' := by
    intro u v
    ext w
    rw [map_add, add_mul', map_add]
  map_smul' := by
    intro r u
    ext v
    rw [map_smul, smul_mul', map_smul]

/-- For fixed left input, transported Zorn multiplication is continuous linear. -/
noncomputable def coordMulRight (u : V8) : V8 →L[ℝ] V8 :=
  (coordMulLinear u).toContinuousLinearMap

@[simp]
theorem coordMulRight_apply (u v : V8) :
    coordMulRight u v = coordLE (coordLE.symm u * coordLE.symm v) := by
  rfl

/-- The left input depends linearly on a continuous-linear right multiplication map. -/
noncomputable def coordMulOuterLinear : V8 →ₗ[ℝ] (V8 →L[ℝ] V8) where
  toFun := coordMulRight
  map_add' := by
    intro u v
    apply ContinuousLinearMap.ext
    intro w
    change
      coordLE (coordLE.symm (u + v) * coordLE.symm w) =
        coordLE (coordLE.symm u * coordLE.symm w) +
          coordLE (coordLE.symm v * coordLE.symm w)
    rw [map_add, add_mul', map_add]
  map_smul' := by
    intro r u
    apply ContinuousLinearMap.ext
    intro v
    change
      coordLE (coordLE.symm (r • u) * coordLE.symm v) =
        r • coordLE (coordLE.symm u * coordLE.symm v)
    rw [map_smul, smul_mul', map_smul]

/--
The transported Zorn multiplication as a curried continuous bilinear map.

Only `Mathlib.Topology.Algebra.Module.FiniteDimension` is required: continuity
is introduced by `LinearMap.toContinuousLinearMap` in each argument.
-/
noncomputable def coordMul : V8 →L[ℝ] V8 →L[ℝ] V8 :=
  coordMulOuterLinear.toContinuousLinearMap

@[simp]
theorem coordMul_apply (u v : V8) :
    coordMul u v = coordLE (coordLE.symm u * coordLE.symm v) := by
  rfl

@[simp]
theorem coordMul_coordLE (X Y : CZ) :
    coordMul (coordLE X) (coordLE Y) = coordLE (X * Y) := by
  simp [coordMul_apply]

/-- Transport a canonical Zorn endomorphism to the coordinate space. -/
def coordEndLinear (D : EndCZ) : Module.End ℝ V8 :=
  (coordLE : CZ →ₗ[ℝ] V8).comp
    (D.comp (coordLE.symm : V8 →ₗ[ℝ] CZ))

/-- Every transported endomorphism is continuous because `V8` is finite-dimensional. -/
noncomputable def coordEnd (D : EndCZ) : V8 →L[ℝ] V8 :=
  (coordEndLinear D).toContinuousLinearMap

@[simp]
theorem coordEnd_apply (D : EndCZ) (u : V8) :
    coordEnd D u = coordLE (D (coordLE.symm u)) := by
  rfl

@[simp]
theorem coordEnd_coordLE (D : EndCZ) (X : CZ) :
    coordEnd D (coordLE X) = coordLE (D X) := by
  simp [coordEnd]

@[simp]
theorem coordEnd_zero :
    coordEnd (0 : EndCZ) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  simp [coordEnd_apply]

@[simp]
theorem coordEnd_add (D E : EndCZ) :
    coordEnd (D + E) = coordEnd D + coordEnd E := by
  apply ContinuousLinearMap.ext
  intro u
  simp [coordEnd_apply]

@[simp]
theorem coordEnd_smul (r : ℝ) (D : EndCZ) :
    coordEnd (r • D) = r • coordEnd D := by
  apply ContinuousLinearMap.ext
  intro u
  simp [coordEnd_apply]

@[simp]
theorem coordEnd_neg (D : EndCZ) :
    coordEnd (-D) = -(coordEnd D) := by
  apply ContinuousLinearMap.ext
  intro u
  simp [coordEnd_apply]

/-- The Leibniz property is invariant under coordinate transport. -/
theorem coordEnd_isDerivation
    (D : EndCZ)
    (hD : CZD.IsDerivation D) :
    CDE.IsDerivation coordMul (coordEnd D) := by
  intro u v
  simp only [coordEnd_apply, coordMul_apply, Equiv.apply_symm_apply]
  rw [hD]
  rw [map_add]

/-!
## Coordinate exponential flow
-/

/-- The exponential flow on coordinates generated by a canonical Zorn endomorphism. -/
noncomputable def coordFlow (D : EndCZ) (t : ℝ) : V8 →L[ℝ] V8 :=
  CDE.flow (coordEnd D) t

@[simp]
theorem coordFlow_zero (D : EndCZ) :
    coordFlow D 0 = 1 := by
  simp [coordFlow]

@[simp]
theorem coordFlow_neg_generator (D : EndCZ) (t : ℝ) :
    coordFlow (-D) t = coordFlow D (-t) := by
  simp [coordFlow, coordEnd_neg]

/-- Coordinate flow satisfies the pointwise additive parameter law. -/
theorem coordFlow_add_apply
    (D : EndCZ)
    (s t : ℝ)
    (u : V8) :
    coordFlow D (s + t) u =
      coordFlow D s (coordFlow D t u) := by
  simpa [coordFlow] using
    CDE.flow_add_apply (coordEnd D) s t u

/-- Negative coordinate flow is a left inverse. -/
@[simp]
theorem coordFlow_neg_apply_flow
    (D : EndCZ)
    (t : ℝ)
    (u : V8) :
    coordFlow (-D) t (coordFlow D t u) = u := by
  rw [coordFlow, coordFlow, coordEnd_neg]
  exact CDE.flow_neg_apply_flow (coordEnd D) t u

/-- Positive coordinate flow is a left inverse of the negative-generator flow. -/
@[simp]
theorem coordFlow_apply_neg_flow
    (D : EndCZ)
    (t : ℝ)
    (u : V8) :
    coordFlow D t (coordFlow (-D) t u) = u := by
  rw [coordFlow, coordFlow, coordEnd_neg]
  exact CDE.flow_apply_flow_neg (coordEnd D) t u

/-- The coordinate exponential flow preserves transported Zorn multiplication. -/
theorem coordFlow_map_mul
    (D : EndCZ)
    (hD : CZD.IsDerivation D)
    (t : ℝ)
    (u v : V8) :
    coordFlow D t (coordMul u v) =
      coordMul (coordFlow D t u) (coordFlow D t v) := by
  simpa [coordFlow] using
    CDE.flow_map_mul
      coordMul
      (coordEnd D)
      (coordEnd_isDerivation D hD)
      t
      u
      v

/-!
## Transport back to the canonical Zorn carrier
-/

/--
The exponential flow transported back to the canonical real Zorn carrier.
Its inverse is generated by the negative derivation.
-/
noncomputable def zornFlowLinearEquiv (D : EndCZ) (t : ℝ) : CZ ≃ₗ[ℝ] CZ :=
  coordLE.trans
    ((CDE.flowLinearEquiv (coordEnd D) t).trans coordLE.symm)

@[simp]
theorem zornFlowLinearEquiv_apply
    (D : EndCZ)
    (t : ℝ)
    (X : CZ) :
    zornFlowLinearEquiv D t X =
      coordLE.symm (CDE.flow (coordEnd D) t (coordLE X)) := by
  rfl

@[simp]
theorem coordLE_zornFlowLinearEquiv
    (D : EndCZ)
    (t : ℝ)
    (X : CZ) :
    coordLE (zornFlowLinearEquiv D t X) =
      CDE.flow (coordEnd D) t (coordLE X) := by
  rw [zornFlowLinearEquiv_apply]
  exact coordLE.apply_symm_apply _

/-- Time-zero Zorn flow is the identity pointwise. -/
@[simp]
theorem zornFlowLinearEquiv_zero_apply
    (D : EndCZ)
    (X : CZ) :
    zornFlowLinearEquiv D 0 X = X := by
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv]
  simp

/-- Time-zero Zorn flow is the identity linear equivalence. -/
@[simp]
theorem zornFlowLinearEquiv_zero (D : EndCZ) :
    zornFlowLinearEquiv D 0 = (1 : CZ ≃ₗ[ℝ] CZ) := by
  apply LinearEquiv.ext
  intro X
  exact zornFlowLinearEquiv_zero_apply D X

/-- The transported Zorn flow satisfies the pointwise additive parameter law. -/
theorem zornFlowLinearEquiv_add_apply
    (D : EndCZ)
    (s t : ℝ)
    (X : CZ) :
    zornFlowLinearEquiv D (s + t) X =
      zornFlowLinearEquiv D s
        (zornFlowLinearEquiv D t X) := by
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv]
  rw [coordLE_zornFlowLinearEquiv]
  rw [coordLE_zornFlowLinearEquiv]
  exact CDE.flow_add_apply (coordEnd D) s t (coordLE X)

/-- The transported linear equivalences satisfy the additive parameter law. -/
theorem zornFlowLinearEquiv_add
    (D : EndCZ)
    (s t : ℝ) :
    zornFlowLinearEquiv D (s + t) =
      zornFlowLinearEquiv D s * zornFlowLinearEquiv D t := by
  apply LinearEquiv.ext
  intro X
  rw [LinearEquiv.mul_apply]
  exact zornFlowLinearEquiv_add_apply D s t X

/-- Negating the generator reverses the time parameter after Zorn transport. -/
@[simp]
theorem zornFlowLinearEquiv_neg_generator
    (D : EndCZ)
    (t : ℝ) :
    zornFlowLinearEquiv (-D) t = zornFlowLinearEquiv D (-t) := by
  apply LinearEquiv.ext
  intro X
  rw [zornFlowLinearEquiv_apply, zornFlowLinearEquiv_apply]
  rw [coordEnd_neg]
  rw [CDE.flow_neg_generator]

/-- The negative-generator flow is a left inverse of the positive flow. -/
@[simp]
theorem zornFlowLinearEquiv_neg_apply
    (D : EndCZ)
    (t : ℝ)
    (X : CZ) :
    zornFlowLinearEquiv (-D) t (zornFlowLinearEquiv D t X) = X := by
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv]
  rw [coordLE_zornFlowLinearEquiv]
  rw [coordEnd_neg]
  exact CDE.flow_neg_apply_flow (coordEnd D) t (coordLE X)

/-- The positive flow is a left inverse of the negative-generator flow. -/
@[simp]
theorem zornFlowLinearEquiv_apply_neg
    (D : EndCZ)
    (t : ℝ)
    (X : CZ) :
    zornFlowLinearEquiv D t (zornFlowLinearEquiv (-D) t X) = X := by
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv]
  rw [coordLE_zornFlowLinearEquiv]
  rw [coordEnd_neg]
  exact CDE.flow_apply_flow_neg (coordEnd D) t (coordLE X)

/-- Negative time is exactly the inverse transported linear equivalence. -/
theorem zornFlowLinearEquiv_neg_eq_symm
    (D : EndCZ)
    (t : ℝ) :
    zornFlowLinearEquiv D (-t) = (zornFlowLinearEquiv D t).symm := by
  rw [← zornFlowLinearEquiv_neg_generator D t]
  apply LinearEquiv.ext
  intro X
  apply (zornFlowLinearEquiv D t).injective
  rw [LinearEquiv.apply_symm_apply]
  exact zornFlowLinearEquiv_apply_neg D t X

/-!
## Multiplicativity and unit preservation
-/

/--
A canonical Zorn derivation exponentiates to a multiplication-preserving
linear equivalence of the nonassociative split-octonion carrier.
-/
theorem zornFlow_map_mul
    (D : EndCZ)
    (hD : CZD.IsDerivation D)
    (t : ℝ)
    (X Y : CZ) :
    zornFlowLinearEquiv D t (X * Y) =
      zornFlowLinearEquiv D t X * zornFlowLinearEquiv D t Y := by
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv]
  rw [← coordMul_coordLE X Y]
  rw [← coordMul_coordLE
    (zornFlowLinearEquiv D t X)
    (zornFlowLinearEquiv D t Y)]
  rw [coordLE_zornFlowLinearEquiv]
  rw [coordLE_zornFlowLinearEquiv]
  simpa [coordFlow] using
    coordFlow_map_mul D hD t (coordLE X) (coordLE Y)

/-- Left unit law for the canonical Zorn multiplication. -/
private theorem zorn_one_mul (X : CZ) :
    (1 : CZ) * X = X := by
  rcases X with ⟨a, b, x, y⟩
  have h1 : (1 : CZ) =
      { a := 1, b := 1, x := 0, y := 0 } := rfl
  rw [h1]
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, cross]
  · simp [mul_def, mul, dot, cross]
  · funext i
    fin_cases i <;> simp [mul_def, mul, dot, cross]
  · funext i
    fin_cases i <;> simp [mul_def, mul, dot, cross]

/-- Right unit law for the canonical Zorn multiplication. -/
private theorem zorn_mul_one (X : CZ) :
    X * (1 : CZ) = X := by
  rcases X with ⟨a, b, x, y⟩
  have h1 : (1 : CZ) =
      { a := 1, b := 1, x := 0, y := 0 } := rfl
  rw [h1]
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, cross]
  · simp [mul_def, mul, dot, cross]
  · funext i
    fin_cases i <;> simp [mul_def, mul, dot, cross]
  · funext i
    fin_cases i <;> simp [mul_def, mul, dot, cross]

/-- A multiplicative bijective Zorn flow fixes the two-sided unit. -/
@[simp]
theorem zornFlow_map_one
    (D : EndCZ)
    (hD : CZD.IsDerivation D)
    (t : ℝ) :
    zornFlowLinearEquiv D t (1 : CZ) = 1 := by
  let y : CZ := (zornFlowLinearEquiv D t).symm 1
  have hy : zornFlowLinearEquiv D t y = (1 : CZ) := by
    dsimp [y]
    exact (zornFlowLinearEquiv D t).apply_symm_apply 1
  have hm := zornFlow_map_mul D hD t (1 : CZ) y
  rw [zorn_one_mul, hy, zorn_mul_one] at hm
  exact hm.symm

/-!
## Genuine multiplicative automorphisms
-/

/--
The full exponential family as native `MulEquiv`s.

`MulEquiv` packages a bijection and multiplication preservation without
imposing associativity, so it is appropriate for the Zorn algebra.
-/
noncomputable def zornFlowMulEquiv
    (D : CZD.canonicalZornDerivations)
    (t : ℝ) : CZ ≃* CZ where
  toEquiv := (zornFlowLinearEquiv D.1 t).toEquiv
  map_mul' := by
    intro X Y
    exact zornFlow_map_mul D.1 D.2 t X Y

@[simp]
theorem zornFlowMulEquiv_apply
    (D : CZD.canonicalZornDerivations)
    (t : ℝ)
    (X : CZ) :
    zornFlowMulEquiv D t X = zornFlowLinearEquiv D.1 t X := by
  rfl

/-- Time-zero multiplicative automorphism is pointwise the identity. -/
@[simp]
theorem zornFlowMulEquiv_zero_apply
    (D : CZD.canonicalZornDerivations)
    (X : CZ) :
    zornFlowMulEquiv D 0 X = X := by
  change zornFlowLinearEquiv D.1 0 X = X
  exact zornFlowLinearEquiv_zero_apply D.1 X

@[simp]
theorem zornFlowMulEquiv_map_one
    (D : CZD.canonicalZornDerivations)
    (t : ℝ) :
    zornFlowMulEquiv D t (1 : CZ) = 1 := by
  change zornFlowLinearEquiv D.1 t (1 : CZ) = 1
  exact zornFlow_map_one D.1 D.2 t

/-- The Zorn multiplicative automorphisms satisfy the pointwise group law. -/
theorem zornFlowMulEquiv_add_apply
    (D : CZD.canonicalZornDerivations)
    (s t : ℝ)
    (X : CZ) :
    zornFlowMulEquiv D (s + t) X =
      zornFlowMulEquiv D s (zornFlowMulEquiv D t X) := by
  exact zornFlowLinearEquiv_add_apply D.1 s t X

/-- Time-one exponential automorphism of a canonical Zorn derivation. -/
noncomputable def zornDerivationExpAutomorphism
    (D : CZD.canonicalZornDerivations) : CZ ≃* CZ :=
  zornFlowMulEquiv D 1

/-- Main time-one capstone: `exp(D)` preserves the Zorn product. -/
theorem zornDerivationExpAutomorphism_map_mul
    (D : CZD.canonicalZornDerivations)
    (X Y : CZ) :
    zornDerivationExpAutomorphism D (X * Y) =
      zornDerivationExpAutomorphism D X *
        zornDerivationExpAutomorphism D Y := by
  exact map_mul (zornDerivationExpAutomorphism D) X Y

@[simp]
theorem zornDerivationExpAutomorphism_map_one
    (D : CZD.canonicalZornDerivations) :
    zornDerivationExpAutomorphism D (1 : CZ) = 1 := by
  exact zornFlowMulEquiv_map_one D 1

/-- Backward-compatible multiplicativity packet. -/
theorem canonical_derivation_exponential_packet
    (D : CZD.canonicalZornDerivations)
    (t : ℝ)
    (X Y : CZ) :
    zornFlowMulEquiv D t (X * Y) =
      zornFlowMulEquiv D t X * zornFlowMulEquiv D t Y := by
  exact map_mul (zornFlowMulEquiv D t) X Y

/-- Complete finite-flow packet on the canonical Zorn carrier. -/
theorem canonical_derivation_exponential_full_packet
    (D : CZD.canonicalZornDerivations)
    (s t : ℝ)
    (X Y : CZ) :
    zornFlowMulEquiv D t (1 : CZ) = 1 ∧
      zornFlowMulEquiv D t (X * Y) =
        zornFlowMulEquiv D t X * zornFlowMulEquiv D t Y ∧
      zornFlowLinearEquiv D.1 (s + t) X =
        zornFlowLinearEquiv D.1 s (zornFlowLinearEquiv D.1 t X) ∧
      zornFlowLinearEquiv (-D.1) t (zornFlowLinearEquiv D.1 t X) = X := by
  exact ⟨
    zornFlowMulEquiv_map_one D t,
    map_mul (zornFlowMulEquiv D t) X Y,
    zornFlowLinearEquiv_add_apply D.1 s t X,
    zornFlowLinearEquiv_neg_apply D.1 t X⟩

end InfoGeometry.Lie.CanonicalZornDerivationExponential

end noncomputable section