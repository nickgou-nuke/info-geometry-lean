import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
import InfoGeometry.Canonical.ZornCliffordRepresentation
import InfoGeometry.Lie.ContinuousDerivationExponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Exponentiating canonical Zorn derivations

This file specializes the generic derivation exponential to the canonical
real Zorn split-octonion carrier.

The nonassociative Zorn multiplication is transported through the linear
equivalence

    coordLE : CZ ≃ₗ[ℝ] (Fin 8 → ℝ).

The coordinate space is finite-dimensional. Therefore every linear endomorphism
is continuous, and the transported Zorn multiplication is continuous.

The exponential flow is defined by transporting the derivation to its matrix
representation, applying the matrix exponential in the Frobenius-normed
matrix algebra, and transporting back.

No associative `AlgEquiv` structure is imposed on the split-octonion product.
The final automorphism is packaged as a `MulEquiv`.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornDerivationExponential

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
open InfoGeometry.Lie.ContinuousDerivationExponential

open InfoGeometry.Lie.CanonicalZornDerivation

abbrev CZ := CZ
abbrev EndCZ := EndCZ
abbrev V8 := Fin 8 → ℝ

open scoped Matrix.Norms.Frobenius

/-!
## Coordinate linear equivalence and basis
-/

/-- The coordinate function of the canonical linear equivalence. -/
def coordLEFun : CZ → V8 := fun X => fun i =>
  match i with
  | Fin.mk 0 _ => X.a
  | Fin.mk 1 _ => X.b
  | Fin.mk 2 _ => X.x 0
  | Fin.mk 3 _ => X.x 1
  | Fin.mk 4 _ => X.x 2
  | Fin.mk 5 _ => X.y 0
  | Fin.mk 6 _ => X.y 1
  | Fin.mk 7 _ => X.y 2

/-- The inverse coordinate function. -/
def coordLEFunInv : V8 → CZ := fun v =>
  {
    a := v 0,
    b := v 1,
    x := fun j => v (Fin.mk (j + 2) (by omega)),
    y := fun j => v (Fin.mk (j + 5) (by omega))
  }

/-- The canonical linear equivalence from `ZornMatrix ℝ` to `Fin 8 → ℝ`. -/
noncomputable def coordLE : CZ ≃ V8 := {
  toFun := coordLEFun,
  invFun := coordLEFunInv,
  left_inv := by
    intro X
    cases X with | mk a b x y =>
    ext
    · simp [coordLEFun, coordLEFunInv]
    · simp [coordLEFun, coordLEFunInv]
    · funext j
      fin_cases j <;> simp [coordLEFun, coordLEFunInv]
    · funext j
      fin_cases j <;> simp [coordLEFun, coordLEFunInv],
  right_inv := by
    intro v
    funext i
    fin_cases i <;> simp [coordLEFun, coordLEFunInv]
}

/-- `coordLE` is linear over `ℝ`. -/
noncomputable def coordLELinearEquiv : CZ ≃ₗ[ℝ] V8 := {
  toEquiv := coordLE,
  map_add' := by
    intro X Y
    funext i
    fin_cases i <;> simp [coordLEFun, coordLEFunInv],
  map_smul' := by
    intro r X
    funext i
    fin_cases i <;> simp [coordLEFun, coordLEFunInv]
}

/-- The standard basis of `V8` transported to `CZ`. -/
def zornBasis : Basis (Fin 8) ℝ CZ :=
  let basisVecs : Fin 8 → CZ := ![ 
    { a := 1, b := 0, x := ![0, 0, 0], y := ![0, 0, 0] }, -- e₀
    { a := 0, b := 1, x := ![0, 0, 0], y := ![0, 0, 0] }, -- e₁
    { a := 0, b := 0, x := ![1, 0, 0], y := ![0, 0, 0] }, -- e₂
    { a := 0, b := 0, x := ![0, 1, 0], y := ![0, 0, 0] }, -- e₃
    { a := 0, b := 0, x := ![0, 0, 1], y := ![0, 0, 0] }, -- e₄
    { a := 0, b := 0, x := ![0, 0, 0], y := ![1, 0, 0] }, -- e₅
    { a := 0, b := 0, x := ![0, 0, 0], y := ![0, 1, 0] }, -- e₆
    { a := 0, b := 0, x := ![0, 0, 0], y := ![0, 0, 1] }  -- e₇
  ]
  refine' ⟨basisVecs, _⟩
  -- Prove linear independence and spanning
  exact by
    refine' Basis.mk_of_injective_span_eq_top _
    · -- Linear independence
      intro g hg
      have h₁ := congr_fun hg 0
      have h₂ := congr_fun hg 1
      have h₃ := congr_fun hg 2
      have h₄ := congr_fun hg 3
      have h₅ := congr_fun hg 4
      have h₆ := congr_fun hg 5
      have h₇ := congr_fun hg 6
      have h₈ := congr_fun hg 7
      simp [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons] at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ ⊢
      <;>
      (try aesop) <;>
      (try simp_all [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons]) <;>
      (try norm_num at *) <;>
      (try linarith) <;>
      (try aesop)
    · -- Spanning
      apply Fintype.eq_of_injective (fun X => fun i => coordLE X i)
      intro X Y h
      apply coordLE.injective
      ext i
      fin_cases i <;> simp_all [coordLE_apply]
      <;> aesop

/-- The canonical linear equivalence as a linear equivalence. -/
abbrev coordLELin : CZ ≃ₗ[ℝ] V8 := coordLELinearEquiv

@[simp]
theorem coordLE_apply (X : CZ) (i : Fin 8) :
    coordLE X i = if i = 0 then X.a
    else if i = 1 then X.b
    else if i = 2 then X.x 0
    else if i = 3 then X.x 1
    else if i = 4 then X.x 2
    else if i = 5 then X.y 0
    else if i = 6 then X.y 1
    else X.y 2 := by
  rfl

@[simp]
theorem coordLE_symm_apply (v : V8) :
    coordLE.symm v =
      {
        a := v 0,
        b := v 1,
        x := fun j => v (Fin.mk (j + 2) (by omega)),
        y := fun j => v (Fin.mk (j + 5) (by omega))
      } := by
  rfl

/-!
## Transported Zorn multiplication
-/

/--
The transported Zorn multiplication as a bilinear linear map.
-/
def coordMulLinear :
    V8 →ₗ[ℝ] V8 →ₗ[ℝ] V8 where
  toFun u :=
    {
      toFun := fun v => coordLE (coordLE.symm u * coordLE.symm v)
      map_add' := by intro v w; simp [mul_add, map_add]
      map_smul' := by intro r v; simp [mul_smul, map_smul]
    }
  map_add' := by intro u v; ext w; simp [add_mul, map_add]
  map_smul' := by intro r u; ext v; simp [smul_mul, map_smul]

/--
The transported Zorn multiplication as a continuous bilinear map.

Continuity follows from finite dimensionality.
-/
noncomputable def coordMul :
    V8 →L[ℝ] V8 →L[ℝ] V8 :=
  coordMulLinear.toContinuousBilinearMap

@[simp]
theorem coordMul_apply (u v : V8) :
    coordMul u v = coordLE (coordLE.symm u * coordLE.symm v) := by
  rfl

@[simp]
theorem coordMul_coordLE (X Y : CZ) :
    coordMul (coordLE X) (coordLE Y) = coordLE (X * Y) := by
  simp [coordMul]

/-!
## Transported derivations
-/

/--
Transport a canonical Zorn linear endomorphism to the real
eight-dimensional coordinate carrier.
-/
def coordEndLinear (D : EndCZ) : V8 →ₗ[ℝ] V8 :=
  (coordLELin : CZ →ₗ[ℝ] V8).comp (D.comp (coordLELin.symm : V8 →ₗ[ℝ] CZ))

/--
Every transported endomorphism is continuous because `V8` is finite
dimensional.
-/
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

/-- Transport respects zero. -/
@[simp]
theorem coordEnd_zero : coordEnd (0 : EndCZ) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  simp [coordEnd_apply]

/-- Transport respects addition. -/
@[simp]
theorem coordEnd_add (D E : EndCZ) :
    coordEnd (D + E) = coordEnd D + coordEnd E := by
  apply ContinuousLinearMap.ext
  intro u
  simp [coordEnd_apply]

/-- Transport respects scalar multiplication. -/
@[simp]
theorem coordEnd_smul (r : ℝ) (D : EndCZ) :
    coordEnd (r • D) = r • coordEnd D := by
  apply ContinuousLinearMap.ext
  intro u
  simp [coordEnd_apply]

/-- Transport respects negation. -/
@[simp]
theorem coordEnd_neg (D : EndCZ) :
    coordEnd (-D) = -(coordEnd D) := by
  apply ContinuousLinearMap.ext
  intro u
  simp [coordEnd_apply]

/--
The Leibniz property survives coordinate transport.
-/
theorem coordEnd_isDerivation (D : EndCZ) (hD : IsDerivation D) :
    IsDerivation coordMul (coordEnd D) := by
  intro u v
  simp only [coordEnd_apply, coordMul_apply, Equiv.apply_symm_apply]
  rw [hD]
  rw [map_add]

/-!
## Coordinate exponential flow
-/

/-- The exponential flow on coordinates generated by a canonical Zorn endomorphism. -/
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

/-- Coordinate flow satisfies the pointwise additive parameter law. -/
theorem coordFlow_add_apply
    (D : EndCZ)
    (s t : ℝ)
    (u : V8) :
    coordFlow D (s + t) u =
      coordFlow D s (coordFlow D t u) := by
  simpa [coordFlow] using
    flow_add_apply (coordEnd D) s t u

/-- Negative coordinate flow is a left inverse. -/
@[simp]
theorem coordFlow_neg_apply_flow
    (D : EndCZ)
    (t : ℝ)
    (u : V8) :
    coordFlow (-D) t (coordFlow D t u) = u := by
  simp [coordFlow, coordEnd_neg]

/-- Positive coordinate flow is a left inverse of the negative-generator flow. -/
@[simp]
theorem coordFlow_apply_neg_flow
    (D : EndCZ)
    (t : ℝ)
    (u : V8) :
    coordFlow D t (coordFlow (-D) t u) = u := by
  simp [coordFlow, coordEnd_neg]

/-- The coordinate exponential flow of a derivation preserves transported Zorn multiplication. -/
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

/-!
## Transport the exponential back to the Zorn carrier
-/

/--
The exponential flow transported back to the canonical Zorn carrier.
Its inverse is the same construction for the negative generator.
-/
noncomputable def zornFlowLinearEquiv
    (D : EndCZ)
    (t : ℝ) :
    CZ ≃ₗ[ℝ] CZ :=
  (coordLELin.trans (flowLinearEquiv (coordEnd D) t)).trans coordLELin.symm

@[simp]
theorem zornFlowLinearEquiv_apply (D : EndCZ) (t : ℝ) (X : CZ) :
    zornFlowLinearEquiv D t X =
      coordLELin.symm (flow (coordEnd D) t (coordLE X)) := by
  simp [zornFlowLinearEquiv, flowLinearEquiv_apply, LinearEquiv.trans_apply]
  <;>
  simp_all [coordLELin]
  <;>
  rfl

@[simp]
theorem coordLE_zornFlowLinearEquiv (D : EndCZ) (t : ℝ) (X : CZ) :
    coordLE (zornFlowLinearEquiv D t X) =
      flow (coordEnd D) t (coordLE X) := by
  rw [zornFlowLinearEquiv_apply]
  <;>
  simp [coordLELin, LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply]
  <;>
  rfl

/-- Time zero is the identity on the canonical Zorn carrier. -/
@[simp]
theorem zornFlowLinearEquiv_zero_apply
    (D : EndCZ)
    (X : CZ) :
    zornFlowLinearEquiv D 0 X = X := by
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv]
  simp [flow_zero]

/-- Time zero is the identity linear equivalence. -/
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
  rw [coordLE_zornFlowLinearEquiv, coordLE_zornFlowLinearEquiv, coordLE_zornFlowLinearEquiv]
  exact flow_add_apply (coordEnd D) s t (coordLE X)

/-- Negating the generator reverses the time parameter after Zorn transport. -/
@[simp]
theorem zornFlowLinearEquiv_neg_generator
    (D : EndCZ)
    (t : ℝ) :
    zornFlowLinearEquiv (-D) t = zornFlowLinearEquiv D (-t) := by
  apply LinearEquiv.ext
  intro X
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv]
  rw [coordEnd_neg]
  have h := flow_neg_generator (coordEnd D) t
  rw [h]
  <;>
  simp [coordLE_zornFlowLinearEquiv]
  <;>
  rfl

/-- The negative-generator flow is a left inverse of the positive flow. -/
@[simp]
theorem zornFlowLinearEquiv_neg_apply
    (D : EndCZ)
    (t : ℝ)
    (X : CZ) :
    zornFlowLinearEquiv (-D) t (zornFlowLinearEquiv D t X) = X := by
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv, coordLE_zornFlowLinearEquiv]
  rw [coordEnd_neg]
  exact flow_neg_apply_flow (coordEnd D) t (coordLE X)

/-- The positive flow is a left inverse of the negative-generator flow. -/
@[simp]
theorem zornFlowLinearEquiv_apply_neg
    (D : EndCZ)
    (t : ℝ)
    (X : CZ) :
    zornFlowLinearEquiv D t (zornFlowLinearEquiv (-D) t X) = X := by
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv, coordLE_zornFlowLinearEquiv]
  rw [coordEnd_neg]
  exact flow_apply_flow_neg (coordEnd D) t (coordLE X)

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
## Multiplicativity
-/

/--
A canonical Zorn derivation exponentiates to a multiplication-preserving
linear equivalence of the nonassociative split-octonion carrier.
-/
theorem zornFlow_map_mul
    (D : EndCZ)
    (hD : IsDerivation D)
    (t : ℝ)
    (X Y : CZ) :
    zornFlowLinearEquiv D t (X * Y) =
      zornFlowLinearEquiv D t X *
        zornFlowLinearEquiv D t Y := by
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv]
  rw [← coordMul_coordLE X Y]
  rw [← coordMul_coordLE (zornFlowLinearEquiv D t X) (zornFlowLinearEquiv D t Y)]
  rw [coordLE_zornFlowLinearEquiv, coordLE_zornFlowLinearEquiv]
  -- Use the generic derivation exponential's multiplicativity
  have h₁ : IsDerivation coordMul (coordEnd D) := coordEnd_isDerivation D hD
  have h₂ : coordFlow D t (coordMul (coordLE X) (coordLE Y)) = coordMul (coordFlow D t (coordLE X)) (coordFlow D t (coordLE Y)) := by
    apply flow_map_mul
    exact h₁
  simpa [coordFlow, coordMul_coordLE] using h₂

/-- A multiplicative bijective Zorn flow fixes the unique two-sided unit. -/
@[simp]
theorem zornFlow_map_one
    (D : EndCZ)
    (hD : IsDerivation D)
    (t : ℝ) :
    zornFlowLinearEquiv D t (1 : CZ) = 1 := by
  have h₂ : zornFlowLinearEquiv D t ((zornFlowLinearEquiv D t).symm 1) = 1 := by
    apply LinearEquiv.apply_symm_apply
  have h₃ : zornFlowLinearEquiv D t (1 * ((zornFlowLinearEquiv D t).symm 1)) = zornFlowLinearEquiv D t 1 * zornFlowLinearEquiv D t ((zornFlowLinearEquiv D t).symm 1) := by
    apply zornFlow_map_mul D hD t
  have h₄ : (1 : CZ) * ((zornFlowLinearEquiv D t).symm 1) = (zornFlowLinearEquiv D t).symm 1 := by simp [one_mul]
  rw [h₄] at h₃
  have h₅ : zornFlowLinearEquiv D t ((zornFlowLinearEquiv D t).symm 1) = zornFlowLinearEquiv D t 1 * 1 := by
    calc
      zornFlowLinearEquiv D t ((zornFlowLinearEquiv D t).symm 1) = zornFlowLinearEquiv D t (1 * ((zornFlowLinearEquiv D t).symm 1)) := by simp [one_mul]
      _ = zornFlowLinearEquiv D t 1 * zornFlowLinearEquiv D t ((zornFlowLinearEquiv D t).symm 1) := by
        apply zornFlow_map_mul D hD t
      _ = zornFlowLinearEquiv D t 1 * 1 := by rw [h₂]
  have h₆ : zornFlowLinearEquiv D t 1 = 1 := by
    calc
      zornFlowLinearEquiv D t 1 = zornFlowLinearEquiv D t 1 * 1 := by simp
      _ = zornFlowLinearEquiv D t ((zornFlowLinearEquiv D t).symm 1) := by rw [h₅]
      _ = 1 := by rw [h₂]
  exact h₆

/-!
## One-parameter group law on the Zorn carrier
-/

/--
Pointwise one-parameter group law on the Zorn carrier.
-/
theorem zornFlowLinearEquiv_add_apply
    (D : EndCZ)
    (s t : ℝ)
    (X : CZ) :
    zornFlowLinearEquiv D (s + t) X =
      zornFlowLinearEquiv D s
        (zornFlowLinearEquiv D t X) := by
  apply coordLE.injective
  rw [coordLE_zornFlowLinearEquiv, coordLE_zornFlowLinearEquiv, coordLE_zornFlowLinearEquiv]
  exact flow_add_apply (coordEnd D) s t (coordLE X)

/-!
## Genuine multiplicative automorphisms
-/

/--
The full exponential family as native `MulEquiv`s.

`MulEquiv` requires a bijection and preservation of multiplication. It does
not impose associativity on the multiplication, so it is appropriate for the
Zorn split-octonion carrier.
-/
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
    zornFlowMulEquiv D t X = zornFlowLinearEquiv D.1 t X := by
  rfl

/-- Time-zero multiplicative automorphism is pointwise the identity. -/
@[simp]
theorem zornFlowMulEquiv_zero_apply
    (D : canonicalZornDerivations)
    (X : CZ) :
    zornFlowMulEquiv D 0 X = X := by
  simp [zornFlowMulEquiv]
  <;> simp [zornFlowLinearEquiv_zero_apply]

/--
Time-one multiplicative automorphism preserves the unit.
-/
@[simp]
theorem zornFlowMulEquiv_map_one
    (D : canonicalZornDerivations)
    (t : ℝ) :
    zornFlowMulEquiv D t (1 : CZ) = 1 := by
  change zornFlowLinearEquiv D.1 t (1 : CZ) = 1
  exact zornFlow_map_one D.1 D.2 t

/--
The Zorn multiplicative automorphisms satisfy the one-parameter group law
pointwise.
-/
theorem zornFlowMulEquiv_add_apply
    (D : canonicalZornDerivations)
    (s t : ℝ)
    (X : CZ) :
    zornFlowMulEquiv D (s + t) X =
      zornFlowMulEquiv D s
        (zornFlowMulEquiv D t X) := by
  exact zornFlowLinearEquiv_add_apply D.1 s t X

/--
Time-one exponential automorphism of a canonical Zorn derivation.
-/
noncomputable def zornDerivationExpAutomorphism
    (D : canonicalZornDerivations) : CZ ≃* CZ :=
  zornFlowMulEquiv D 1

/--
Main time-one capstone:

`exp(D)` preserves the Zorn product.
-/
theorem zornDerivationExpAutomorphism_map_mul
    (D : canonicalZornDerivations)
    (X Y : CZ) :
    zornDerivationExpAutomorphism D (X * Y) =
      zornDerivationExpAutomorphism D X *
        zornDerivationExpAutomorphism D Y := by
  exact map_mul (zornDerivationExpAutomorphism D) X Y

@[simp]
theorem zornDerivationExpAutomorphism_map_one
    (D : canonicalZornDerivations) :
    zornDerivationExpAutomorphism D (1 : CZ) = 1 := by
  exact zornFlowMulEquiv_map_one D 1

/-- Backward-compatible multiplicativity packet. -/
theorem canonical_derivation_exponential_packet
    (D : canonicalZornDerivations)
    (t : ℝ)
    (X Y : CZ) :
    zornFlowMulEquiv D t (X * Y) =
      zornFlowMulEquiv D t X * zornFlowMulEquiv D t Y := by
  exact map_mul (zornFlowMulEquiv D t) X Y

/-- Complete finite-flow packet on the canonical Zorn carrier. -/
theorem canonical_derivation_exponential_full_packet
    (D : canonicalZornDerivations)
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