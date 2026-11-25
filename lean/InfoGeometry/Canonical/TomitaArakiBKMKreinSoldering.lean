/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SouriauOnsagerBKMIntegrability
import InfoGeometry.Canonical.SouriauOnsagerBKMPositivity
import InfoGeometry.Krein.DoubledSpace
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Tomita–Takesaki / Araki Standard-Form Natural-Cone Soldering & Doubled Krein Weld

This module supplies the typed morphism weld (Soldering Way II) connecting
three previously separate families in the repository DAG:
- `SouriauOnsagerBKM.FaithfulDensityOperator` (`kuboMoriTransform`, `kuboMoriPairing`),
- finite-dimensional Tomita–Takesaki / Araki modular theory (`tomitaJ`, `modularOp`,
  `relativeModularOp`, `naturalConeVector`, `relativeTomitaS`, `relativeTomitaF`), and
- `InfoGeometry.Krein.DoubledSpace` (`modular_j`, `spectral_epsilon`, `complex_i`).

1. **Hilbert–Schmidt standard form, left/right actions, & Tomita conjugation `tomitaJ`:**
   Equips `FiniteOperatorAlgebra n` with the Hilbert–Schmidt pairing
   `hsInner X Y := finiteOperatorTrace (star X * Y)` and proves the commutant
   intertwining identity `tomitaJ (leftMulLinear A (tomitaJ X)) = rightMulLinear (star A) X`
   together with anti-unitarity `hsInner (tomitaJ X) (tomitaJ Y) = hsInner Y X`.
2. **Araki natural-cone vector, modular & relative modular operators:**
   Constructs `naturalConeVector D := D.rpow (1 / 2)`, proving the Araki GNS state
   soldering identity `hsInner (naturalConeVector D) (leftMulLinear A (naturalConeVector D)) = Tr(D.rho * A)`,
   the one-parameter modular group law `relativeModularOp D₁ D₂ (s + t) = ...`, modular
   invariance `modularOp D s (naturalConeVector D) = naturalConeVector D`, exact
   Araki polar decompositions `S_{D₁, D₂} = J ∘ Δ_{D₁, D₂}^{1/2} = Δ_{D₂, D₁}^{-1/2} ∘ J`,
   and the Tomita factorization `relativeTomitaF D₁ D₂ (relativeTomitaS D₁ D₂ X) = relativeModularOp D₁ D₂ 1 X`.
3. **BKM–Tomita–Araki intertwiner & algebraic KMS boundary law:**
   Proves `D.kuboMoriTransform A = ∫ s in 0..1, modularOp D s (A * D.rho)`,
   `D.kuboMoriPairing A B = ∫ s in 0..1, hsInner (A * naturalConeVector D) (modularOp D s (B * naturalConeVector D))`,
   and the exact KMS boundary relation `Tr(D.rho * (A * modularOp D 1 B)) = Tr(D.rho * (B * A))`.
4. **Real Hilbert–Schmidt carrier `HSRealSelfAdjoint n` & typed `LinearEquiv` to `DoubledSpace`:**
   Builds the complete finite-dimensional real Hilbert space `HSRealSelfAdjoint n` of
   self-adjoint operators and the canonical `ℝ`-linear equivalence
   `operatorToDoubledKrein n : FiniteOperatorAlgebra n ≃ₗ[ℝ] DoubledSpace (HSRealSelfAdjoint n)`
   intertwining `tomitaJ ↔ modular_j`, `X ↦ i X* ↔ spectral_epsilon`,
   `X ↦ -i X ↔ complex_i`, the Hilbert–Schmidt metric up to factor `2`,
   and conjugating `modularOp` / `kuboMoriTransform` onto `DoubledSpace`.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace InfoGeometry.Canonical.TomitaArakiBKMKreinSoldering

open MeasureTheory
open scoped Interval RealInnerProductSpace
open SouriauOnsagerBKM
open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

/-! ## Section 1: Hilbert–Schmidt Standard Form, Left/Right Actions, & Tomita `J` -/

section HilbertSchmidtStandardForm

variable {n : ℕ}

/-- Complex Hilbert–Schmidt pairing `⟨X, Y⟩_HS = Tr(X* Y)` on `FiniteOperatorAlgebra n`. -/
def hsInner (X Y : FiniteOperatorAlgebra n) : ℂ :=
  finiteOperatorTrace (star X * Y)

theorem hsInner_conj_symm (X Y : FiniteOperatorAlgebra n) :
    star (hsInner X Y) = hsInner Y X := by
  unfold hsInner
  rw [← finiteOperatorTrace_star, star_mul, star_star]

theorem hsInner_self_re_nonneg (X : FiniteOperatorAlgebra n) :
    0 ≤ (hsInner X X).re :=
  finiteOperatorTrace_star_mul_self_re_nonneg X

theorem hsInner_self_re_pos {X : FiniteOperatorAlgebra n} (hX : X ≠ 0) :
    0 < (hsInner X X).re :=
  finiteOperatorTrace_star_mul_self_re_pos X hX

theorem hsInner_eq_zero_iff (X : FiniteOperatorAlgebra n) :
    (hsInner X X).re = 0 ↔ X = 0 :=
  finiteOperatorTrace_star_mul_self_re_eq_zero_iff X

theorem hsInner_add_right (X Y Z : FiniteOperatorAlgebra n) :
    hsInner X (Y + Z) = hsInner X Y + hsInner X Z := by
  unfold hsInner
  rw [mul_add]
  exact map_add (finiteOperatorTraceLinear n) _ _

theorem hsInner_smul_right (c : ℂ) (X Y : FiniteOperatorAlgebra n) :
    hsInner X (c • Y) = c * hsInner X Y := by
  unfold hsInner
  rw [mul_smul_comm]
  exact map_smul (finiteOperatorTraceLinear n) c _

theorem hsInner_mul_left (A X Y : FiniteOperatorAlgebra n) :
    hsInner X (A * Y) = hsInner (star A * X) Y := by
  unfold hsInner
  rw [star_mul, mul_assoc, star_star]

theorem hsInner_mul_right (B X Y : FiniteOperatorAlgebra n) :
    hsInner X (Y * B) = hsInner (X * star B) Y := by
  unfold hsInner
  rw [star_mul, star_star]
  calc
    finiteOperatorTrace (star X * (Y * B))
        = finiteOperatorTrace ((star X * Y) * B) := by rw [← mul_assoc]
    _ = finiteOperatorTrace (B * (star X * Y)) := finiteOperatorTrace_mul_comm _ _
    _ = finiteOperatorTrace ((B * star X) * Y) := by rw [mul_assoc]

/-- Left multiplication representation `L_A(X) = A * X`. -/
def leftMulLinear (A : FiniteOperatorAlgebra n) :
    FiniteOperatorAlgebra n →ₗ[ℂ] FiniteOperatorAlgebra n where
  toFun X := A * X
  map_add' _ _ := mul_add A _ _
  map_smul' c X := mul_smul_comm c A X

/-- Right multiplication representation `R_B(X) = X * B`. -/
def rightMulLinear (B : FiniteOperatorAlgebra n) :
    FiniteOperatorAlgebra n →ₗ[ℂ] FiniteOperatorAlgebra n where
  toFun X := X * B
  map_add' _ _ := add_mul _ _ B
  map_smul' c X := smul_mul_assoc c X B

@[simp] theorem leftMulLinear_apply (A X : FiniteOperatorAlgebra n) :
    leftMulLinear A X = A * X :=
  rfl

@[simp] theorem rightMulLinear_apply (B X : FiniteOperatorAlgebra n) :
    rightMulLinear B X = X * B :=
  rfl

/-- `FiniteOperatorAlgebra n →ₐ[ℂ] Module.End ℂ (FiniteOperatorAlgebra n)` via left multiplication. -/
def leftMulAlgHom (n : ℕ) :
    FiniteOperatorAlgebra n →ₐ[ℂ] Module.End ℂ (FiniteOperatorAlgebra n) where
  toFun := leftMulLinear
  map_one' := by ext X; simp
  map_mul' A B := by ext X; simp [mul_assoc]
  map_zero' := by ext X; simp
  map_add' A B := by ext X; simp [add_mul]
  commutes' c := by ext X; simp [Algebra.algebraMap_eq_smul_one]

/-- Left and right actions commute: `[L_A, R_B] = 0`. -/
theorem leftMul_comm_rightMul (A B X : FiniteOperatorAlgebra n) :
    leftMulLinear A (rightMulLinear B X) = rightMulLinear B (leftMulLinear A X) := by
  simp [mul_assoc]

/-- Tomita modular conjugation `J(X) = X*` on the Hilbert–Schmidt standard form. -/
def tomitaJ (X : FiniteOperatorAlgebra n) : FiniteOperatorAlgebra n :=
  star X

@[simp] theorem tomitaJ_involutive (X : FiniteOperatorAlgebra n) :
    tomitaJ (tomitaJ X) = X :=
  star_star X

theorem tomitaJ_add (X Y : FiniteOperatorAlgebra n) :
    tomitaJ (X + Y) = tomitaJ X + tomitaJ Y :=
  star_add X Y

theorem tomitaJ_real_smul (r : ℝ) (X : FiniteOperatorAlgebra n) :
    tomitaJ (r • X) = r • tomitaJ X := by
  change star ((r : ℂ) • X) = (r : ℂ) • star X
  rw [star_smul, Complex.star_def, Complex.conj_ofReal]

/-- **Tomita Commutant Theorem** (`J L_A J = R_{A*}`). -/
theorem tomitaJ_leftMul_tomitaJ (A X : FiniteOperatorAlgebra n) :
    tomitaJ (leftMulLinear A (tomitaJ X)) = rightMulLinear (star A) X := by
  simp [tomitaJ, star_mul]

/-- Anti-unitarity of Tomita conjugation `J` on the Hilbert–Schmidt pairing:
`⟨J X, J Y⟩_HS = ⟨Y, X⟩_HS`. -/
theorem hsInner_tomitaJ (X Y : FiniteOperatorAlgebra n) :
    hsInner (tomitaJ X) (tomitaJ Y) = hsInner Y X := by
  unfold hsInner tomitaJ
  rw [star_star, finiteOperatorTrace_mul_comm]

end HilbertSchmidtStandardForm

/-! ## Section 2: Araki Natural Cone, Modular Operator `Δ`, & Polar Decomposition -/

section ArakiModularTheory

variable {n : ℕ}

/-- Canonical cyclic and separating vector `ξ_D = ρ^{1/2}` in the Araki natural positive cone. -/
def naturalConeVector (D : FaithfulDensityOperator n) : FiniteOperatorAlgebra n :=
  D.rpow (1 / 2 : ℝ)

@[simp] theorem star_naturalConeVector (D : FaithfulDensityOperator n) :
    star (naturalConeVector D) = naturalConeVector D :=
  D.star_rpow (1 / 2 : ℝ)

@[simp] theorem naturalConeVector_mul_self (D : FaithfulDensityOperator n) :
    naturalConeVector D * naturalConeVector D = D.rho := by
  unfold naturalConeVector
  rw [← D.rpow_add]
  have h : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  rw [h, D.rpow_one]

/-- **Araki Natural-Cone State Soldering**: `⟨ξ_D, L_A ξ_D⟩_HS = Tr(ρ A)`. -/
theorem hsInner_naturalConeVector_leftMul
    (D : FaithfulDensityOperator n) (A : FiniteOperatorAlgebra n) :
    hsInner (naturalConeVector D) (leftMulLinear A (naturalConeVector D)) =
      finiteOperatorTrace (D.rho * A) := by
  unfold hsInner
  rw [leftMulLinear_apply, star_naturalConeVector, ← mul_assoc, finiteOperatorTrace_mul_comm,
    ← mul_assoc, naturalConeVector_mul_self]

theorem hsInner_naturalConeVector_self (D : FaithfulDensityOperator n) :
    hsInner (naturalConeVector D) (naturalConeVector D) = 1 := by
  unfold hsInner
  rw [star_naturalConeVector, naturalConeVector_mul_self, D.trace_one]

/-- Araki relative modular operator power `Δ_{D₁, D₂}^s(X) = D₁^s X D₂^{-s}`. -/
def relativeModularOp (D₁ D₂ : FaithfulDensityOperator n) (s : ℝ) :
    FiniteOperatorAlgebra n →ₗ[ℂ] FiniteOperatorAlgebra n where
  toFun X := D₁.rpow s * X * D₂.rpow (-s)
  map_add' X Y := by simp [mul_add, add_mul]
  map_smul' c X := by simp [mul_smul_comm, smul_mul_assoc]

@[simp] theorem relativeModularOp_apply
    (D₁ D₂ : FaithfulDensityOperator n) (s : ℝ) (X : FiniteOperatorAlgebra n) :
    relativeModularOp D₁ D₂ s X = D₁.rpow s * X * D₂.rpow (-s) :=
  rfl

/-- Tomita–Takesaki modular operator power `Δ_D^s(X) = ρ^s X ρ^{-s}`. -/
def modularOp (D : FaithfulDensityOperator n) (s : ℝ) :
    FiniteOperatorAlgebra n →ₗ[ℂ] FiniteOperatorAlgebra n :=
  relativeModularOp D D s

@[simp] theorem modularOp_apply
    (D : FaithfulDensityOperator n) (s : ℝ) (X : FiniteOperatorAlgebra n) :
    modularOp D s X = D.rpow s * X * D.rpow (-s) :=
  rfl

@[simp] theorem relativeModularOp_zero
    (D₁ D₂ : FaithfulDensityOperator n) (X : FiniteOperatorAlgebra n) :
    relativeModularOp D₁ D₂ 0 X = X := by
  simp

theorem relativeModularOp_add
    (D₁ D₂ : FaithfulDensityOperator n) (s t : ℝ) (X : FiniteOperatorAlgebra n) :
    relativeModularOp D₁ D₂ (s + t) X =
      relativeModularOp D₁ D₂ s (relativeModularOp D₁ D₂ t X) := by
  unfold relativeModularOp
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [D₁.rpow_add s t]
  have hneg : -(s + t) = -t + -s := by ring
  rw [hneg, D₂.rpow_add (-t) (-s)]
  simp only [mul_assoc]

theorem tomitaJ_relativeModularOp_tomitaJ
    (D₁ D₂ : FaithfulDensityOperator n) (s : ℝ) (X : FiniteOperatorAlgebra n) :
    tomitaJ (relativeModularOp D₁ D₂ s (tomitaJ X)) =
      relativeModularOp D₂ D₁ (-s) X := by
  simp [tomitaJ, star_mul, mul_assoc]

/-- Modular invariance of the natural-cone vector: `Δ_D^s(ξ_D) = ξ_D`. -/
theorem modularOp_naturalConeVector (D : FaithfulDensityOperator n) (s : ℝ) :
    modularOp D s (naturalConeVector D) = naturalConeVector D := by
  unfold modularOp relativeModularOp naturalConeVector
  simp only [LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]
  rw [← D.rpow_add (1 / 2 : ℝ) (-s), ← D.rpow_add s ((1 / 2 : ℝ) + -s)]
  congr 1
  ring

/-- Araki relative Tomita operator `S_{D₁, D₂}(X) = D₂^{-1/2} X* D₁^{1/2}`
satisfying `S_{D₁, D₂}(A ξ_{D₂}) = A* ξ_{D₁}`. -/
def relativeTomitaS (D₁ D₂ : FaithfulDensityOperator n) (X : FiniteOperatorAlgebra n) :
    FiniteOperatorAlgebra n :=
  D₂.rpow (-(1 / 2 : ℝ)) * star X * D₁.rpow (1 / 2 : ℝ)

/-- Dual relative Tomita operator `F_{D₁, D₂}(Y) = D₁^{1/2} Y* D₂^{-1/2}`. -/
def relativeTomitaF (D₁ D₂ : FaithfulDensityOperator n) (Y : FiniteOperatorAlgebra n) :
    FiniteOperatorAlgebra n :=
  D₁.rpow (1 / 2 : ℝ) * star Y * D₂.rpow (-(1 / 2 : ℝ))

/-- Tomita operator `S_D(X) = ρ^{-1/2} X* ρ^{1/2}`. -/
def tomitaS (D : FaithfulDensityOperator n) (X : FiniteOperatorAlgebra n) :
    FiniteOperatorAlgebra n :=
  relativeTomitaS D D X

/-- **Araki GNS defining relation**: `S_{D₁, D₂}(A ξ_{D₂}) = A* ξ_{D₁}`. -/
theorem relativeTomitaS_mul_naturalCone
    (D₁ D₂ : FaithfulDensityOperator n) (A : FiniteOperatorAlgebra n) :
    relativeTomitaS D₁ D₂ (A * naturalConeVector D₂) = star A * naturalConeVector D₁ := by
  unfold relativeTomitaS naturalConeVector
  rw [star_mul, D₂.star_rpow]
  calc
    D₂.rpow (-(1 / 2 : ℝ)) * (D₂.rpow (1 / 2 : ℝ) * star A) * D₁.rpow (1 / 2 : ℝ)
        = (D₂.rpow (-(1 / 2 : ℝ)) * D₂.rpow (1 / 2 : ℝ)) * star A * D₁.rpow (1 / 2 : ℝ) := by
          simp only [mul_assoc]
    _ = D₂.rpow (-(1 / 2 : ℝ) + (1 / 2 : ℝ)) * star A * D₁.rpow (1 / 2 : ℝ) := by
          rw [D₂.rpow_add]
    _ = star A * D₁.rpow (1 / 2 : ℝ) := by
          have h : -(1 / 2 : ℝ) + (1 / 2 : ℝ) = 0 := by norm_num
          rw [h, D₂.rpow_zero, one_mul]

/-- Involutive law for single-state Tomita operator: `S_D(S_D(X)) = X`. -/
@[simp] theorem tomitaS_involutive
    (D : FaithfulDensityOperator n) (X : FiniteOperatorAlgebra n) :
    tomitaS D (tomitaS D X) = X := by
  unfold tomitaS relativeTomitaS
  simp only [star_mul, star_star, D.star_rpow]
  have h1 : -(1 / 2 : ℝ) + (1 / 2 : ℝ) = 0 := by norm_num
  have h2 : (1 / 2 : ℝ) + -(1 / 2 : ℝ) = 0 := by norm_num
  calc
    D.rpow (-(1 / 2 : ℝ)) * (D.rpow (1 / 2 : ℝ) * X * D.rpow (-(1 / 2 : ℝ))) * D.rpow (1 / 2 : ℝ)
        = (D.rpow (-(1 / 2 : ℝ)) * D.rpow (1 / 2 : ℝ)) * X *
            (D.rpow (-(1 / 2 : ℝ)) * D.rpow (1 / 2 : ℝ)) := by
          simp only [mul_assoc]
    _ = D.rpow (-(1 / 2 : ℝ) + (1 / 2 : ℝ)) * X * D.rpow (-(1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
          rw [D.rpow_add]
    _ = X := by
          rw [h1, D.rpow_zero, one_mul, mul_one]

/-- Anti-adjointness `⟨S_{D₁, D₂} X, Y⟩_HS = ⟨F_{D₁, D₂} Y, X⟩_HS`. -/
theorem hsInner_relativeTomitaS_eq_relativeTomitaF
    (D₁ D₂ : FaithfulDensityOperator n) (X Y : FiniteOperatorAlgebra n) :
    hsInner (relativeTomitaS D₁ D₂ X) Y = hsInner (relativeTomitaF D₁ D₂ Y) X := by
  unfold hsInner relativeTomitaS relativeTomitaF
  simp only [star_mul, star_star, D₁.star_rpow, D₂.star_rpow]
  calc
    finiteOperatorTrace (D₁.rpow (1 / 2 : ℝ) * X * D₂.rpow (-(1 / 2 : ℝ)) * Y)
        = finiteOperatorTrace ((D₁.rpow (1 / 2 : ℝ) * X) * (D₂.rpow (-(1 / 2 : ℝ)) * Y)) := by
            simp only [mul_assoc]
    _ = finiteOperatorTrace ((D₂.rpow (-(1 / 2 : ℝ)) * Y) * (D₁.rpow (1 / 2 : ℝ) * X)) :=
            finiteOperatorTrace_mul_comm _ _
    _ = finiteOperatorTrace (D₂.rpow (-(1 / 2 : ℝ)) * Y * D₁.rpow (1 / 2 : ℝ) * X) := by
            simp only [mul_assoc]

/-- **Araki polar decomposition (form 1)**: `S_{D₁, D₂} = J ∘ Δ_{D₁, D₂}^{1/2}`. -/
theorem relativeTomitaS_eq_tomitaJ_comp_relativeModularOp
    (D₁ D₂ : FaithfulDensityOperator n) (X : FiniteOperatorAlgebra n) :
    relativeTomitaS D₁ D₂ X = tomitaJ (relativeModularOp D₁ D₂ (1 / 2 : ℝ) X) := by
  unfold relativeTomitaS tomitaJ relativeModularOp
  simp [star_mul, mul_assoc]

/-- **Araki polar decomposition (form 2)**: `S_{D₁, D₂} = Δ_{D₂, D₁}^{-1/2} ∘ J`. -/
theorem relativeTomitaS_eq_relativeModularOp_comp_tomitaJ
    (D₁ D₂ : FaithfulDensityOperator n) (X : FiniteOperatorAlgebra n) :
    relativeTomitaS D₁ D₂ X = relativeModularOp D₂ D₁ (-(1 / 2 : ℝ)) (tomitaJ X) := by
  simp [relativeTomitaS, relativeModularOp, tomitaJ]

/-- **Tomita modular factorization**: `F_{D₁, D₂} ∘ S_{D₁, D₂} = Δ_{D₁, D₂}^1`. -/
theorem relativeTomitaF_comp_relativeTomitaS
    (D₁ D₂ : FaithfulDensityOperator n) (X : FiniteOperatorAlgebra n) :
    relativeTomitaF D₁ D₂ (relativeTomitaS D₁ D₂ X) = relativeModularOp D₁ D₂ 1 X := by
  unfold relativeTomitaF relativeTomitaS relativeModularOp
  simp only [LinearMap.coe_mk, AddHom.coe_mk, star_mul, star_star, D₁.star_rpow, D₂.star_rpow]
  rw [← mul_assoc, ← mul_assoc, ← D₁.rpow_add]
  have h1 : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  have h2 : -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = -1 := by norm_num
  rw [h1, mul_assoc, mul_assoc, ← D₂.rpow_add, h2, ← mul_assoc]

end ArakiModularTheory

/-! ## Section 3: Exact BKM–Tomita–Araki Intertwiner & Algebraic KMS Law -/

section BKMTomitaIntertwiner

variable {n : ℕ}

/-- Pointwise intertwining of `modularInterpolation` and `modularOp`:
`ρ^s A ρ^{1-s} = Δ_D^s (A * ρ)`. -/
theorem modularInterpolation_eq_modularOp_mul_rho
    (D : FaithfulDensityOperator n) (s : ℝ) (A : FiniteOperatorAlgebra n) :
    D.modularInterpolation s A = modularOp D s (A * D.rho) := by
  unfold FaithfulDensityOperator.modularInterpolation modularOp relativeModularOp
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [← D.rpow_one]
  simp only [mul_assoc]
  rw [← D.rpow_add 1 (-s), sub_eq_add_neg]

/-- Integrated operator-valued BKM–Tomita–Araki intertwiner:
`K_D(A) = ∫₀¹ Δ_D^s (A ρ) ds`. -/
theorem kuboMoriTransform_eq_integral_modularOp
    (D : FaithfulDensityOperator n) (A : FiniteOperatorAlgebra n) :
    D.kuboMoriTransform A = ∫ s in (0 : ℝ)..1, modularOp D s (A * D.rho) := by
  unfold FaithfulDensityOperator.kuboMoriTransform
  simp_rw [modularInterpolation_eq_modularOp_mul_rho D]

/-- Hilbert–Schmidt GNS representation of the Kubo–Mori integrand:
`⟨A, B⟩_{BKM,s} = ⟨A ξ_D, Δ_D^{1-s}(B ξ_D)⟩_HS`. -/
theorem kuboMoriIntegrand_eq_hsInner_modularOp
    (D : FaithfulDensityOperator n) (A B : FiniteOperatorAlgebra n) (s : ℝ) :
    D.kuboMoriIntegrand A B s =
      hsInner (A * naturalConeVector D) (modularOp D (1 - s) (B * naturalConeVector D)) := by
  unfold FaithfulDensityOperator.kuboMoriIntegrand hsInner modularOp relativeModularOp naturalConeVector
  simp only [LinearMap.coe_mk, AddHom.coe_mk, star_mul, D.star_rpow]
  have hexp : (1 / 2 : ℝ) + -(1 - s) = s - 1 / 2 := by ring
  have hexp2 : (s - 1 / 2 : ℝ) + (1 / 2 : ℝ) = s := by ring
  have hsplit :
      D.rpow (1 / 2 : ℝ) * star A * (D.rpow (1 - s) * (B * D.rpow (1 / 2 : ℝ)) * D.rpow (-(1 - s))) =
        (D.rpow (1 / 2 : ℝ) * star A * D.rpow (1 - s) * B) * D.rpow (s - 1 / 2 : ℝ) := by
    calc
      D.rpow (1 / 2 : ℝ) * star A * (D.rpow (1 - s) * (B * D.rpow (1 / 2 : ℝ)) * D.rpow (-(1 - s)))
          = D.rpow (1 / 2 : ℝ) * star A * D.rpow (1 - s) * B * (D.rpow (1 / 2 : ℝ) * D.rpow (-(1 - s))) := by
            simp only [mul_assoc]
      _ = (D.rpow (1 / 2 : ℝ) * star A * D.rpow (1 - s) * B) * D.rpow (s - 1 / 2 : ℝ) := by
            rw [← D.rpow_add (1 / 2 : ℝ) (-(1 - s)), hexp]
  rw [hsplit, finiteOperatorTrace_mul_comm]
  calc
    finiteOperatorTrace (B * D.rpow s * star A * D.rpow (1 - s))
        = finiteOperatorTrace (B * (D.rpow s * star A * D.rpow (1 - s))) := by
          simp only [mul_assoc]
    _ = finiteOperatorTrace ((D.rpow s * star A * D.rpow (1 - s)) * B) :=
          finiteOperatorTrace_mul_comm _ _
    _ = finiteOperatorTrace (((D.rpow (s - 1 / 2 : ℝ) * D.rpow (1 / 2 : ℝ)) * star A * D.rpow (1 - s)) * B) := by
          rw [← D.rpow_add (s - 1 / 2 : ℝ) (1 / 2 : ℝ), hexp2]
    _ = finiteOperatorTrace (D.rpow (s - 1 / 2 : ℝ) * (D.rpow (1 / 2 : ℝ) * star A * D.rpow (1 - s) * B)) := by
          simp only [mul_assoc]
    _ = finiteOperatorTrace ((D.rpow (1 / 2 : ℝ) * star A * D.rpow (1 - s) * B) * D.rpow (s - 1 / 2 : ℝ)) :=
          finiteOperatorTrace_mul_comm _ _

/-- Integrated GNS Kubo–Mori modular representation:
`⟨A, B⟩_BKM = ∫₀¹ ⟨A ξ_D, Δ_D^s (B ξ_D)⟩_HS ds`. -/
theorem kuboMoriPairing_eq_integral_hsInner_modularOp
    (D : FaithfulDensityOperator n) (A B : FiniteOperatorAlgebra n) :
    D.kuboMoriPairing A B =
      ∫ s in (0 : ℝ)..1,
        hsInner (A * naturalConeVector D) (modularOp D s (B * naturalConeVector D)) := by
  unfold FaithfulDensityOperator.kuboMoriPairing
  simp_rw [kuboMoriIntegrand_eq_hsInner_modularOp D A B]
  simpa only [sub_zero, sub_self] using
    intervalIntegral.integral_comp_sub_left
      (fun s : ℝ =>
        hsInner (A * naturalConeVector D) (modularOp D s (B * naturalConeVector D)))
      (1 : ℝ) (a := (0 : ℝ)) (b := (1 : ℝ))

/-- **Exact algebraic KMS boundary relation** for the modular operator `Δ_D^1`:
`Tr(ρ A Δ_D^1(B)) = Tr(ρ B A)`. -/
theorem gibbsState_mul_modularOp_one
    (D : FaithfulDensityOperator n) (A B : FiniteOperatorAlgebra n) :
    finiteOperatorTrace (D.rho * (A * modularOp D 1 B)) =
      finiteOperatorTrace (D.rho * (B * A)) := by
  unfold modularOp relativeModularOp
  simp only [LinearMap.coe_mk, AddHom.coe_mk, D.rpow_one]
  calc
    finiteOperatorTrace (D.rho * (A * (D.rho * B * D.rpow (-1))))
        = finiteOperatorTrace ((D.rho * A * D.rho * B) * D.rpow (-1)) := by
            simp only [mul_assoc]
    _ = finiteOperatorTrace (D.rpow (-1) * (D.rho * A * D.rho * B)) :=
            finiteOperatorTrace_mul_comm _ _
    _ = finiteOperatorTrace ((D.rpow (-1) * D.rpow 1) * (A * D.rho * B)) := by
            rw [D.rpow_one]
            simp only [mul_assoc]
    _ = finiteOperatorTrace (A * (D.rho * B)) := by
            rw [← D.rpow_add (-1) 1]
            have h0 : (-1 : ℝ) + 1 = 0 := by norm_num
            rw [h0, D.rpow_zero, one_mul, mul_assoc]
    _ = finiteOperatorTrace ((D.rho * B) * A) := finiteOperatorTrace_mul_comm _ _
    _ = finiteOperatorTrace (D.rho * (B * A)) := by rw [mul_assoc]

end BKMTomitaIntertwiner

/-! ## Section 4: `HSRealSelfAdjoint n` & Typed Soldering Equivalence to `DoubledSpace` -/

section DoubledKreinSoldering

/-- Real self-adjoint Hilbert–Schmidt carrier extracted from `FiniteOperatorAlgebra n`. -/
structure HSRealSelfAdjoint (n : ℕ) where
  op : FiniteOperatorAlgebra n
  isSelfAdjoint : IsSelfAdjoint op

namespace HSRealSelfAdjoint

@[ext] theorem ext {n : ℕ} {A B : HSRealSelfAdjoint n} (h : A.op = B.op) : A = B := by
  cases A; cases B; simp only [mk.injEq]; exact h

/-- Constructive zero witness in `HSRealSelfAdjoint n`. -/
def zero (n : ℕ) : HSRealSelfAdjoint n where
  op := 0
  isSelfAdjoint := by
    change star (0 : FiniteOperatorAlgebra n) = 0
    exact star_zero (FiniteOperatorAlgebra n)

/-- Constructive identity witness in `HSRealSelfAdjoint n`. -/
def one (n : ℕ) : HSRealSelfAdjoint n where
  op := 1
  isSelfAdjoint := by
    change star (1 : FiniteOperatorAlgebra n) = 1
    exact star_one (FiniteOperatorAlgebra n)

instance {n : ℕ} : Zero (HSRealSelfAdjoint n) :=
  ⟨zero n⟩

instance {n : ℕ} : Inhabited (HSRealSelfAdjoint n) :=
  ⟨zero n⟩

instance {n : ℕ} : Add (HSRealSelfAdjoint n) :=
  ⟨fun A B => ⟨A.op + B.op, by
    change star (A.op + B.op) = A.op + B.op
    rw [star_add A.op B.op, A.isSelfAdjoint.star_eq, B.isSelfAdjoint.star_eq]⟩⟩

instance {n : ℕ} : Neg (HSRealSelfAdjoint n) :=
  ⟨fun A => ⟨-A.op, by
    change star (-A.op) = -A.op
    rw [star_neg A.op, A.isSelfAdjoint.star_eq]⟩⟩

instance {n : ℕ} : Sub (HSRealSelfAdjoint n) :=
  ⟨fun A B => ⟨A.op - B.op, by
    change star (A.op - B.op) = A.op - B.op
    rw [star_sub A.op B.op, A.isSelfAdjoint.star_eq, B.isSelfAdjoint.star_eq]⟩⟩

instance {n : ℕ} : SMul ℝ (HSRealSelfAdjoint n) :=
  ⟨fun r A => ⟨(r : ℂ) • A.op, by
    change star ((r : ℂ) • A.op) = (r : ℂ) • A.op
    rw [star_smul (r : ℂ) A.op, Complex.star_def, Complex.conj_ofReal, A.isSelfAdjoint.star_eq]⟩⟩

@[simp] theorem add_op {n : ℕ} (A B : HSRealSelfAdjoint n) : (A + B).op = A.op + B.op := rfl
@[simp] theorem sub_op {n : ℕ} (A B : HSRealSelfAdjoint n) : (A - B).op = A.op - B.op := rfl
@[simp] theorem neg_op {n : ℕ} (A : HSRealSelfAdjoint n) : (-A).op = -A.op := rfl
@[simp] theorem zero_op {n : ℕ} : (0 : HSRealSelfAdjoint n).op = 0 := rfl
@[simp] theorem smul_op {n : ℕ} (r : ℝ) (A : HSRealSelfAdjoint n) : (r • A).op = (r : ℂ) • A.op := rfl

instance {n : ℕ} : AddCommGroup (HSRealSelfAdjoint n) where
  zero_add A := by ext1; exact zero_add A.op
  add_zero A := by ext1; exact add_zero A.op
  add_assoc A B C := by ext1; exact add_assoc A.op B.op C.op
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel A := by ext1; exact neg_add_cancel A.op
  add_comm A B := by ext1; exact add_comm A.op B.op
  sub_eq_add_neg A B := by ext1; exact sub_eq_add_neg A.op B.op

instance {n : ℕ} : Module ℝ (HSRealSelfAdjoint n) where
  one_smul A := by ext1; exact one_smul ℂ A.op
  mul_smul r s A := by
    ext1
    simp only [smul_op]
    push_cast
    exact mul_smul (r : ℂ) (s : ℂ) A.op
  smul_zero r := by ext1; exact smul_zero (A := FiniteOperatorAlgebra n) (r : ℂ)
  smul_add r A B := by ext1; exact smul_add (r : ℂ) A.op B.op
  add_smul r s A := by
    ext1
    simp only [smul_op, add_op]
    push_cast
    exact add_smul (r : ℂ) (s : ℂ) A.op
  zero_smul A := by ext1; exact zero_smul ℂ A.op

private theorem trace_mul_real_symm {n : ℕ} (A B : HSRealSelfAdjoint n) :
    (finiteOperatorTrace (A.op * B.op)).re = (finiteOperatorTrace (B.op * A.op)).re ∧
    (finiteOperatorTrace (A.op * B.op)).im = 0 := by
  have hcomm : finiteOperatorTrace (A.op * B.op) = finiteOperatorTrace (B.op * A.op) :=
    finiteOperatorTrace_mul_comm A.op B.op
  have hstar :
      star (finiteOperatorTrace (A.op * B.op)) = finiteOperatorTrace (B.op * A.op) := by
    rw [← finiteOperatorTrace_star, star_mul, A.isSelfAdjoint.star_eq, B.isSelfAdjoint.star_eq]
  have hconj : star (finiteOperatorTrace (A.op * B.op)) = finiteOperatorTrace (A.op * B.op) :=
    hstar.trans hcomm.symm
  have him : (finiteOperatorTrace (A.op * B.op)).im = 0 := by
    have := congrArg Complex.im hconj
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  exact ⟨congrArg Complex.re hcomm, him⟩

/-- Real Hilbert–Schmidt inner-product core on `HSRealSelfAdjoint n`. -/
noncomputable instance instCore {n : ℕ} :
    InnerProductSpace.Core ℝ (HSRealSelfAdjoint n) where
  inner A B := (finiteOperatorTrace (A.op * B.op)).re
  conj_inner_symm A B := (trace_mul_real_symm B A).1
  re_inner_nonneg A := by
    have h := finiteOperatorTrace_star_mul_self_re_nonneg A.op
    rwa [A.isSelfAdjoint.star_eq] at h
  add_left A B C := by
    change (finiteOperatorTrace ((A.op + B.op) * C.op)).re =
      (finiteOperatorTrace (A.op * C.op)).re + (finiteOperatorTrace (B.op * C.op)).re
    rw [add_mul]
    change ((finiteOperatorTraceLinear n) (A.op * C.op + B.op * C.op)).re = _
    rw [map_add, Complex.add_re]
    rfl
  smul_left A B r := by
    change (finiteOperatorTrace (((r : ℂ) • A.op) * B.op)).re =
      r * (finiteOperatorTrace (A.op * B.op)).re
    rw [smul_mul_assoc]
    change ((finiteOperatorTraceLinear n) ((r : ℂ) • (A.op * B.op))).re = _
    rw [map_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rfl
  definite A h := by
    ext1
    change (finiteOperatorTrace (A.op * A.op)).re = 0 at h
    nth_rw 1 [← A.isSelfAdjoint.star_eq] at h
    exact (finiteOperatorTrace_star_mul_self_re_eq_zero_iff A.op).mp h

noncomputable instance instNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup (HSRealSelfAdjoint n) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

noncomputable instance instInnerProductSpace {n : ℕ} :
    InnerProductSpace ℝ (HSRealSelfAdjoint n) :=
  InnerProductSpace.ofCore (instCore (n := n)).toCore

@[simp] theorem inner_eq {n : ℕ} (A B : HSRealSelfAdjoint n) :
    inner ℝ A B = (finiteOperatorTrace (A.op * B.op)).re :=
  rfl

private def toMatrixFunLinear (n : ℕ) :
    HSRealSelfAdjoint n →ₗ[ℝ] (Fin n × Fin n → ℂ) where
  toFun A p := matrixOfOp A.op p.1 p.2
  map_add' A B := by
    ext p
    simp [matrixOfOp_add]
  map_smul' r A := by
    ext p
    have hsm := matrixOfOp_complex_smul (r : ℂ) A.op
    simp [hsm]

private theorem toMatrixFunLinear_injective (n : ℕ) :
    Function.Injective (toMatrixFunLinear n) := by
  intro A B h
  ext1
  apply matrixOfOp_injective
  ext i j
  exact congrArg (fun f => f (i, j)) h

instance instFiniteDimensional {n : ℕ} :
    FiniteDimensional ℝ (HSRealSelfAdjoint n) :=
  Module.Finite.of_injective (toMatrixFunLinear n) (toMatrixFunLinear_injective n)

noncomputable instance instCompleteSpace {n : ℕ} :
    CompleteSpace (HSRealSelfAdjoint n) :=
  FiniteDimensional.complete ℝ (HSRealSelfAdjoint n)

end HSRealSelfAdjoint

/-- Hermitian real part `(X + X*) / 2` in `HSRealSelfAdjoint n`. -/
def hermRe {n : ℕ} (X : FiniteOperatorAlgebra n) : HSRealSelfAdjoint n where
  op := (1 / 2 : ℂ) • (X + star X)
  isSelfAdjoint := by
    change star ((1 / 2 : ℂ) • (X + star X)) = (1 / 2 : ℂ) • (X + star X)
    rw [star_smul (1 / 2 : ℂ) (X + star X), star_add X (star X), star_star]
    have hhalf : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
    rw [hhalf, add_comm]

/-- Hermitian imaginary part `-i (X - X*) / 2` in `HSRealSelfAdjoint n`,
so `X = (hermRe X).op + Complex.I • (hermIm X).op`. -/
def hermIm {n : ℕ} (X : FiniteOperatorAlgebra n) : HSRealSelfAdjoint n where
  op := (-(Complex.I / 2)) • (X - star X)
  isSelfAdjoint := by
    change star ((-(Complex.I / 2)) • (X - star X)) = (-(Complex.I / 2)) • (X - star X)
    rw [star_smul (-(Complex.I / 2)) (X - star X), star_sub X (star X), star_star]
    have hcoeff : star (-(Complex.I / 2)) = Complex.I / 2 := by
      rw [Complex.star_def, map_neg, map_div₀, Complex.conj_I, map_ofNat]
      ring
    rw [hcoeff, neg_smul (Complex.I / 2) (X - star X), ← smul_neg (Complex.I / 2) (X - star X),
      neg_sub]

@[simp] theorem hermRe_add {n : ℕ} (X Y : FiniteOperatorAlgebra n) :
    hermRe (X + Y) = hermRe X + hermRe Y := by
  ext1
  simp only [hermRe, HSRealSelfAdjoint.add_op]
  rw [star_add X Y, ← smul_add (1 / 2 : ℂ) (X + star X) (Y + star Y)]
  congr 1
  abel

@[simp] theorem hermIm_add {n : ℕ} (X Y : FiniteOperatorAlgebra n) :
    hermIm (X + Y) = hermIm X + hermIm Y := by
  ext1
  simp only [hermIm, HSRealSelfAdjoint.add_op]
  rw [star_add X Y, ← smul_add (-(Complex.I / 2)) (X - star X) (Y - star Y)]
  congr 1
  abel

@[simp] theorem hermRe_real_smul {n : ℕ} (r : ℝ) (X : FiniteOperatorAlgebra n) :
    hermRe (r • X) = r • hermRe X := by
  ext1
  simp only [hermRe, HSRealSelfAdjoint.smul_op]
  change (1 / 2 : ℂ) • ((r : ℂ) • X + star ((r : ℂ) • X)) =
    (r : ℂ) • ((1 / 2 : ℂ) • (X + star X))
  rw [star_smul (r : ℂ) X, Complex.star_def, Complex.conj_ofReal, ← smul_add (r : ℂ) X (star X),
    smul_comm]

@[simp] theorem hermIm_real_smul {n : ℕ} (r : ℝ) (X : FiniteOperatorAlgebra n) :
    hermIm (r • X) = r • hermIm X := by
  ext1
  simp only [hermIm, HSRealSelfAdjoint.smul_op]
  change (-(Complex.I / 2)) • ((r : ℂ) • X - star ((r : ℂ) • X)) =
    (r : ℂ) • ((-(Complex.I / 2)) • (X - star X))
  rw [star_smul (r : ℂ) X, Complex.star_def, Complex.conj_ofReal, ← smul_sub (r : ℂ) X (star X),
    smul_comm]

theorem hermRe_add_I_smul_hermIm {n : ℕ} (X : FiniteOperatorAlgebra n) :
    (hermRe X).op + Complex.I • (hermIm X).op = X := by
  dsimp [hermRe, hermIm]
  rw [smul_smul]
  have hi : Complex.I * -(Complex.I / 2) = (1 / 2 : ℂ) := by
    calc
      Complex.I * -(Complex.I / 2) = -((Complex.I * Complex.I) / 2) := by ring
      _ = -((-1 : ℂ) / 2) := by rw [Complex.I_mul_I]
      _ = (1 / 2 : ℂ) := by ring
  rw [hi, smul_add (1 / 2 : ℂ) X (star X), smul_sub (1 / 2 : ℂ) X (star X), ← add_sub_assoc]
  have hadd :
      (1 / 2 : ℂ) • X + (1 / 2 : ℂ) • star X + (1 / 2 : ℂ) • X =
        X + (1 / 2 : ℂ) • star X := by
    rw [add_right_comm, ← add_smul (1 / 2 : ℂ) (1 / 2 : ℂ) X]
    have h1 : (1 / 2 : ℂ) + (1 / 2 : ℂ) = 1 := by norm_num
    rw [h1, one_smul]
  rw [hadd, add_sub_cancel_right]

@[simp] theorem hermRe_of_isSelfAdjoint {n : ℕ} (A : HSRealSelfAdjoint n) :
    hermRe A.op = A := by
  ext1
  dsimp [hermRe]
  rw [A.isSelfAdjoint.star_eq, smul_add (1 / 2 : ℂ) A.op A.op,
    ← add_smul (1 / 2 : ℂ) (1 / 2 : ℂ) A.op]
  have h1 : (1 / 2 : ℂ) + (1 / 2 : ℂ) = 1 := by norm_num
  rw [h1, one_smul]

@[simp] theorem hermIm_of_isSelfAdjoint {n : ℕ} (A : HSRealSelfAdjoint n) :
    hermIm A.op = 0 := by
  ext1
  simp only [hermIm, HSRealSelfAdjoint.zero_op, A.isSelfAdjoint.star_eq, sub_self, smul_zero]

@[simp] theorem hermRe_I_mul_selfAdjoint {n : ℕ} (B : HSRealSelfAdjoint n) :
    hermRe (Complex.I • B.op) = 0 := by
  ext1
  simp only [hermRe, HSRealSelfAdjoint.zero_op]
  rw [star_smul Complex.I B.op, Complex.star_def, Complex.conj_I, B.isSelfAdjoint.star_eq,
    neg_smul Complex.I B.op, add_neg_cancel, smul_zero]

@[simp] theorem hermIm_I_mul_selfAdjoint {n : ℕ} (B : HSRealSelfAdjoint n) :
    hermIm (Complex.I • B.op) = B := by
  ext1
  dsimp [hermIm]
  rw [star_smul Complex.I B.op, Complex.star_def, Complex.conj_I, B.isSelfAdjoint.star_eq,
    neg_smul Complex.I B.op, sub_neg_eq_add, ← add_smul Complex.I Complex.I B.op, smul_smul]
  have hc : -(Complex.I / 2) * (Complex.I + Complex.I) = 1 := by
    calc
      -(Complex.I / 2) * (Complex.I + Complex.I) = -(Complex.I * Complex.I) := by ring
      _ = -(-1 : ℂ) := by rw [Complex.I_mul_I]
      _ = 1 := by norm_num
  rw [hc, one_smul]

@[simp] theorem hermRe_tomitaJ {n : ℕ} (X : FiniteOperatorAlgebra n) :
    hermRe (tomitaJ X) = hermRe X := by
  ext1
  simp only [hermRe, tomitaJ, star_star, add_comm]

@[simp] theorem hermIm_tomitaJ {n : ℕ} (X : FiniteOperatorAlgebra n) :
    hermIm (tomitaJ X) = -hermIm X := by
  ext1
  simp only [hermIm, tomitaJ, HSRealSelfAdjoint.neg_op, star_star]
  rw [← smul_neg (-(Complex.I / 2)) (X - star X), neg_sub]

@[simp] theorem hermRe_I_mul_star {n : ℕ} (X : FiniteOperatorAlgebra n) :
    hermRe (Complex.I • star X) = hermIm X := by
  ext1
  dsimp [hermRe, hermIm]
  rw [star_smul Complex.I (star X), Complex.star_def, Complex.conj_I, star_star,
    smul_add (1 / 2 : ℂ), smul_sub (-(Complex.I / 2)), smul_smul, smul_smul]
  have ha : (1 / 2 : ℂ) * Complex.I = Complex.I / 2 := by ring
  have hb : (1 / 2 : ℂ) * (-Complex.I) = -(Complex.I / 2) := by ring
  rw [ha, hb, sub_eq_add_neg, ← neg_smul (-(Complex.I / 2)) (star X), neg_neg, add_comm]

@[simp] theorem hermIm_I_mul_star {n : ℕ} (X : FiniteOperatorAlgebra n) :
    hermIm (Complex.I • star X) = hermRe X := by
  ext1
  dsimp [hermIm, hermRe]
  rw [star_smul Complex.I (star X), Complex.star_def, Complex.conj_I, star_star,
    neg_smul Complex.I X, sub_neg_eq_add, smul_add (-(Complex.I / 2)), smul_smul, smul_smul]
  have hi : -(Complex.I / 2) * Complex.I = (1 / 2 : ℂ) := by
    calc
      -(Complex.I / 2) * Complex.I = -((Complex.I * Complex.I) / 2) := by ring
      _ = -((-1 : ℂ) / 2) := by rw [Complex.I_mul_I]
      _ = (1 / 2 : ℂ) := by ring
  rw [hi, ← smul_add (1 / 2 : ℂ) (star X) X, add_comm]

theorem neg_I_smul_eq_tomitaJ_I_mul_star {n : ℕ} (X : FiniteOperatorAlgebra n) :
    -(Complex.I • X) = tomitaJ (Complex.I • star X) := by
  unfold tomitaJ
  rw [star_smul Complex.I (star X), Complex.star_def, Complex.conj_I, star_star,
    neg_smul Complex.I X]

@[simp] theorem hermRe_neg_I_smul {n : ℕ} (X : FiniteOperatorAlgebra n) :
    hermRe (-(Complex.I • X)) = hermIm X := by
  rw [neg_I_smul_eq_tomitaJ_I_mul_star, hermRe_tomitaJ, hermRe_I_mul_star]

@[simp] theorem hermIm_neg_I_smul {n : ℕ} (X : FiniteOperatorAlgebra n) :
    hermIm (-(Complex.I • X)) = -hermRe X := by
  rw [neg_I_smul_eq_tomitaJ_I_mul_star, hermIm_tomitaJ, hermIm_I_mul_star]

/-- **Canonical Tomita–Krein `ℝ`-linear soldering equivalence**:
identifies `FiniteOperatorAlgebra n` with `DoubledSpace (HSRealSelfAdjoint n)`
via `X ↦ to_doubled (Re(X) + Im(X)) (Re(X) - Im(X))`. -/
noncomputable def operatorToDoubledKrein (n : ℕ) :
    FiniteOperatorAlgebra n ≃ₗ[ℝ] DoubledSpace (HSRealSelfAdjoint n) where
  toFun X := to_doubled (hermRe X + hermIm X) (hermRe X - hermIm X)
  map_add' X Y := by
    apply DoubledSpace.ext
    · simp; abel
    · simp; abel
  map_smul' r X := by
    apply DoubledSpace.ext
    · simp [WithLp.smul_fst, smul_add]
    · simp [WithLp.smul_snd, smul_sub]
  invFun u :=
    (1 / 2 : ℂ) • ((WithLp.fst u).op + (WithLp.snd u).op) +
      (Complex.I / 2) • ((WithLp.fst u).op - (WithLp.snd u).op)
  left_inv X := by
    change (1 / 2 : ℂ) • ((hermRe X + hermIm X).op + (hermRe X - hermIm X).op) +
        (Complex.I / 2) • ((hermRe X + hermIm X).op - (hermRe X - hermIm X).op) = X
    have h1 : (hermRe X + hermIm X).op + (hermRe X - hermIm X).op =
        (2 : ℂ) • (hermRe X).op := by
      rw [two_smul ℂ (hermRe X).op]
      simp only [HSRealSelfAdjoint.add_op, HSRealSelfAdjoint.sub_op]
      abel
    have h2 : (hermRe X + hermIm X).op - (hermRe X - hermIm X).op =
        (2 : ℂ) • (hermIm X).op := by
      rw [two_smul ℂ (hermIm X).op]
      simp only [HSRealSelfAdjoint.add_op, HSRealSelfAdjoint.sub_op]
      abel
    rw [h1, h2, smul_smul, smul_smul]
    have ha : (1 / 2 : ℂ) * 2 = 1 := by norm_num
    have hb : (Complex.I / 2) * 2 = Complex.I := by ring
    rw [ha, hb, one_smul]
    exact hermRe_add_I_smul_hermIm X
  right_inv u := by
    let x := WithLp.fst u
    let ξ := WithLp.snd u
    let X : FiniteOperatorAlgebra n :=
      (1 / 2 : ℂ) • (x.op + ξ.op) + (Complex.I / 2) • (x.op - ξ.op)
    have hX : X = ((1 / 2 : ℝ) • (x + ξ)).op + Complex.I • ((1 / 2 : ℝ) • (x - ξ)).op := by
      simp [X, smul_smul]; ring_nf
    have hre : hermRe X = (1 / 2 : ℝ) • (x + ξ) := by
      rw [hX, hermRe_add, hermRe_of_isSelfAdjoint, hermRe_I_mul_selfAdjoint, add_zero]
    have him : hermIm X = (1 / 2 : ℝ) • (x - ξ) := by
      rw [hX, hermIm_add, hermIm_of_isSelfAdjoint, hermIm_I_mul_selfAdjoint, zero_add]
    apply DoubledSpace.ext
    · change hermRe X + hermIm X = x
      rw [hre, him, ← smul_add]
      have hx : (x + ξ) + (x - ξ) = (2 : ℝ) • x := by rw [two_smul]; abel
      rw [hx, smul_smul]
      norm_num
    · change hermRe X - hermIm X = ξ
      rw [hre, him, ← smul_sub]
      have hξ : (x + ξ) - (x - ξ) = (2 : ℝ) • ξ := by rw [two_smul]; abel
      rw [hξ, smul_smul]
      norm_num

/-- **Soldering Theorem I (`tomitaJ ↔ modular_j`)**:
Tomita's modular conjugation is the exact image of Krein's sheet swap `modular_j`. -/
theorem operatorToDoubledKrein_tomitaJ {n : ℕ} (X : FiniteOperatorAlgebra n) :
    operatorToDoubledKrein n (tomitaJ X) = modular_j (operatorToDoubledKrein n X) := by
  apply DoubledSpace.ext
  · change hermRe (tomitaJ X) + hermIm (tomitaJ X) = hermRe X - hermIm X
    rw [hermRe_tomitaJ, hermIm_tomitaJ, sub_eq_add_neg]
  · change hermRe (tomitaJ X) - hermIm (tomitaJ X) = hermRe X + hermIm X
    rw [hermRe_tomitaJ, hermIm_tomitaJ, sub_neg_eq_add]

/-- **Soldering Theorem II (`X ↦ i X* ↔ spectral_epsilon`)**:
the chiral anti-involution intertwines Krein's fundamental symmetry `spectral_epsilon`. -/
theorem operatorToDoubledKrein_chiralInvolution {n : ℕ} (X : FiniteOperatorAlgebra n) :
    operatorToDoubledKrein n (Complex.I • star X) =
      spectral_epsilon (operatorToDoubledKrein n X) := by
  apply DoubledSpace.ext
  · change hermRe (Complex.I • star X) + hermIm (Complex.I • star X) = hermRe X + hermIm X
    rw [hermRe_I_mul_star, hermIm_I_mul_star, add_comm]
  · change hermRe (Complex.I • star X) - hermIm (Complex.I • star X) = -(hermRe X - hermIm X)
    rw [hermRe_I_mul_star, hermIm_I_mul_star, neg_sub]

/-- **Soldering Theorem III (`X ↦ -i X ↔ complex_i`)**:
multiplication by `-i` intertwines `complex_i = modular_j ∘ spectral_epsilon`. -/
theorem operatorToDoubledKrein_neg_I_smul {n : ℕ} (X : FiniteOperatorAlgebra n) :
    operatorToDoubledKrein n (-(Complex.I • X)) =
      complex_i (operatorToDoubledKrein n X) := by
  rw [neg_I_smul_eq_tomitaJ_I_mul_star, operatorToDoubledKrein_tomitaJ,
    operatorToDoubledKrein_chiralInvolution]
  rfl

/-- **Soldering Theorem IV (Exact Hilbert–Schmidt Metric Identity)**:
`⟪Φ X, Φ Y⟫_ℝ = 2 * Re ⟨X, Y⟩_HS`. -/
theorem inner_operatorToDoubledKrein {n : ℕ} (X Y : FiniteOperatorAlgebra n) :
    inner ℝ (operatorToDoubledKrein n X) (operatorToDoubledKrein n Y) =
      2 * (hsInner X Y).re := by
  rw [show inner ℝ (operatorToDoubledKrein n X) (operatorToDoubledKrein n Y) =
      doubledHilbertBilin (operatorToDoubledKrein n X) (operatorToDoubledKrein n Y) from rfl]
  dsimp [operatorToDoubledKrein]
  rw [doubledHilbertBilin_to_doubled]
  rw [show inner ℝ (hermRe X + hermIm X) (hermRe Y + hermIm Y) +
        inner ℝ (hermRe X - hermIm X) (hermRe Y - hermIm Y) =
      2 * (inner ℝ (hermRe X) (hermRe Y) + inner ℝ (hermIm X) (hermIm Y)) by
    rw [inner_add_left, inner_add_right, inner_add_right,
      inner_sub_left, inner_sub_right, inner_sub_right]
    ring]
  congr 1
  have hX : X = (hermRe X).op + Complex.I • (hermIm X).op := (hermRe_add_I_smul_hermIm X).symm
  have hY : Y = (hermRe Y).op + Complex.I • (hermIm Y).op := (hermRe_add_I_smul_hermIm Y).symm
  have hre :
      (hsInner X Y).re =
        (finiteOperatorTrace ((hermRe X).op * (hermRe Y).op)).re +
          (finiteOperatorTrace ((hermIm X).op * (hermIm Y).op)).re := by
    unfold hsInner
    have hstarX : star X = (hermRe X).op - Complex.I • (hermIm X).op := by
      conv_lhs => rw [hX]
      rw [star_add (hermRe X).op (Complex.I • (hermIm X).op),
        star_smul Complex.I (hermIm X).op, Complex.star_def, Complex.conj_I,
        (hermRe X).isSelfAdjoint.star_eq, (hermIm X).isSelfAdjoint.star_eq,
        neg_smul Complex.I (hermIm X).op, sub_eq_add_neg]
    have hprod :
        star X * Y =
          ((hermRe X).op * (hermRe Y).op + Complex.I • ((hermRe X).op * (hermIm Y).op)) +
            ((-Complex.I) • ((hermIm X).op * (hermRe Y).op) +
              (hermIm X).op * (hermIm Y).op) := by
      conv_lhs => rw [hstarX, hY]
      rw [sub_mul, mul_add, mul_add,
        mul_smul_comm Complex.I (hermRe X).op (hermIm Y).op,
        smul_mul_assoc Complex.I (hermIm X).op (hermRe Y).op,
        smul_mul_assoc Complex.I (hermIm X).op (Complex.I • (hermIm Y).op),
        mul_smul_comm Complex.I (hermIm X).op (hermIm Y).op,
        smul_smul Complex.I Complex.I ((hermIm X).op * (hermIm Y).op),
        Complex.I_mul_I, neg_one_smul ℂ ((hermIm X).op * (hermIm Y).op),
        neg_smul Complex.I ((hermIm X).op * (hermRe Y).op)]
      abel
    rw [hprod]
    change ((finiteOperatorTraceLinear n)
        (((hermRe X).op * (hermRe Y).op + Complex.I • ((hermRe X).op * (hermIm Y).op)) +
          ((-Complex.I) • ((hermIm X).op * (hermRe Y).op) +
            (hermIm X).op * (hermIm Y).op))).re = _
    rw [map_add, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have him1 := (HSRealSelfAdjoint.trace_mul_real_symm (hermRe X) (hermIm Y)).2
    have him2 := (HSRealSelfAdjoint.trace_mul_real_symm (hermIm X) (hermRe Y)).2
    change (((finiteOperatorTrace ((hermRe X).op * (hermRe Y).op) +
        Complex.I * finiteOperatorTrace ((hermRe X).op * (hermIm Y).op)) +
        (-Complex.I * finiteOperatorTrace ((hermIm X).op * (hermRe Y).op) +
          finiteOperatorTrace ((hermIm X).op * (hermIm Y).op)))).re = _
    simp [him1, him2]
  rw [hre]
  rfl

/-- Modular operator transported onto `DoubledSpace (HSRealSelfAdjoint n)`. -/
def doubledKreinModularOp
    {n : ℕ} (D : FaithfulDensityOperator n) (s : ℝ) :
    DoubledSpace (HSRealSelfAdjoint n) →ₗ[ℝ] DoubledSpace (HSRealSelfAdjoint n) :=
  (operatorToDoubledKrein n).toLinearMap.comp
    (((modularOp D s).restrictScalars ℝ).comp (operatorToDoubledKrein n).symm.toLinearMap)

/-- Operator-valued Kubo–Mori transform transported onto `DoubledSpace (HSRealSelfAdjoint n)`. -/
def doubledKreinKuboMoriTransform
    {n : ℕ} (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow) :
    DoubledSpace (HSRealSelfAdjoint n) →ₗ[ℝ] DoubledSpace (HSRealSelfAdjoint n) :=
  (operatorToDoubledKrein n).toLinearMap.comp
    (((D.kuboMoriTransformCLM hpow).toLinearMap.restrictScalars ℝ).comp
      (operatorToDoubledKrein n).symm.toLinearMap)

/-- **Krein–Tomita Modular Swap Intertwining on `DoubledSpace`**:
`modular_j (doubledKreinModularOp D s u) = doubledKreinModularOp D (-s) (modular_j u)`. -/
theorem modular_j_doubledKreinModularOp
    {n : ℕ} (D : FaithfulDensityOperator n) (s : ℝ) (u : DoubledSpace (HSRealSelfAdjoint n)) :
    modular_j (doubledKreinModularOp D s u) =
      doubledKreinModularOp D (-s) (modular_j u) := by
  change modular_j (operatorToDoubledKrein n (modularOp D s ((operatorToDoubledKrein n).symm u))) =
    operatorToDoubledKrein n (modularOp D (-s) ((operatorToDoubledKrein n).symm (modular_j u)))
  rw [← operatorToDoubledKrein_tomitaJ]
  have hinj :
      tomitaJ (modularOp D s ((operatorToDoubledKrein n).symm u)) =
        modularOp D (-s) ((operatorToDoubledKrein n).symm (modular_j u)) := by
    have hm :
        modular_j u =
          operatorToDoubledKrein n (tomitaJ ((operatorToDoubledKrein n).symm u)) := by
      rw [operatorToDoubledKrein_tomitaJ]
      simp
    rw [hm, (operatorToDoubledKrein n).symm_apply_apply]
    simpa only [modularOp, tomitaJ_involutive] using
      tomitaJ_relativeModularOp_tomitaJ D D s (tomitaJ ((operatorToDoubledKrein n).symm u))
  exact congrArg (operatorToDoubledKrein n) hinj

end DoubledKreinSoldering

end InfoGeometry.Canonical.TomitaArakiBKMKreinSoldering
