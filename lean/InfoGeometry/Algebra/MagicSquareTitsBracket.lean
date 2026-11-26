/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.NativeTitsE8Carrier
import InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear
import InfoGeometry.Lie.SplitOctonionStandardDerivationCovariance
import InfoGeometry.Lie.SplitDerivationCoordinates
import InfoGeometry.Algebra.H3ZornReducedStructureLieAlgebra
import InfoGeometry.Algebra.H3ZornMcCrimmonTraceIdentities
import InfoGeometry.Algebra.H3ZornAdjointProductIdentity
import InfoGeometry.Algebra.H3ZornE6RootSystem
import InfoGeometry.Algebra.H3ZornInfinitesimalReconstruction
import InfoGeometry.Exceptional.GenericGradedJacobiClosure

/-!
# Freudenthal–Tits Magic Square 248D Lie Algebra `SplitE8Lie` (`𝔈₈(8)`)

On the native carrier `SplitE8Lie ≃ₗ[ℝ] G₂(2) ⊕ (Im(𝕆_s) ⊗ H₃(𝕆_s)⁰) ⊕ F₄(4)`
(`14 + 7 × 26 + 52 = 248`), this module constructs the genuine non-vacuous
248-dimensional split `E₈` Lie algebra via the Freudenthal–Tits Magic Square
bracket with verified rational constants `(c₁, c₂, c₃) = (1/3, -2, 1)`:

`[a ⊗ x, b ⊗ y] = (1/3) * traceBilin x.1 y.1 • g2Inner a b`
`                + (-2) * zornBilin a.1 b.1 • f4Inner x y`
`                + (zornComm0 a b) ⊗ (h3Mul0 x y)`

All 27 graded Jacobi cells are closed coordinate-free via
`GenericGradedJacobiClosure.global_leibniz_of_homogeneous` using decoupled
7D split-octonion (alternative/Teichmüller/Kleinfeld) and 26D split-Albert
(cubic Cayley–Hamilton/McCrimmon/Jordan) identities.

The module also exports embeddings, projections, a concrete nonzero bracket
witness `exists_bracket_ne_zero`, and the 2D `G₂` Cartan, 4D `F₄` Cartan, and
traceless diagonal/off-diagonal evaluation helpers for `SplitE8RootSystem.lean`.
-/

noncomputable section

namespace InfoGeometry.Algebra.MagicSquareTitsBracket

open scoped TensorProduct BigOperators
open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear
open InfoGeometry.Canonical.NativeTitsE8Carrier
open InfoGeometry.Exceptional

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private abbrev G2VDer := InfoGeometry.Canonical.NativeTitsE8Carrier.G2DerivationCarrier
local notation "VZ" => InfoGeometry.Canonical.NativeTitsE8Carrier.VZ

/-! ## 1. Operations on `splitOctonionTraceZero` (`7D`) and `h3TraceZero` (`26D`) -/

section TracelessOperations

/-- Trace-zero projection of `ZornVectorMatrix.commutator` on `splitOctonionTraceZero`. -/
def zornComm0 (a b : splitOctonionTraceZero) : splitOctonionTraceZero :=
  ⟨a.1 * b.1 - b.1 * a.1, by
    change ZornVectorMatrix.trace (ZornVectorMatrix.commutator a.1 b.1) = 0
    exact ZornVectorMatrix.trace_commutator a.1 b.1⟩

@[simp] theorem zornComm0_coe (a b : splitOctonionTraceZero) :
    (zornComm0 a b : VZ) = a.1 * b.1 - b.1 * a.1 := rfl

/-- Bilinear `ℝ`-linear map version of `zornComm0`. -/
def zornComm0LM :
    splitOctonionTraceZero →ₗ[ℝ] splitOctonionTraceZero →ₗ[ℝ] splitOctonionTraceZero :=
  LinearMap.mk₂ ℝ zornComm0
    (fun a₁ a₂ b => by
      apply Subtype.ext
      change (a₁.1 + a₂.1) * b.1 - b.1 * (a₁.1 + a₂.1) =
        (a₁.1 * b.1 - b.1 * a₁.1) + (a₂.1 * b.1 - b.1 * a₂.1)
      simp only [add_mul, mul_add]
      abel)
    (fun r a b => by
      apply Subtype.ext
      change (r • a.1) * b.1 - b.1 * (r • a.1) = r • (a.1 * b.1 - b.1 * a.1)
      simp only [smul_mul_assoc, mul_smul_comm, smul_sub])
    (fun a b₁ b₂ => by
      apply Subtype.ext
      change a.1 * (b₁.1 + b₂.1) - (b₁.1 + b₂.1) * a.1 =
        (a.1 * b₁.1 - b₁.1 * a.1) + (a.1 * b₂.1 - b₂.1 * a.1)
      simp only [mul_add, add_mul]
      abel)
    (fun r a b => by
      apply Subtype.ext
      change a.1 * (r • b.1) - (r • b.1) * a.1 = r • (a.1 * b.1 - b.1 * a.1)
      simp only [mul_smul_comm, smul_mul_assoc, smul_sub])

@[simp] theorem zornComm0LM_apply (a b : splitOctonionTraceZero) :
    zornComm0LM a b = zornComm0 a b := rfl

theorem zornComm0_self (a : splitOctonionTraceZero) : zornComm0 a a = 0 := by
  apply Subtype.ext
  change a.1 * a.1 - a.1 * a.1 = 0
  exact sub_self _

theorem zornComm0_antisymm (a b : splitOctonionTraceZero) :
    zornComm0 b a = -zornComm0 a b := by
  apply Subtype.ext
  change b.1 * a.1 - a.1 * b.1 = -(a.1 * b.1 - b.1 * a.1)
  abel

/-- Action of `G2DerivationCarrier` (`VDer`) on `splitOctonionTraceZero`. -/
def g2Act (D : G2DerivationCarrier) (a : splitOctonionTraceZero) : splitOctonionTraceZero :=
  ⟨D a.1, InfoGeometry.Lie.SplitDerivationCoordinates.every_derivation_trace_zero D a.1⟩

@[simp] theorem g2Act_coe (D : G2DerivationCarrier) (a : splitOctonionTraceZero) :
    (g2Act D a : VZ) = D a.1 := rfl

/-- Bilinear `ℝ`-linear action of `G2DerivationCarrier` on `splitOctonionTraceZero`. -/
def g2ActLM :
    G2DerivationCarrier →ₗ[ℝ] splitOctonionTraceZero →ₗ[ℝ] splitOctonionTraceZero :=
  LinearMap.mk₂ ℝ g2Act
    (fun D₁ D₂ a => by apply Subtype.ext; rfl)
    (fun r D a => by apply Subtype.ext; rfl)
    (fun D a₁ a₂ => by apply Subtype.ext; exact D.map_add a₁.1 a₂.1)
    (fun r D a => by apply Subtype.ext; exact D.map_smul r a.1)

@[simp] theorem g2ActLM_apply (D : G2DerivationCarrier) (a : splitOctonionTraceZero) :
    g2ActLM D a = g2Act D a := rfl

/-- Inner derivation `D_{a, b}` in `G2DerivationCarrier`. -/
def g2Inner (a b : splitOctonionTraceZero) : G2DerivationCarrier :=
  innerDerivation a.1 b.1

/-- Bilinear `ℝ`-linear inner derivation map into `G2DerivationCarrier`. -/
def g2InnerLM :
    splitOctonionTraceZero →ₗ[ℝ] splitOctonionTraceZero →ₗ[ℝ] G2DerivationCarrier :=
  LinearMap.mk₂ ℝ g2Inner
    (fun a₁ a₂ b => innerDerivation_add_left a₁.1 a₂.1 b.1)
    (fun r a b => innerDerivation_smul_left r a.1 b.1)
    (fun a b₁ b₂ => innerDerivation_add_right a.1 b₁.1 b₂.1)
    (fun r a b => by
      change innerDerivation a.1 (r • b.1) = r • innerDerivation a.1 b.1
      exact (innerDerivation a.1).map_smul r b.1)

@[simp] theorem g2InnerLM_apply (a b : splitOctonionTraceZero) :
    g2InnerLM a b = g2Inner a b := rfl

theorem g2Inner_self (a : splitOctonionTraceZero) : g2Inner a a = 0 := by
  have h := innerDerivation_swap a.1 a.1
  have h2 : (2 : ℝ) • g2Inner a a = 0 := by
    rw [two_smul]
    change innerDerivation a.1 a.1 + innerDerivation a.1 a.1 = 0
    nth_rw 2 [h]
    exact add_neg_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

theorem g2Inner_antisymm (a b : splitOctonionTraceZero) :
    g2Inner b a = -g2Inner a b :=
  innerDerivation_swap a.1 b.1

/-- Bilinear pairing `zornBilin` restricted to `splitOctonionTraceZero`. -/
def zornBilin0LM :
    splitOctonionTraceZero →ₗ[ℝ] splitOctonionTraceZero →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun a b => zornBilin a.1 b.1)
    (fun a₁ a₂ b => zornBilin_add_left a₁.1 a₂.1 b.1)
    (fun r a b => zornBilin_smul_left r a.1 b.1)
    (fun a b₁ b₂ => zornBilin_add_right a.1 b₁.1 b₂.1)
    (fun r a b => zornBilin_smul_right r a.1 b.1)

@[simp] theorem zornBilin0LM_apply (a b : splitOctonionTraceZero) :
    zornBilin0LM a b = zornBilin a.1 b.1 := rfl

/-- Trace-zero projection `H3Zorn ℝ →ₗ[ℝ] h3TraceZero`. -/
def h3Proj0 : H3Zorn ℝ →ₗ[ℝ] h3TraceZero where
  toFun X := ⟨X - ((1 / 3 : ℝ) * linearTrace X) • (1 : H3Zorn ℝ), by
    change linearTrace (X - ((1 / 3 : ℝ) * linearTrace X) • (1 : H3Zorn ℝ)) = 0
    rw [sub_eq_add_neg, linearTrace_add,
      show -(((1 / 3 : ℝ) * linearTrace X) • (1 : H3Zorn ℝ)) =
        (-((1 / 3 : ℝ) * linearTrace X)) • (1 : H3Zorn ℝ) by module,
      linearTrace_smul]
    have h1 : linearTrace (1 : H3Zorn ℝ) = 3 := by
      change (1 : ℝ) + 1 + 1 = 3; norm_num
    rw [h1]
    ring⟩
  map_add' X Y := by
    apply Subtype.ext
    change (X + Y) - ((1 / 3 : ℝ) * linearTrace (X + Y)) • (1 : H3Zorn ℝ) =
      (X - ((1 / 3 : ℝ) * linearTrace X) • (1 : H3Zorn ℝ)) +
        (Y - ((1 / 3 : ℝ) * linearTrace Y) • (1 : H3Zorn ℝ))
    rw [linearTrace_add]
    module
  map_smul' r X := by
    apply Subtype.ext
    change (r • X) - ((1 / 3 : ℝ) * linearTrace (r • X)) • (1 : H3Zorn ℝ) =
      r • (X - ((1 / 3 : ℝ) * linearTrace X) • (1 : H3Zorn ℝ))
    rw [linearTrace_smul]
    module

@[simp] theorem h3Proj0_coe (X : H3Zorn ℝ) :
    (h3Proj0 X : H3Zorn ℝ) = X - ((1 / 3 : ℝ) * linearTrace X) • (1 : H3Zorn ℝ) := rfl

theorem h3Proj0_of_mem (x : h3TraceZero) : h3Proj0 x.1 = x := by
  apply Subtype.ext
  have hx : linearTrace x.1 = 0 := x.2
  simp [hx]

theorem h3Proj0_smul_one (r : ℝ) : h3Proj0 (r • (1 : H3Zorn ℝ)) = 0 := by
  apply Subtype.ext
  have h1 : linearTrace (1 : H3Zorn ℝ) = 3 := by change (1 : ℝ) + 1 + 1 = 3; norm_num
  simp only [h3Proj0_coe, linearTrace_smul, h1, Submodule.coe_zero]
  module

/-- Traceless Jordan product `x *₀ y` on `h3TraceZero`. -/
def h3Mul0 (x y : h3TraceZero) : h3TraceZero :=
  ⟨x.1 * y.1 - ((1 / 3 : ℝ) * traceBilin x.1 y.1) • (1 : H3Zorn ℝ), by
    change linearTrace (x.1 * y.1 - ((1 / 3 : ℝ) * traceBilin x.1 y.1) • (1 : H3Zorn ℝ)) = 0
    rw [sub_eq_add_neg, linearTrace_add,
      show -(((1 / 3 : ℝ) * traceBilin x.1 y.1) • (1 : H3Zorn ℝ)) =
        (-((1 / 3 : ℝ) * traceBilin x.1 y.1)) • (1 : H3Zorn ℝ) by module,
      linearTrace_smul]
    have htr : linearTrace (x.1 * y.1) = traceBilin x.1 y.1 := by
      rw [← traceBilin_one, h3Zorn_traceBilin_jordanLmul_assoc x.1 y.1 1]
      change traceBilin y.1 (candidateJordanMul x.1 1) = traceBilin x.1 y.1
      rw [candidateJordanMul_one_right, traceBilin_symm]
    have h1 : linearTrace (1 : H3Zorn ℝ) = 3 := by change (1 : ℝ) + 1 + 1 = 3; norm_num
    rw [htr, h1]
    ring⟩

@[simp] theorem h3Mul0_coe (x y : h3TraceZero) :
    (h3Mul0 x y : H3Zorn ℝ) = x.1 * y.1 - ((1 / 3 : ℝ) * traceBilin x.1 y.1) • (1 : H3Zorn ℝ) :=
  rfl

theorem h3Mul0_eq_proj0 (x y : h3TraceZero) :
    h3Mul0 x y = h3Proj0 (x.1 * y.1) := by
  apply Subtype.ext
  have htr : linearTrace (x.1 * y.1) = traceBilin x.1 y.1 := by
    rw [← traceBilin_one, h3Zorn_traceBilin_jordanLmul_assoc x.1 y.1 1]
    change traceBilin y.1 (candidateJordanMul x.1 1) = traceBilin x.1 y.1
    rw [candidateJordanMul_one_right, traceBilin_symm]
  simp [h3Mul0_coe, h3Proj0_coe, htr]

/-- Bilinear `ℝ`-linear map version of `h3Mul0`. -/
def h3Mul0LM : h3TraceZero →ₗ[ℝ] h3TraceZero →ₗ[ℝ] h3TraceZero :=
  LinearMap.mk₂ ℝ h3Mul0
    (fun x₁ x₂ y => by
      apply Subtype.ext
      simp only [h3Mul0_coe, Submodule.coe_add, add_mul, traceBilin_add_left]
      module)
    (fun r x y => by
      apply Subtype.ext
      simp only [h3Mul0_coe, SetLike.val_smul, smul_mul_assoc, traceBilin_smul_left]
      module)
    (fun x y₁ y₂ => by
      apply Subtype.ext
      simp only [h3Mul0_coe, Submodule.coe_add, mul_add, traceBilin_add_right]
      module)
    (fun r x y => by
      apply Subtype.ext
      simp only [h3Mul0_coe, SetLike.val_smul, mul_smul_comm, traceBilin_smul_right]
      module)

@[simp] theorem h3Mul0LM_apply (x y : h3TraceZero) :
    h3Mul0LM x y = h3Mul0 x y := rfl

theorem h3Mul0_comm (x y : h3TraceZero) : h3Mul0 x y = h3Mul0 y x := by
  apply Subtype.ext
  simp only [h3Mul0_coe, mul_comm x.1 y.1, traceBilin_symm x.1 y.1]

/-- Action of `F4DerivationCarrier` (`H3ZornF4Derivations`) on `h3TraceZero`. -/
def f4Act (D : F4DerivationCarrier) (x : h3TraceZero) : h3TraceZero :=
  ⟨D.1 x.1, h3ZornF4_derivation_linearTrace_zero D x.1⟩

@[simp] theorem f4Act_coe (D : F4DerivationCarrier) (x : h3TraceZero) :
    (f4Act D x : H3Zorn ℝ) = D.1 x.1 := rfl

/-- Bilinear `ℝ`-linear action of `F4DerivationCarrier` on `h3TraceZero`. -/
def f4ActLM : F4DerivationCarrier →ₗ[ℝ] h3TraceZero →ₗ[ℝ] h3TraceZero :=
  LinearMap.mk₂ ℝ f4Act
    (fun D₁ D₂ x => by apply Subtype.ext; rfl)
    (fun r D x => by apply Subtype.ext; rfl)
    (fun D x₁ x₂ => by apply Subtype.ext; exact D.1.map_add x₁.1 x₂.1)
    (fun r D x => by apply Subtype.ext; exact D.1.map_smul r x.1)

@[simp] theorem f4ActLM_apply (D : F4DerivationCarrier) (x : h3TraceZero) :
    f4ActLM D x = f4Act D x := rfl

/-- Inner Jordan derivation `[L_x, L_y]` in `F4DerivationCarrier`. -/
def f4Inner (x y : h3TraceZero) : F4DerivationCarrier :=
  ⟨(h3ZornJordanInnerDerivation x.1 y.1 : Module.End ℝ (H3Zorn ℝ)),
    h3ZornJordanInnerDerivation_mem_F4 x.1 y.1⟩

/-- Bilinear `ℝ`-linear inner derivation map into `F4DerivationCarrier`. -/
def f4InnerLM : h3TraceZero →ₗ[ℝ] h3TraceZero →ₗ[ℝ] F4DerivationCarrier :=
  LinearMap.mk₂ ℝ f4Inner
    (fun x₁ x₂ y => by
      apply Subtype.ext; apply LinearMap.ext; intro z
      change (x₁.1 + x₂.1) * (y.1 * z) - y.1 * ((x₁.1 + x₂.1) * z) =
        (x₁.1 * (y.1 * z) - y.1 * (x₁.1 * z)) + (x₂.1 * (y.1 * z) - y.1 * (x₂.1 * z))
      simp only [add_mul, mul_add]
      abel)
    (fun r x y => by
      apply Subtype.ext; apply LinearMap.ext; intro z
      change (r • x.1) * (y.1 * z) - y.1 * ((r • x.1) * z) =
        r • (x.1 * (y.1 * z) - y.1 * (x.1 * z))
      simp only [smul_mul_assoc, mul_smul_comm]
      module)
    (fun x y₁ y₂ => by
      apply Subtype.ext; apply LinearMap.ext; intro z
      change x.1 * ((y₁.1 + y₂.1) * z) - (y₁.1 + y₂.1) * (x.1 * z) =
        (x.1 * (y₁.1 * z) - y₁.1 * (x.1 * z)) + (x.1 * (y₂.1 * z) - y₂.1 * (x.1 * z))
      simp only [mul_add, add_mul]
      abel)
    (fun r x y => by
      apply Subtype.ext; apply LinearMap.ext; intro z
      change x.1 * ((r • y.1) * z) - (r • y.1) * (x.1 * z) =
        r • (x.1 * (y.1 * z) - y.1 * (x.1 * z))
      simp only [mul_smul_comm, smul_mul_assoc]
      module)

@[simp] theorem f4InnerLM_apply (x y : h3TraceZero) :
    f4InnerLM x y = f4Inner x y := rfl

theorem f4Inner_self (x : h3TraceZero) : f4Inner x x = 0 := by
  apply Subtype.ext; apply LinearMap.ext; intro z
  simp [f4Inner]

theorem f4Inner_antisymm (x y : h3TraceZero) : f4Inner y x = -f4Inner x y := by
  apply Subtype.ext; apply LinearMap.ext; intro z
  change y.1 * (x.1 * z) - x.1 * (y.1 * z) = -(x.1 * (y.1 * z) - y.1 * (x.1 * z))
  abel

/-- Bilinear pairing `traceBilin` restricted to `h3TraceZero`. -/
def traceBilin0LM : h3TraceZero →ₗ[ℝ] h3TraceZero →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => traceBilin x.1 y.1)
    (fun x₁ x₂ y => traceBilin_add_left x₁.1 x₂.1 y.1)
    (fun r x y => traceBilin_smul_left r x.1 y.1)
    (fun x y₁ y₂ => traceBilin_add_right x.1 y₁.1 y₂.1)
    (fun r x y => traceBilin_smul_right r x.1 y.1)

@[simp] theorem traceBilin0LM_apply (x y : h3TraceZero) :
    traceBilin0LM x y = traceBilin x.1 y.1 := rfl

end TracelessOperations

/-! ## 2. Decoupled 7D Split-Octonion Identities -/

section OctonionIdentities

theorem zorn_conj_eq_neg_of_trace_zero (a : splitOctonionTraceZero) :
    ZornVectorMatrix.conj a.1 = -a.1 := by
  have h : a.1 + ZornVectorMatrix.conj a.1 =
      ZornVectorMatrix.scalar (ZornVectorMatrix.trace a.1) :=
    ZornVectorMatrix.conj_trace_identity a.1
  have htr : ZornVectorMatrix.trace a.1 = 0 := a.2
  have hsz : ZornVectorMatrix.scalar (0 : ℝ) = (0 : VZ) := by
    ext <;> simp [ZornVectorMatrix.scalar, ZornVectorMatrix.zero]
  rw [htr, hsz] at h
  exact eq_neg_of_add_eq_zero_right h

theorem zorn_sq_eq_neg_norm_smul_one (a : splitOctonionTraceZero) :
    a.1 * a.1 = -(ZornVectorMatrix.norm a.1) • (ZornVectorMatrix.one : VZ) := by
  have ch := (ZornVectorMatrix.zorn_involution_cayley_hamilton_and_antiautomorphism a.1 a.1).2.2.2.1
  have htr : ZornVectorMatrix.trace a.1 = 0 := a.2
  rw [htr, zero_smul, sub_zero] at ch
  exact eq_neg_of_add_eq_zero_left ch |>.trans (by rw [neg_smul])

theorem zorn_anticommutator_traceZero (a b : splitOctonionTraceZero) :
    a.1 * b.1 + b.1 * a.1 = -(zornBilin a.1 b.1) • (ZornVectorMatrix.one : VZ) := by
  have hsum := zorn_sq_eq_neg_norm_smul_one (a + b)
  have ha := zorn_sq_eq_neg_norm_smul_one a
  have hb := zorn_sq_eq_neg_norm_smul_one b
  have hnorm : ZornVectorMatrix.norm (a.1 + b.1) =
      ZornVectorMatrix.norm a.1 + ZornVectorMatrix.norm b.1 + zornBilin a.1 b.1 :=
    zornBilin_norm_add a.1 b.1
  change (a.1 + b.1) * (a.1 + b.1) = -(ZornVectorMatrix.norm (a.1 + b.1)) • ZornVectorMatrix.one at hsum
  rw [add_mul, mul_add, mul_add, ha, hb, hnorm] at hsum
  have h1 : (-(ZornVectorMatrix.norm a.1) • (ZornVectorMatrix.one : VZ)) + a.1 * b.1 +
      (b.1 * a.1 + -(ZornVectorMatrix.norm b.1) • (ZornVectorMatrix.one : VZ)) =
    a.1 * b.1 + b.1 * a.1 + (-(ZornVectorMatrix.norm a.1) • (ZornVectorMatrix.one : VZ) +
      -(ZornVectorMatrix.norm b.1) • (ZornVectorMatrix.one : VZ)) := by abel
  have h2 : -(ZornVectorMatrix.norm a.1 + ZornVectorMatrix.norm b.1 + zornBilin a.1 b.1) •
      (ZornVectorMatrix.one : VZ) =
    -(zornBilin a.1 b.1) • (ZornVectorMatrix.one : VZ) +
      (-(ZornVectorMatrix.norm a.1) • (ZornVectorMatrix.one : VZ) +
      -(ZornVectorMatrix.norm b.1) • (ZornVectorMatrix.one : VZ)) := by
    simp only [neg_add, add_smul, neg_smul]
    abel
  rw [h1, h2] at hsum
  exact add_right_cancel hsum

theorem zornBilin_deriv_skew (D : G2DerivationCarrier) (a b : splitOctonionTraceZero) :
    zornBilin (D a.1) b.1 + zornBilin a.1 (D b.1) = 0 := by
  have h := InfoGeometry.Lie.SplitDerivationCoordinates.every_derivation_norm_skew D a.1 b.1
  have hp (x y : VZ) : QuadraticMap.polar ZornVectorMatrix.norm x y = zornBilin x y := by
    change ZornVectorMatrix.norm (x + y) - ZornVectorMatrix.norm x - ZornVectorMatrix.norm y =
      zornBilin x y
    rw [zornBilin_norm_add]
    ring
  rwa [hp, hp] at h

theorem zornBilin_comm_cyclic (a b c : splitOctonionTraceZero) :
    zornBilin a.1 (zornComm0 b c).1 = zornBilin b.1 (zornComm0 c a).1 := by
  have h1 : ∀ u v w : splitOctonionTraceZero,
      zornBilin u.1 (zornComm0 v w).1 =
        -ZornVectorMatrix.trace (u.1 * (v.1 * w.1)) +
        ZornVectorMatrix.trace (u.1 * (w.1 * v.1)) := by
    intro u v w
    change ZornVectorMatrix.trace (ZornVectorMatrix.mul u.1 (ZornVectorMatrix.conj (zornComm0 v w).1)) = _
    rw [zorn_conj_eq_neg_of_trace_zero (zornComm0 v w)]
    change ZornVectorMatrix.trace (ZornVectorMatrix.mul u.1 (ZornVectorMatrix.neg (v.1 * w.1 - w.1 * v.1))) = _
    rw [ZornVectorMatrix.mul_neg, ZornVectorMatrix.trace_neg,
      show v.1 * w.1 - w.1 * v.1 = ZornVectorMatrix.sub (v.1 * w.1) (w.1 * v.1) from rfl,
      ZornVectorMatrix.mul_sub, ZornVectorMatrix.trace_sub]
    change -(ZornVectorMatrix.trace (ZornVectorMatrix.mul u.1 (v.1 * w.1)) -
        ZornVectorMatrix.trace (ZornVectorMatrix.mul u.1 (w.1 * v.1))) =
      -ZornVectorMatrix.trace (ZornVectorMatrix.mul u.1 (v.1 * w.1)) +
        ZornVectorMatrix.trace (ZornVectorMatrix.mul u.1 (w.1 * v.1))
    ring
  rw [h1 a b c, h1 b c a]
  have cyc1 : ZornVectorMatrix.trace (a.1 * (b.1 * c.1)) =
      ZornVectorMatrix.trace (b.1 * (c.1 * a.1)) := by
    change ZornVectorMatrix.trace (ZornVectorMatrix.mul a.1 (ZornVectorMatrix.mul b.1 c.1)) =
      ZornVectorMatrix.trace (ZornVectorMatrix.mul b.1 (ZornVectorMatrix.mul c.1 a.1))
    rw [← ZornVectorMatrix.trace_mul_assoc, ZornVectorMatrix.trace_mul_cyclic,
      ZornVectorMatrix.trace_mul_assoc]
  have cyc2 : ZornVectorMatrix.trace (a.1 * (c.1 * b.1)) =
      ZornVectorMatrix.trace (b.1 * (a.1 * c.1)) := by
    change ZornVectorMatrix.trace (ZornVectorMatrix.mul a.1 (ZornVectorMatrix.mul c.1 b.1)) =
      ZornVectorMatrix.trace (ZornVectorMatrix.mul b.1 (ZornVectorMatrix.mul a.1 c.1))
    rw [← ZornVectorMatrix.trace_mul_assoc, ← ZornVectorMatrix.trace_mul_cyclic,
      ZornVectorMatrix.trace_mul_assoc]
  rw [cyc1, cyc2]

theorem g2_covariant (D : G2DerivationCarrier) (a b : splitOctonionTraceZero) :
    ⁅D, g2Inner a b⁆ = g2Inner (g2Act D a) b + g2Inner a (g2Act D b) := by
  apply ZornVectorMatrix.Derivation.ext
  intro x
  have hc := NonAssocDerivation.stanDerMap_covariant (toNonAssocDerivation D) a.1 b.1 x
  change D (innerDerivation a.1 b.1 x) - innerDerivation a.1 b.1 (D x) =
    innerDerivation (D a.1) b.1 x + innerDerivation a.1 (D b.1) x
  exact hc

theorem g2Act_lie (D E : G2DerivationCarrier) (a : splitOctonionTraceZero) :
    g2Act ⁅D, E⁆ a = g2Act D (g2Act E a) - g2Act E (g2Act D a) := by
  apply Subtype.ext
  rfl

theorem g2Act_zornComm0 (D : G2DerivationCarrier) (a b : splitOctonionTraceZero) :
    g2Act D (zornComm0 a b) = zornComm0 (g2Act D a) b + zornComm0 a (g2Act D b) := by
  apply Subtype.ext
  simp only [g2Act_coe, zornComm0_coe, Submodule.coe_add]
  have hsub : D (a.1 * b.1 - b.1 * a.1) = D (a.1 * b.1) - D (b.1 * a.1) :=
    (toNonAssocDerivation D).toLinearMap.map_sub (a.1 * b.1) (b.1 * a.1)
  have h1 : D (a.1 * b.1) = D a.1 * b.1 + a.1 * D b.1 := D.map_mul a.1 b.1
  have h2 : D (b.1 * a.1) = D b.1 * a.1 + b.1 * D a.1 := D.map_mul b.1 a.1
  rw [hsub, h1, h2]
  abel

private theorem zorn_mul_one_right (x : VZ) : x * ZornVectorMatrix.one = x :=
  ZornVectorMatrix.mul_one x

private theorem zorn_one_mul_left (x : VZ) : ZornVectorMatrix.one * x = x :=
  ZornVectorMatrix.one_mul x

/-- Decoupled 7D Octonion Identity 2 (symmetric triple form):
`[b, [c, a]] - [c, [a, b]] + 6 ⟨b, c⟩ a = 2 (⟨b, c⟩ a + ⟨c, a⟩ b + ⟨a, b⟩ c)`. -/
theorem octonion_comm_double_identity (a b c : splitOctonionTraceZero) :
    (b.1 * (c.1 * a.1 - a.1 * c.1) - (c.1 * a.1 - a.1 * c.1) * b.1) -
      (c.1 * (a.1 * b.1 - b.1 * a.1) - (a.1 * b.1 - b.1 * a.1) * c.1) +
      (6 : ℝ) • (zornBilin b.1 c.1 • a.1) =
    (2 : ℝ) • (zornBilin b.1 c.1 • a.1 + zornBilin c.1 a.1 • b.1 + zornBilin a.1 b.1 • c.1) := by
  have hca : a.1 * c.1 = -(c.1 * a.1) - zornBilin c.1 a.1 • ZornVectorMatrix.one := by
    have h := zorn_anticommutator_traceZero c a
    rw [eq_sub_of_add_eq' h]
    module
  have hab : a.1 * b.1 = -(b.1 * a.1) - zornBilin a.1 b.1 • ZornVectorMatrix.one := by
    have h := zorn_anticommutator_traceZero a b
    rw [eq_sub_of_add_eq' h]
    module
  have hbc : b.1 * c.1 + c.1 * b.1 = -(zornBilin b.1 c.1) • ZornVectorMatrix.one :=
    zorn_anticommutator_traceZero b c
  have hL : b.1 * (c.1 * a.1) + c.1 * (b.1 * a.1) = -(zornBilin b.1 c.1) • a.1 := by
    have h := alternative_left_linearized zorn_left_alternative b.1 c.1 a.1
    rw [← add_mul, hbc, neg_smul, neg_mul, smul_mul_assoc, zorn_one_mul_left] at h
    rw [neg_smul]
    exact h.symm
  have hR : (a.1 * b.1) * c.1 + (a.1 * c.1) * b.1 = -(zornBilin b.1 c.1) • a.1 := by
    have h := alternative_right_linearized zorn_right_alternative b.1 c.1 a.1
    rw [← mul_add, hbc, neg_smul, mul_neg, mul_smul_comm, zorn_mul_one_right] at h
    rw [neg_smul]
    exact h
  have h1 : c.1 * a.1 - a.1 * c.1 = (2 : ℝ) • (c.1 * a.1) + zornBilin c.1 a.1 • ZornVectorMatrix.one := by
    rw [hca]
    module
  have h2 : a.1 * b.1 - b.1 * a.1 = -((2 : ℝ) • (b.1 * a.1)) - zornBilin a.1 b.1 • ZornVectorMatrix.one := by
    rw [hab]
    module
  have hR' : -((c.1 * a.1) * b.1) - (b.1 * a.1) * c.1 =
      -(zornBilin b.1 c.1) • a.1 + zornBilin c.1 a.1 • b.1 + zornBilin a.1 b.1 • c.1 := by
    have hca_b : (a.1 * c.1) * b.1 = -(c.1 * a.1) * b.1 - zornBilin c.1 a.1 • b.1 := by
      rw [hca, sub_mul, neg_mul, smul_mul_assoc, zorn_one_mul_left]
    have hab_c : (a.1 * b.1) * c.1 = -(b.1 * a.1) * c.1 - zornBilin a.1 b.1 • c.1 := by
      rw [hab, sub_mul, neg_mul, smul_mul_assoc, zorn_one_mul_left]
    rw [hca_b, hab_c] at hR
    have hR0 : (-((c.1 * a.1) * b.1) - (b.1 * a.1) * c.1) -
        (zornBilin c.1 a.1 • b.1 + zornBilin a.1 b.1 • c.1) = -(zornBilin b.1 c.1) • a.1 := by
      rw [← hR]
      simp only [neg_mul]
      abel
    rw [← hR0]
    abel
  rw [h1, h2]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    smul_mul_assoc, mul_smul_comm, zorn_mul_one_right, zorn_one_mul_left]
  have hcomb :
      ((2 : ℝ) • (b.1 * (c.1 * a.1)) + zornBilin c.1 a.1 • b.1 -
        ((2 : ℝ) • ((c.1 * a.1) * b.1) + zornBilin c.1 a.1 • b.1)) -
      (-((2 : ℝ) • (c.1 * (b.1 * a.1))) - zornBilin a.1 b.1 • c.1 -
        (-((2 : ℝ) • ((b.1 * a.1) * c.1)) - zornBilin a.1 b.1 • c.1)) =
      (2 : ℝ) • (b.1 * (c.1 * a.1) + c.1 * (b.1 * a.1)) +
        (2 : ℝ) • (-((c.1 * a.1) * b.1) - (b.1 * a.1) * c.1) := by
    module
  rw [hcomb, hL, hR']
  module

private theorem associator_comm_cyclic (a b c w : VZ) :
    _root_.associator a (b * c - c * b) w +
      _root_.associator b (c * a - a * c) w +
      _root_.associator c (a * b - b * a) w =
    (-2 : ℝ) • (_root_.associator a b c * w - w * _root_.associator a b c) := by
  have h12 := alternative_associator_swap12 (A := VZ) zorn_left_alternative
  have h23 := alternative_associator_swap23 (A := VZ) zorn_right_alternative
  have hcyc := alternative_associator_cycle (A := VZ) zorn_left_alternative zorn_right_alternative
  let T (A B C D : VZ) : VZ :=
    _root_.associator (A * B) C D - _root_.associator A (B * C) D +
      _root_.associator A B (C * D) - A * _root_.associator B C D - _root_.associator A B C * D
  have vz_add : ∀ p q : VZ, ZornVectorMatrix.add p q = p + q := fun _ _ => rfl
  have vz_mul : ∀ p q : VZ, ZornVectorMatrix.mul p q = p * q := fun _ _ => rfl
  have vz_neg : ∀ p : VZ, ZornVectorMatrix.neg p = -p := fun _ => rfl
  have vz_smul : ∀ (r : ℝ) (p : VZ), ZornVectorMatrix.smul r p = r • p := fun _ _ => rfl
  have vz_zero : ZornVectorMatrix.zero = (0 : VZ) := rfl
  have hT (A B C D : VZ) : T A B C D = 0 := by
    have hc := associator_cocycle A B C D
    have h_eq : T A B C D =
      -(A * _root_.associator B C D - _root_.associator (A * B) C D +
        _root_.associator A (B * C) D - _root_.associator A B (C * D) +
        _root_.associator A B C * D) := by
      dsimp [T]
      simp only [vz_add, vz_mul, vz_neg]
      abel
    rw [h_eq, hc, neg_zero]
  have hS4 (x y z : VZ) :
      T x y z w - T x z y w =
        (_root_.associator (x * y) z w - _root_.associator (x * z) y w) -
        _root_.associator x (y * z - z * y) w +
        (_root_.associator x y (z * w) - _root_.associator x z (y * w)) -
        (2 : ℝ) • (x * _root_.associator y z w) -
        (2 : ℝ) • (_root_.associator x y z * w) := by
    dsimp [T]
    simp only [vz_add, vz_mul, vz_smul]
    have hassoc_sub (p q r s : VZ) :
        _root_.associator p (q - r) s = _root_.associator p q s - _root_.associator p r s := by
      simp only [_root_.associator_apply, mul_sub, sub_mul]; abel
    have hm : ∀ u v : VZ, u * (-v) = -(u * v) := _root_.mul_neg
    have mh : ∀ u v : VZ, (-u) * v = -(u * v) := _root_.neg_mul
    rw [hassoc_sub, h23 x z y, h12 z y w, hm, mh]
    have h2r (p : VZ) : (2 : ℝ) • p = p + p := two_smul ℝ p
    rw [h2r, h2r]
    abel
  have hS1 (x y z : VZ) :
      T w x y z - T w x z y =
        (2 : ℝ) • _root_.associator (w * x) y z -
        (_root_.associator w (x * y) z - _root_.associator w (x * z) y) +
        _root_.associator w x (y * z - z * y) -
        (2 : ℝ) • (w * _root_.associator x y z) -
        (_root_.associator w x y * z - _root_.associator w x z * y) := by
    dsimp [T]
    simp only [vz_add, vz_mul, vz_smul]
    have hassoc_sub (p q r s : VZ) :
        _root_.associator p q (r - s) = _root_.associator p q r - _root_.associator p q s := by
      simp only [_root_.associator_apply, mul_sub]; abel
    have hm : ∀ u v : VZ, u * (-v) = -(u * v) := _root_.mul_neg
    rw [hassoc_sub, h23 (w * x) z y, h23 x z y, hm]
    have h2r (p : VZ) : (2 : ℝ) • p = p + p := two_smul ℝ p
    rw [h2r, h2r]
    abel
  have hS3 (x y z : VZ) :
      T x y w z - T x z w y =
        (_root_.associator (x * y) w z - _root_.associator (x * z) w y) -
        (_root_.associator x (y * w) z - _root_.associator x (z * w) y) +
        (_root_.associator x y (w * z) - _root_.associator x z (w * y)) -
        (x * _root_.associator y w z - x * _root_.associator z w y) -
        (_root_.associator x y w * z - _root_.associator x z w * y) := by
    dsimp [T]
    simp only [vz_add, vz_mul]
    abel
  have hsum :
      (T a b c w - T a c b w) + (T b c a w - T b a c w) + (T c a b w - T c b a w) -
      ((T w a b c - T w a c b) + (T w b c a - T w b a c) + (T w c a b - T w c b a)) +
      ((T a b w c - T a c w b) + (T b c w a - T b a w c) + (T c a w b - T c b w a)) = 0 := by
    simp only [hT, sub_self, add_zero]
  rw [hS4 a b c, hS4 b c a, hS4 c a b,
      hS1 a b c, hS1 b c a, hS1 c a b,
      hS3 a b c, hS3 b c a, hS3 c a b] at hsum
  have hw1 (u v : VZ) : _root_.associator w u v = _root_.associator u v w := (hcyc w u v).symm
  have hw2 (u v : VZ) : _root_.associator u w v = -_root_.associator u v w := h23 u w v
  have habc1 : _root_.associator b c a = _root_.associator a b c := hcyc a b c
  have habc2 : _root_.associator c a b = _root_.associator a b c := (hcyc b c a).trans habc1
  simp only [hw1, hw2] at hsum
  have hwx1 : _root_.associator (w * a) b c = _root_.associator b c (w * a) := (hcyc (w * a) b c).symm
  have hwx2 : _root_.associator (w * b) c a = _root_.associator c a (w * b) := (hcyc (w * b) c a).symm
  have hwx3 : _root_.associator (w * c) a b = _root_.associator a b (w * c) := (hcyc (w * c) a b).symm
  rw [hwx1, hwx2, hwx3] at hsum
  have hyw1 : _root_.associator a (b * w) c = _root_.associator c a (b * w) := hcyc c a (b * w)
  have hyw2 : _root_.associator a (c * w) b = _root_.associator b a (c * w) := hcyc b a (c * w)
  have hyw3 : _root_.associator b (c * w) a = _root_.associator a b (c * w) := hcyc a b (c * w)
  have hyw4 : _root_.associator b (a * w) c = _root_.associator c b (a * w) := hcyc c b (a * w)
  have hyw5 : _root_.associator c (a * w) b = _root_.associator b c (a * w) := hcyc b c (a * w)
  have hyw6 : _root_.associator c (b * w) a = _root_.associator a c (b * w) := hcyc a c (b * w)
  rw [hyw1, hyw2, hyw3, hyw4, hyw5, hyw6] at hsum
  have hflip1 (p : VZ) : _root_.associator b a p = -_root_.associator a b p := h12 b a p
  have hflip2 (p : VZ) : _root_.associator c b p = -_root_.associator b c p := h12 c b p
  have hflip3 (p : VZ) : _root_.associator a c p = -_root_.associator c a p := h12 a c p
  simp only [hflip1, hflip2, hflip3] at hsum
  rw [habc1, habc2] at hsum
  have hassoc_sub_mid (p q r s : VZ) :
      _root_.associator p (q - r) s = _root_.associator p q s - _root_.associator p r s := by
    simp only [_root_.associator_apply, mul_sub, sub_mul]; abel
  have hpq1 : _root_.associator (a * b) c w = -_root_.associator c (a * b) w := h12 _ _ _
  have hpq2 : _root_.associator (a * c) b w = -_root_.associator b (a * c) w := h12 _ _ _
  have hpq3 : _root_.associator (b * c) a w = -_root_.associator a (b * c) w := h12 _ _ _
  have hpq4 : _root_.associator (b * a) c w = -_root_.associator c (b * a) w := h12 _ _ _
  have hpq5 : _root_.associator (c * a) b w = -_root_.associator b (c * a) w := h12 _ _ _
  have hpq6 : _root_.associator (c * b) a w = -_root_.associator a (c * b) w := h12 _ _ _
  rw [hpq1, hpq2, hpq3, hpq4, hpq5, hpq6] at hsum
  simp only [hassoc_sub_mid] at hsum
  simp only [neg_neg, _root_.mul_neg, _root_.neg_mul, sub_neg_eq_add] at hsum
  have h3 : (3 : ℝ) • (_root_.associator a (b * c - c * b) w +
      _root_.associator b (c * a - a * c) w +
      _root_.associator c (a * b - b * a) w) =
    (-6 : ℝ) • (_root_.associator a b c * w - w * _root_.associator a b c) := by
    simp only [hassoc_sub_mid]
    refine sub_eq_zero.mp (Eq.trans ?_ ((congrArg Neg.neg hsum).trans neg_zero))
    module
  have hinv := congrArg (fun z : VZ => (1 / 3 : ℝ) • z) h3
  simp only [smul_smul] at hinv
  norm_num at hinv
  simp only [vz_add, vz_mul, vz_neg, vz_smul] at hinv
  simpa using hinv

/-- Decoupled 7D Octonion Identity 1:
`D_{a, [b, c]} + D_{b, [c, a]} + D_{c, [a, b]} = 0`. -/
theorem stanDer_comm_cyclic_zero (a b c : splitOctonionTraceZero) :
    g2Inner a (zornComm0 b c) + g2Inner b (zornComm0 c a) + g2Inner c (zornComm0 a b) = 0 := by
  apply ZornVectorMatrix.Derivation.ext
  intro w
  change innerDerivation a.1 (b.1 * c.1 - c.1 * b.1) w +
      innerDerivation b.1 (c.1 * a.1 - a.1 * c.1) w +
      innerDerivation c.1 (a.1 * b.1 - b.1 * a.1) w = 0
  rw [innerDerivation_operatorial_normal_form, innerDerivation_operatorial_normal_form,
    innerDerivation_operatorial_normal_form]
  have hjac :
      (a.1 * (b.1 * c.1 - c.1 * b.1) - (b.1 * c.1 - c.1 * b.1) * a.1) +
        (b.1 * (c.1 * a.1 - a.1 * c.1) - (c.1 * a.1 - a.1 * c.1) * b.1) +
        (c.1 * (a.1 * b.1 - b.1 * a.1) - (a.1 * b.1 - b.1 * a.1) * c.1) =
      (-6 : ℝ) • ZornVectorMatrix.zornAssociator a.1 b.1 c.1 := by
    exact ZornVectorMatrix.zornJacobiator_eq_neg_six_smul_zornAssociator a.1 b.1 c.1
  have hassoc :
      ((a.1 * (b.1 * c.1 - c.1 * b.1) - (b.1 * c.1 - c.1 * b.1) * a.1) * w -
        w * (a.1 * (b.1 * c.1 - c.1 * b.1) - (b.1 * c.1 - c.1 * b.1) * a.1)) +
      ((b.1 * (c.1 * a.1 - a.1 * c.1) - (c.1 * a.1 - a.1 * c.1) * b.1) * w -
        w * (b.1 * (c.1 * a.1 - a.1 * c.1) - (c.1 * a.1 - a.1 * c.1) * b.1)) +
      ((c.1 * (a.1 * b.1 - b.1 * a.1) - (a.1 * b.1 - b.1 * a.1) * c.1) * w -
        w * (c.1 * (a.1 * b.1 - b.1 * a.1) - (a.1 * b.1 - b.1 * a.1) * c.1)) =
      (-6 : ℝ) • (_root_.associator a.1 b.1 c.1 * w - w * _root_.associator a.1 b.1 c.1) := by
    have hsum :
        ((a.1 * (b.1 * c.1 - c.1 * b.1) - (b.1 * c.1 - c.1 * b.1) * a.1) +
          (b.1 * (c.1 * a.1 - a.1 * c.1) - (c.1 * a.1 - a.1 * c.1) * b.1) +
          (c.1 * (a.1 * b.1 - b.1 * a.1) - (a.1 * b.1 - b.1 * a.1) * c.1)) * w -
        w * ((a.1 * (b.1 * c.1 - c.1 * b.1) - (b.1 * c.1 - c.1 * b.1) * a.1) +
          (b.1 * (c.1 * a.1 - a.1 * c.1) - (c.1 * a.1 - a.1 * c.1) * b.1) +
          (c.1 * (a.1 * b.1 - b.1 * a.1) - (a.1 * b.1 - b.1 * a.1) * c.1)) =
        (-6 : ℝ) • (_root_.associator a.1 b.1 c.1 * w - w * _root_.associator a.1 b.1 c.1) := by
      rw [hjac]
      simp only [smul_mul_assoc, mul_smul_comm, smul_sub]
      rfl
    simp only [add_mul, mul_add] at hsum
    rw [← hsum]
    abel
  have hcyc := associator_comm_cyclic a.1 b.1 c.1 w
  have h3_comm :
      (3 : ℕ) • _root_.associator a.1 (b.1 * c.1 - c.1 * b.1) w +
        (3 : ℕ) • _root_.associator b.1 (c.1 * a.1 - a.1 * c.1) w +
        (3 : ℕ) • _root_.associator c.1 (a.1 * b.1 - b.1 * a.1) w =
      (-6 : ℝ) • (_root_.associator a.1 b.1 c.1 * w - w * _root_.associator a.1 b.1 c.1) := by
    have h3s : ∀ u : VZ, (3 : ℕ) • u = (3 : ℝ) • u := fun u => by module
    rw [h3s, h3s, h3s, ← smul_add, ← smul_add, hcyc, smul_smul]
    norm_num
  have hgoal :
      (((a.1 * (b.1 * c.1 - c.1 * b.1) - (b.1 * c.1 - c.1 * b.1) * a.1) * w -
          w * (a.1 * (b.1 * c.1 - c.1 * b.1) - (b.1 * c.1 - c.1 * b.1) * a.1)) -
        3 • _root_.associator a.1 (b.1 * c.1 - c.1 * b.1) w) +
      (((b.1 * (c.1 * a.1 - a.1 * c.1) - (c.1 * a.1 - a.1 * c.1) * b.1) * w -
          w * (b.1 * (c.1 * a.1 - a.1 * c.1) - (c.1 * a.1 - a.1 * c.1) * b.1)) -
        3 • _root_.associator b.1 (c.1 * a.1 - a.1 * c.1) w) +
      (((c.1 * (a.1 * b.1 - b.1 * a.1) - (a.1 * b.1 - b.1 * a.1) * c.1) * w -
          w * (c.1 * (a.1 * b.1 - b.1 * a.1) - (a.1 * b.1 - b.1 * a.1) * c.1)) -
        3 • _root_.associator c.1 (a.1 * b.1 - b.1 * a.1) w) = 0 := by
    have hre :
        (((a.1 * (b.1 * c.1 - c.1 * b.1) - (b.1 * c.1 - c.1 * b.1) * a.1) * w -
            w * (a.1 * (b.1 * c.1 - c.1 * b.1) - (b.1 * c.1 - c.1 * b.1) * a.1)) -
          3 • _root_.associator a.1 (b.1 * c.1 - c.1 * b.1) w) +
        (((b.1 * (c.1 * a.1 - a.1 * c.1) - (c.1 * a.1 - a.1 * c.1) * b.1) * w -
            w * (b.1 * (c.1 * a.1 - a.1 * c.1) - (c.1 * a.1 - a.1 * c.1) * b.1)) -
          3 • _root_.associator b.1 (c.1 * a.1 - a.1 * c.1) w) +
        (((c.1 * (a.1 * b.1 - b.1 * a.1) - (a.1 * b.1 - b.1 * a.1) * c.1) * w -
            w * (c.1 * (a.1 * b.1 - b.1 * a.1) - (a.1 * b.1 - b.1 * a.1) * c.1)) -
          3 • _root_.associator c.1 (a.1 * b.1 - b.1 * a.1) w) =
        (((a.1 * (b.1 * c.1 - c.1 * b.1) - (b.1 * c.1 - c.1 * b.1) * a.1) * w -
            w * (a.1 * (b.1 * c.1 - c.1 * b.1) - (b.1 * c.1 - c.1 * b.1) * a.1)) +
          ((b.1 * (c.1 * a.1 - a.1 * c.1) - (c.1 * a.1 - a.1 * c.1) * b.1) * w -
            w * (b.1 * (c.1 * a.1 - a.1 * c.1) - (c.1 * a.1 - a.1 * c.1) * b.1)) +
          ((c.1 * (a.1 * b.1 - b.1 * a.1) - (a.1 * b.1 - b.1 * a.1) * c.1) * w -
            w * (c.1 * (a.1 * b.1 - b.1 * a.1) - (a.1 * b.1 - b.1 * a.1) * c.1))) -
          ((3 : ℕ) • _root_.associator a.1 (b.1 * c.1 - c.1 * b.1) w +
            (3 : ℕ) • _root_.associator b.1 (c.1 * a.1 - a.1 * c.1) w +
            (3 : ℕ) • _root_.associator c.1 (a.1 * b.1 - b.1 * a.1) w) := by abel
    rw [hre, hassoc, h3_comm, sub_self]
  exact hgoal

theorem kleinfeld_traceZero_combo (a b c : splitOctonionTraceZero) :
    -(ZornVectorMatrix.zornAssociator a.1 b.1 c.1) -
      (1 / 3 : ℝ) • (a.1 * (b.1 * c.1 - c.1 * b.1) - (b.1 * c.1 - c.1 * b.1) * a.1) -
      (1 / 3 : ℝ) • (g2Act (g2Inner b c) a).1 = 0 := by
  change -_root_.associator a.1 b.1 c.1 -
      (1 / 3 : ℝ) • (a.1 * (b.1 * c.1 - c.1 * b.1) - (b.1 * c.1 - c.1 * b.1) * a.1) -
      (1 / 3 : ℝ) • innerDerivation b.1 c.1 a.1 = 0
  rw [innerDerivation_operatorial_normal_form]
  change -_root_.associator a.1 b.1 c.1 -
      (1 / 3 : ℝ) • (a.1 * (b.1 * c.1 - c.1 * b.1) - (b.1 * c.1 - c.1 * b.1) * a.1) -
      (1 / 3 : ℝ) • (((b.1 * c.1 - c.1 * b.1) * a.1 - a.1 * (b.1 * c.1 - c.1 * b.1)) -
        3 • _root_.associator b.1 c.1 a.1) = 0
  have hcyc : _root_.associator b.1 c.1 a.1 = _root_.associator a.1 b.1 c.1 :=
    alternative_associator_cycle zorn_left_alternative zorn_right_alternative a.1 b.1 c.1
  rw [hcyc]
  have h3 : (3 : ℕ) • _root_.associator a.1 b.1 c.1 = (3 : ℝ) • _root_.associator a.1 b.1 c.1 := by
    module
  rw [h3]
  module

end OctonionIdentities

/-! ## 3. Decoupled 26D Split-Albert Jordan Identities -/

section JordanIdentities

theorem h3_traceBilin_mul_cyclic (x y z : h3TraceZero) :
    traceBilin x.1 (h3Mul0 y z).1 = traceBilin y.1 (h3Mul0 z x).1 := by
  have hsimp : ∀ u v w : h3TraceZero,
      traceBilin u.1 (h3Mul0 v w).1 = traceBilin u.1 (v.1 * w.1) := by
    intro u v w
    simp only [h3Mul0_coe, traceBilin_sub_right, traceBilin_smul_right, traceBilin_one]
    have hu : linearTrace u.1 = 0 := u.2
    rw [hu]
    ring
  rw [hsimp x y z, hsimp y z x, ← h3Zorn_traceBilin_jordanLmul_assoc y.1 x.1 z.1,
    mul_comm y.1 x.1, traceBilin_symm, mul_comm z.1 x.1]
  rw [← h3Zorn_traceBilin_jordanLmul_assoc x.1 z.1 y.1, mul_comm x.1 z.1]
  rw [traceBilin_symm y.1 (z.1 * x.1)]

theorem f4_derivation_traceBilin_skew0 (D : F4DerivationCarrier) (x y : h3TraceZero) :
    traceBilin (f4Act D x).1 y.1 + traceBilin x.1 (f4Act D y).1 = 0 :=
  h3ZornF4_derivation_traceBilin_skew D x.1 y.1

theorem f4Act_lie (D E : F4DerivationCarrier) (x : h3TraceZero) :
    f4Act ⁅D, E⁆ x = f4Act D (f4Act E x) - f4Act E (f4Act D x) := by
  apply Subtype.ext
  rfl

theorem f4Act_h3Mul0 (D : F4DerivationCarrier) (x y : h3TraceZero) :
    f4Act D (h3Mul0 x y) = h3Mul0 (f4Act D x) y + h3Mul0 x (f4Act D y) := by
  apply Subtype.ext
  simp only [f4Act_coe, h3Mul0_coe, Submodule.coe_add]
  have h1 : D.1 (1 : H3Zorn ℝ) = 0 := h3ZornF4_derivation_apply_one_eq_zero D
  have hskew := f4_derivation_traceBilin_skew0 D x y
  have htb : traceBilin (D.1 x.1) y.1 + traceBilin x.1 (D.1 y.1) = 0 := hskew
  rw [D.1.map_sub, D.2 x.1 y.1, map_smul, h1, smul_zero, sub_zero]
  have hcoef : ((1 / 3 : ℝ) * traceBilin (D.1 x.1) y.1 +
      (1 / 3 : ℝ) * traceBilin x.1 (D.1 y.1)) = 0 := by linarith
  have hzero : (((1 / 3 : ℝ) * traceBilin (D.1 x.1) y.1) • (1 : H3Zorn ℝ) +
      ((1 / 3 : ℝ) * traceBilin x.1 (D.1 y.1)) • (1 : H3Zorn ℝ)) = 0 := by
    rw [← add_smul, hcoef, zero_smul]
  have hsub : D.1 x.1 * y.1 - ((1 / 3 : ℝ) * traceBilin (D.1 x.1) y.1) • (1 : H3Zorn ℝ) +
      (x.1 * D.1 y.1 - ((1 / 3 : ℝ) * traceBilin x.1 (D.1 y.1)) • (1 : H3Zorn ℝ)) =
      D.1 x.1 * y.1 + x.1 * D.1 y.1 -
        (((1 / 3 : ℝ) * traceBilin (D.1 x.1) y.1) • (1 : H3Zorn ℝ) +
          ((1 / 3 : ℝ) * traceBilin x.1 (D.1 y.1)) • (1 : H3Zorn ℝ)) := by
    abel
  rw [hsub, hzero, sub_zero]

theorem f4_covariant (D : F4DerivationCarrier) (x y : h3TraceZero) :
    ⁅D, f4Inner x y⁆ = f4Inner (f4Act D x) y + f4Inner x (f4Act D y) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  have h1' : D.1 (x.1 * z) - x.1 * D.1 z = D.1 x.1 * z :=
    congrArg (fun f : Module.End ℝ (H3Zorn ℝ) => f z) (h3Zorn_derivation_lie_jordanLmul D x.1)
  have h2' : D.1 (y.1 * z) - y.1 * D.1 z = D.1 y.1 * z :=
    congrArg (fun f : Module.End ℝ (H3Zorn ℝ) => f z) (h3Zorn_derivation_lie_jordanLmul D y.1)
  have h3' : D.1 (x.1 * (y.1 * z)) - x.1 * D.1 (y.1 * z) = D.1 x.1 * (y.1 * z) :=
    congrArg (fun f : Module.End ℝ (H3Zorn ℝ) => f (y.1 * z)) (h3Zorn_derivation_lie_jordanLmul D x.1)
  have h4' : D.1 (y.1 * (x.1 * z)) - y.1 * D.1 (x.1 * z) = D.1 y.1 * (x.1 * z) :=
    congrArg (fun f : Module.End ℝ (H3Zorn ℝ) => f (x.1 * z)) (h3Zorn_derivation_lie_jordanLmul D y.1)
  have h1mul : y.1 * (D.1 (x.1 * z) - x.1 * D.1 z) = y.1 * (D.1 x.1 * z) :=
    congrArg (fun w => y.1 * w) h1'
  have h2mul : x.1 * (D.1 (y.1 * z) - y.1 * D.1 z) = x.1 * (D.1 y.1 * z) :=
    congrArg (fun w => x.1 * w) h2'
  rw [mul_sub] at h1mul h2mul
  have hDx : D.1 (x.1 * (y.1 * z)) = D.1 x.1 * (y.1 * z) + x.1 * D.1 (y.1 * z) :=
    eq_add_of_sub_eq' (by rw [← h3']; abel)
  have hDy : D.1 (y.1 * (x.1 * z)) = D.1 y.1 * (x.1 * z) + y.1 * D.1 (x.1 * z) :=
    eq_add_of_sub_eq' (by rw [← h4']; abel)
  have hxy : x.1 * (y.1 * D.1 z) = x.1 * D.1 (y.1 * z) - x.1 * (D.1 y.1 * z) :=
    eq_sub_of_add_eq (by rw [← h2mul]; abel)
  have hyx : y.1 * (x.1 * D.1 z) = y.1 * D.1 (x.1 * z) - y.1 * (D.1 x.1 * z) :=
    eq_sub_of_add_eq (by rw [← h1mul]; abel)
  change D.1 (x.1 * (y.1 * z) - y.1 * (x.1 * z)) -
      (x.1 * (y.1 * D.1 z) - y.1 * (x.1 * D.1 z)) =
    (D.1 x.1 * (y.1 * z) - y.1 * (D.1 x.1 * z)) +
      (x.1 * (D.1 y.1 * z) - D.1 y.1 * (x.1 * z))
  rw [D.1.map_sub, hDx, hDy, hxy, hyx]
  abel

/-- Decoupled 26D Jordan Identity 1:
`D^Jor_{x, y *₀ z} + D^Jor_{y, z *₀ x} + D^Jor_{z, x *₀ y} = 0`. -/
theorem f4Inner_mul_cyclic_zero (x y z : h3TraceZero) :
    f4Inner x (h3Mul0 y z) + f4Inner y (h3Mul0 z x) + f4Inner z (h3Mul0 x y) = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro w
  have hone (a : H3Zorn ℝ) : (h3ZornJordanInnerDerivation a 1 : Module.End ℝ (H3Zorn ℝ)) w = 0 := by
    simp only [h3ZornJordanInnerDerivation_apply]
    have h1 : (1 : H3Zorn ℝ) * w = w := candidateJordanMul_one_left w
    have h2 : (1 : H3Zorn ℝ) * (a * w) = a * w := candidateJordanMul_one_left (a * w)
    rw [h1, h2, sub_self]
  have hdrop (u v p : h3TraceZero) :
      (f4Inner u (h3Mul0 v p) : Module.End ℝ (H3Zorn ℝ)) w =
        (h3ZornJordanInnerDerivation u.1 (v.1 * p.1) : Module.End ℝ (H3Zorn ℝ)) w := by
    change u.1 * ((v.1 * p.1 - ((1 / 3 : ℝ) * traceBilin v.1 p.1) • (1 : H3Zorn ℝ)) * w) -
        (v.1 * p.1 - ((1 / 3 : ℝ) * traceBilin v.1 p.1) • (1 : H3Zorn ℝ)) * (u.1 * w) =
      u.1 * (v.1 * p.1 * w) - (v.1 * p.1) * (u.1 * w)
    rw [sub_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
    have hw := hone u.1
    simp only [h3ZornJordanInnerDerivation_apply] at hw
    have hsub :
        (u.1 * (v.1 * p.1 * w) - ((1 / 3 : ℝ) * traceBilin v.1 p.1) • (u.1 * (1 * w))) -
          (v.1 * p.1 * (u.1 * w) - ((1 / 3 : ℝ) * traceBilin v.1 p.1) • (1 * (u.1 * w))) =
        (u.1 * (v.1 * p.1 * w) - v.1 * p.1 * (u.1 * w)) -
          ((1 / 3 : ℝ) * traceBilin v.1 p.1) • (u.1 * (1 * w) - 1 * (u.1 * w)) := by
      module
    rw [hsub, hw, smul_zero, sub_zero]
  change (f4Inner x (h3Mul0 y z) : Module.End ℝ (H3Zorn ℝ)) w +
      (f4Inner y (h3Mul0 z x) : Module.End ℝ (H3Zorn ℝ)) w +
      (f4Inner z (h3Mul0 x y) : Module.End ℝ (H3Zorn ℝ)) w = 0
  rw [hdrop x y z, hdrop y z x, hdrop z x y]
  have hJ := two_nsmul_lie_lmul_lmul_add_add_eq_zero x.1 y.1 z.1
  rw [two_nsmul] at hJ
  have hJw := congrArg (fun f : AddMonoid.End (H3Zorn ℝ) => f w) hJ
  change (x.1 * ((y.1 * z.1) * w) - (y.1 * z.1) * (x.1 * w) +
      (y.1 * ((z.1 * x.1) * w) - (z.1 * x.1) * (y.1 * w)) +
      (z.1 * ((x.1 * y.1) * w) - (x.1 * y.1) * (z.1 * w))) +
      (x.1 * ((y.1 * z.1) * w) - (y.1 * z.1) * (x.1 * w) +
      (y.1 * ((z.1 * x.1) * w) - (z.1 * x.1) * (y.1 * w)) +
      (z.1 * ((x.1 * y.1) * w) - (x.1 * y.1) * (z.1 * w))) = 0 at hJw
  have h2r : (2 : ℝ) •
      ((x.1 * (y.1 * z.1 * w) - (y.1 * z.1) * (x.1 * w)) +
        (y.1 * (z.1 * x.1 * w) - (z.1 * x.1) * (y.1 * w)) +
        (z.1 * (x.1 * y.1 * w) - (x.1 * y.1) * (z.1 * w))) = 0 := by
    rw [two_smul]
    exact hJw
  exact (smul_eq_zero.mp h2r).resolve_left (by norm_num)

/-- Cubic Cayley–Hamilton identity on `h3TraceZero`:
`h3Proj0 (w * (w * w)) = ((1 / 2) * traceBilin w w) • w`. -/
theorem h3Proj0_cube (w : h3TraceZero) :
    h3Proj0 (w.1 * (w.1 * w.1)) = ((1 / 2 : ℝ) * traceBilin w.1 w.1) • w := by
  have hw : linearTrace w.1 = 0 := w.2
  have hsq : w.1 * w.1 =
      ((1 / 2 : ℝ) * traceBilin w.1 w.1) • (1 : H3Zorn ℝ) + adjointQuad w.1 := by
    have h1 := h3Zorn_mul_self_eq_adjoint w.1
    have hm := mccrimmon_identity_16 w.1 w.1
    rw [hw, zero_mul, zero_sub, crossProduct_self, linearTrace_smul] at hm
    have hadj : linearTrace (adjointQuad w.1) = -(1 / 2 : ℝ) * traceBilin w.1 w.1 := by
      linarith
    rw [hw, zero_smul, zero_sub, hadj] at h1
    rw [h1]
    module
  have hcube : w.1 * (w.1 * w.1) =
      ((1 / 2 : ℝ) * traceBilin w.1 w.1) • w.1 + normCubic w.1 • (1 : H3Zorn ℝ) := by
    rw [hsq, mul_add, mul_smul_comm]
    have hw1 : w.1 * (1 : H3Zorn ℝ) = w.1 := candidateJordanMul_one_right w.1
    have hwadj : w.1 * adjointQuad w.1 = normCubic w.1 • (1 : H3Zorn ℝ) :=
      h3zorn_jordan_mul_adjoint_eq_norm_one w.1
    rw [hw1, hwadj]
  rw [hcube, map_add, h3Proj0_smul_one, add_zero, map_smul, h3Proj0_of_mem w]

private theorem symmetric_trilinear_h3TraceZero_eq_zero
    (F : h3TraceZero →ₗ[ℝ] h3TraceZero →ₗ[ℝ] h3TraceZero →ₗ[ℝ] h3TraceZero)
    (h12 : ∀ x y z, F x y z = F y x z)
    (h23 : ∀ x y z, F x y z = F x z y)
    (hdiag : ∀ w, F w w w = 0) (x y z : h3TraceZero) : F x y z = 0 := by
  have h13 (a b c : h3TraceZero) : F a b c = F c b a := by rw [h12, h23, h12]
  have hpol : (6 : ℝ) • F x y z =
      F (x + y + z) (x + y + z) (x + y + z) -
      F (x + y) (x + y) (x + y) - F (x + z) (x + z) (x + z) -
      F (y + z) (y + z) (y + z) + F x x x + F y y y + F z z z := by
    simp only [map_add, LinearMap.add_apply]
    rw [h12 y x x, h23 x x y, h23 y y x, h12 y x y,
      h12 z x x, h23 x x z, h23 z z x, h12 z x z,
      h12 z y y, h23 y y z, h23 z z y, h12 z y z,
      h23 y z x, h12 y x z, h12 z x y, h23 x z y,
      h13 z y x]
    module
  rw [hdiag, hdiag, hdiag, hdiag, hdiag, hdiag, hdiag] at hpol
  simp only [sub_zero, add_zero] at hpol
  exact (smul_eq_zero.mp hpol).resolve_left (by norm_num)

/-- Decoupled 26D Jordan Identity 2 (polarized cubic Cayley–Hamilton on `h3TraceZero`):
`(1/3) P₀(x, y, z) = (1/6) (⟨y, z⟩ x + ⟨z, x⟩ y + ⟨x, y⟩ z)`. -/
theorem h3Proj0_cyclic_cube_polarized (x y z : h3TraceZero) :
    (1 / 3 : ℝ) • h3Proj0 (x.1 * (y.1 * z.1) + y.1 * (z.1 * x.1) + z.1 * (x.1 * y.1)) =
      (1 / 6 : ℝ) • (traceBilin y.1 z.1 • x + traceBilin z.1 x.1 • y + traceBilin x.1 y.1 • z) := by
  let qFun (a b c : h3TraceZero) : h3TraceZero :=
    (1 / 3 : ℝ) • h3Proj0 (a.1 * (b.1 * c.1) + b.1 * (c.1 * a.1) + c.1 * (a.1 * b.1)) -
      (1 / 6 : ℝ) • (traceBilin b.1 c.1 • a + traceBilin c.1 a.1 • b + traceBilin a.1 b.1 • c)
  have h3Proj0_val_add : ∀ u v : H3Zorn ℝ,
      ((h3Proj0 (u + v) : h3TraceZero) : H3Zorn ℝ) =
        (h3Proj0 u : H3Zorn ℝ) + (h3Proj0 v : H3Zorn ℝ) :=
    fun u v => congrArg Subtype.val (h3Proj0.map_add u v)
  have h3Proj0_val_smul : ∀ (r : ℝ) (u : H3Zorn ℝ),
      ((h3Proj0 (r • u) : h3TraceZero) : H3Zorn ℝ) = r • (h3Proj0 u : H3Zorn ℝ) :=
    fun r u => congrArg Subtype.val (h3Proj0.map_smul r u)
  let Q : h3TraceZero →ₗ[ℝ] h3TraceZero →ₗ[ℝ] h3TraceZero →ₗ[ℝ] h3TraceZero :=
    { toFun := fun a =>
        { toFun := fun b =>
            { toFun := fun c => qFun a b c
              map_add' := fun c₁ c₂ => by
                apply Subtype.ext
                simp only [qFun, Submodule.coe_add, Submodule.coe_sub, SetLike.val_smul,
                  mul_add, add_mul, traceBilin_add_right, traceBilin_add_left]
                have hlin : a.1 * (b.1 * c₁.1) + a.1 * (b.1 * c₂.1) +
                    (b.1 * (c₁.1 * a.1) + b.1 * (c₂.1 * a.1)) +
                    (c₁.1 * (a.1 * b.1) + c₂.1 * (a.1 * b.1)) =
                    (a.1 * (b.1 * c₁.1) + b.1 * (c₁.1 * a.1) + c₁.1 * (a.1 * b.1)) +
                    (a.1 * (b.1 * c₂.1) + b.1 * (c₂.1 * a.1) + c₂.1 * (a.1 * b.1)) := by abel
                rw [hlin, h3Proj0_val_add]
                module
              map_smul' := fun r c => by
                apply Subtype.ext
                simp only [qFun, Submodule.coe_add, Submodule.coe_sub, SetLike.val_smul,
                  RingHom.id_apply, mul_smul_comm, smul_mul_assoc,
                  traceBilin_smul_right, traceBilin_smul_left]
                have hlin : r • (a.1 * (b.1 * c.1)) + r • (b.1 * (c.1 * a.1)) +
                    r • (c.1 * (a.1 * b.1)) =
                    r • (a.1 * (b.1 * c.1) + b.1 * (c.1 * a.1) + c.1 * (a.1 * b.1)) := by module
                rw [hlin, h3Proj0_val_smul]
                module }
          map_add' := fun b₁ b₂ => by
            apply LinearMap.ext; intro c; apply Subtype.ext
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, qFun,
              Submodule.coe_add, Submodule.coe_sub, SetLike.val_smul,
              mul_add, add_mul, traceBilin_add_left, traceBilin_add_right]
            have hlin : a.1 * (b₁.1 * c.1) + a.1 * (b₂.1 * c.1) +
                (b₁.1 * (c.1 * a.1) + b₂.1 * (c.1 * a.1)) +
                (c.1 * (a.1 * b₁.1) + c.1 * (a.1 * b₂.1)) =
                (a.1 * (b₁.1 * c.1) + b₁.1 * (c.1 * a.1) + c.1 * (a.1 * b₁.1)) +
                (a.1 * (b₂.1 * c.1) + b₂.1 * (c.1 * a.1) + c.1 * (a.1 * b₂.1)) := by abel
            rw [hlin, h3Proj0_val_add]
            module
          map_smul' := fun r b => by
            apply LinearMap.ext; intro c; apply Subtype.ext
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, qFun,
              Submodule.coe_add, Submodule.coe_sub, SetLike.val_smul, RingHom.id_apply,
              mul_smul_comm, smul_mul_assoc, traceBilin_smul_left, traceBilin_smul_right]
            have hlin : r • (a.1 * (b.1 * c.1)) + r • (b.1 * (c.1 * a.1)) +
                r • (c.1 * (a.1 * b.1)) =
                r • (a.1 * (b.1 * c.1) + b.1 * (c.1 * a.1) + c.1 * (a.1 * b.1)) := by module
            rw [hlin, h3Proj0_val_smul]
            module }
      map_add' := fun a₁ a₂ => by
        apply LinearMap.ext; intro b; apply LinearMap.ext; intro c; apply Subtype.ext
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, qFun,
          Submodule.coe_add, Submodule.coe_sub, SetLike.val_smul,
          add_mul, mul_add, traceBilin_add_right, traceBilin_add_left]
        have hlin : a₁.1 * (b.1 * c.1) + a₂.1 * (b.1 * c.1) +
            (b.1 * (c.1 * a₁.1) + b.1 * (c.1 * a₂.1)) +
            (c.1 * (a₁.1 * b.1) + c.1 * (a₂.1 * b.1)) =
            (a₁.1 * (b.1 * c.1) + b.1 * (c.1 * a₁.1) + c.1 * (a₁.1 * b.1)) +
            (a₂.1 * (b.1 * c.1) + b.1 * (c.1 * a₂.1) + c.1 * (a₂.1 * b.1)) := by abel
        rw [hlin, h3Proj0_val_add]
        module
      map_smul' := fun r a => by
        apply LinearMap.ext; intro b; apply LinearMap.ext; intro c; apply Subtype.ext
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, qFun,
          Submodule.coe_add, Submodule.coe_sub, SetLike.val_smul, RingHom.id_apply,
          smul_mul_assoc, mul_smul_comm, traceBilin_smul_right, traceBilin_smul_left]
        have hlin : r • (a.1 * (b.1 * c.1)) + r • (b.1 * (c.1 * a.1)) +
            r • (c.1 * (a.1 * b.1)) =
            r • (a.1 * (b.1 * c.1) + b.1 * (c.1 * a.1) + c.1 * (a.1 * b.1)) := by module
        rw [hlin, h3Proj0_val_smul]
        module }
  have hQ12 (a b c : h3TraceZero) : Q a b c = Q b a c := by
    change qFun a b c = qFun b a c
    dsimp [qFun]
    have hP : a.1 * (b.1 * c.1) + b.1 * (c.1 * a.1) + c.1 * (a.1 * b.1) =
        b.1 * (a.1 * c.1) + a.1 * (c.1 * b.1) + c.1 * (b.1 * a.1) := by
      rw [mul_comm b.1 c.1, mul_comm c.1 a.1, mul_comm a.1 b.1]
      abel
    have hR : traceBilin b.1 c.1 • a + traceBilin c.1 a.1 • b + traceBilin a.1 b.1 • c =
        traceBilin a.1 c.1 • b + traceBilin c.1 b.1 • a + traceBilin b.1 a.1 • c := by
      rw [traceBilin_symm a.1 b.1, traceBilin_symm c.1 a.1, traceBilin_symm c.1 b.1]
      abel
    rw [hP, hR]
  have hQ23 (a b c : h3TraceZero) : Q a b c = Q a c b := by
    change qFun a b c = qFun a c b
    dsimp [qFun]
    have hP : a.1 * (b.1 * c.1) + b.1 * (c.1 * a.1) + c.1 * (a.1 * b.1) =
        a.1 * (c.1 * b.1) + c.1 * (b.1 * a.1) + b.1 * (a.1 * c.1) := by
      rw [mul_comm b.1 c.1, mul_comm c.1 a.1, mul_comm a.1 b.1]
      abel
    have hR : traceBilin b.1 c.1 • a + traceBilin c.1 a.1 • b + traceBilin a.1 b.1 • c =
        traceBilin c.1 b.1 • a + traceBilin b.1 a.1 • c + traceBilin a.1 c.1 • b := by
      rw [traceBilin_symm b.1 c.1, traceBilin_symm c.1 a.1, traceBilin_symm a.1 b.1]
      abel
    rw [hP, hR]
  have hQdiag (w : h3TraceZero) : Q w w w = 0 := by
    change qFun w w w = 0
    dsimp [qFun]
    have h1 : w.1 * (w.1 * w.1) + w.1 * (w.1 * w.1) + w.1 * (w.1 * w.1) =
        (3 : ℝ) • (w.1 * (w.1 * w.1)) := by module
    have h2 : traceBilin w.1 w.1 • w + traceBilin w.1 w.1 • w + traceBilin w.1 w.1 • w =
        (3 : ℝ) • (traceBilin w.1 w.1 • w) := by module
    rw [h1, h2, map_smul, h3Proj0_cube w]
    module
  have hz : Q x y z = 0 := symmetric_trilinear_h3TraceZero_eq_zero Q hQ12 hQ23 hQdiag x y z
  exact sub_eq_zero.mp hz

/-- Exact decomposition of `h3Mul0 x (h3Mul0 y z)` into `P₀`, `f4Act (f4Inner ...)`, and `traceBilin`. -/
theorem h3Mul0_assoc_decompose (x y z : h3TraceZero) :
    h3Mul0 x (h3Mul0 y z) =
      (1 / 6 : ℝ) • (traceBilin y.1 z.1 • x + traceBilin z.1 x.1 • y + traceBilin x.1 y.1 • z) +
      (1 / 3 : ℝ) • (f4Act (f4Inner x y) z - f4Act (f4Inner z x) y) -
      ((1 / 3 : ℝ) * traceBilin y.1 z.1) • x := by
  rw [← h3Proj0_cyclic_cube_polarized x y z]
  apply Subtype.ext
  have hdrop : (h3Mul0 x (h3Mul0 y z) : H3Zorn ℝ) =
      (h3Proj0 (x.1 * (y.1 * z.1)) : H3Zorn ℝ) - ((1 / 3 : ℝ) * traceBilin y.1 z.1) • x.1 := by
    rw [h3Mul0_eq_proj0 x (h3Mul0 y z)]
    simp only [h3Mul0_coe, mul_sub, mul_smul_comm, map_sub, map_smul, Submodule.coe_sub,
      SetLike.val_smul]
    have hx1 : x.1 * (1 : H3Zorn ℝ) = x.1 := candidateJordanMul_one_right x.1
    rw [hx1, h3Proj0_of_mem x]
  have hf4 : (f4Act (f4Inner x y) z - f4Act (f4Inner z x) y : H3Zorn ℝ) =
      (h3Proj0 ((3 : ℝ) • (x.1 * (y.1 * z.1)) -
        (x.1 * (y.1 * z.1) + y.1 * (z.1 * x.1) + z.1 * (x.1 * y.1))) : H3Zorn ℝ) := by
    have h_inner : ((f4Act (f4Inner x y) z - f4Act (f4Inner z x) y : h3TraceZero) : H3Zorn ℝ) =
        (3 : ℝ) • (x.1 * (y.1 * z.1)) -
          (x.1 * (y.1 * z.1) + y.1 * (z.1 * x.1) + z.1 * (x.1 * y.1)) := by
      simp only [Submodule.coe_sub, f4Act_coe, f4Inner, h3ZornJordanInnerDerivation_apply]
      rw [mul_comm x.1 z.1, mul_comm z.1 y.1]
      module
    have hproj := congrArg Subtype.val (h3Proj0_of_mem (f4Act (f4Inner x y) z - f4Act (f4Inner z x) y))
    simp only [Submodule.coe_sub] at hproj h_inner
    rw [← hproj, h_inner]
  rw [hdrop]
  simp only [Submodule.coe_sub, Submodule.coe_add, SetLike.val_smul]
  rw [hf4, map_sub, map_smul]
  simp only [Submodule.coe_sub, SetLike.val_smul]
  module

end JordanIdentities

/-! ## 4. `SplitE8Lie` Structure, Magic Square Bracket, and Jacobi Identity -/

section MagicSquareBracket

/-- The native 248-dimensional split `E₈` Lie algebra carrier
`G₂(2) ⊕ (Im(𝕆_s) ⊗ H₃(𝕆_s)⁰) ⊕ F₄(4)`, defined as a `structure` to avoid
`Prod` `LieRing` typeclass diamonds. -/
@[ext]
structure SplitE8Lie where
  g2 : G2DerivationCarrier
  mixed : MixedCarrier
  f4 : F4DerivationCarrier

instance : Zero SplitE8Lie := ⟨⟨0, 0, 0⟩⟩
instance : Add SplitE8Lie := ⟨fun x y => ⟨x.g2 + y.g2, x.mixed + y.mixed, x.f4 + y.f4⟩⟩
instance : Neg SplitE8Lie := ⟨fun x => ⟨-x.g2, -x.mixed, -x.f4⟩⟩
instance : Sub SplitE8Lie := ⟨fun x y => ⟨x.g2 - y.g2, x.mixed - y.mixed, x.f4 - y.f4⟩⟩
instance : SMul ℝ SplitE8Lie := ⟨fun r x => ⟨r • x.g2, r • x.mixed, r • x.f4⟩⟩

@[simp] theorem SplitE8Lie.zero_g2 : (0 : SplitE8Lie).g2 = 0 := rfl
@[simp] theorem SplitE8Lie.zero_mixed : (0 : SplitE8Lie).mixed = 0 := rfl
@[simp] theorem SplitE8Lie.zero_f4 : (0 : SplitE8Lie).f4 = 0 := rfl
@[simp] theorem SplitE8Lie.add_g2 (x y : SplitE8Lie) : (x + y).g2 = x.g2 + y.g2 := rfl
@[simp] theorem SplitE8Lie.add_mixed (x y : SplitE8Lie) : (x + y).mixed = x.mixed + y.mixed := rfl
@[simp] theorem SplitE8Lie.add_f4 (x y : SplitE8Lie) : (x + y).f4 = x.f4 + y.f4 := rfl
@[simp] theorem SplitE8Lie.neg_g2 (x : SplitE8Lie) : (-x).g2 = -x.g2 := rfl
@[simp] theorem SplitE8Lie.neg_mixed (x : SplitE8Lie) : (-x).mixed = -x.mixed := rfl
@[simp] theorem SplitE8Lie.neg_f4 (x : SplitE8Lie) : (-x).f4 = -x.f4 := rfl
@[simp] theorem SplitE8Lie.sub_g2 (x y : SplitE8Lie) : (x - y).g2 = x.g2 - y.g2 := rfl
@[simp] theorem SplitE8Lie.sub_mixed (x y : SplitE8Lie) : (x - y).mixed = x.mixed - y.mixed := rfl
@[simp] theorem SplitE8Lie.sub_f4 (x y : SplitE8Lie) : (x - y).f4 = x.f4 - y.f4 := rfl
@[simp] theorem SplitE8Lie.smul_g2 (r : ℝ) (x : SplitE8Lie) : (r • x).g2 = r • x.g2 := rfl
@[simp] theorem SplitE8Lie.smul_mixed (r : ℝ) (x : SplitE8Lie) : (r • x).mixed = r • x.mixed := rfl
@[simp] theorem SplitE8Lie.smul_f4 (r : ℝ) (x : SplitE8Lie) : (r • x).f4 = r • x.f4 := rfl

instance : AddCommGroup SplitE8Lie where
  add_assoc x y z := by ext <;> exact add_assoc _ _ _
  zero_add x := by ext <;> exact zero_add _
  add_zero x := by ext <;> exact add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel x := by ext <;> exact neg_add_cancel _
  add_comm x y := by ext <;> exact add_comm _ _
  sub_eq_add_neg x y := by ext <;> exact sub_eq_add_neg _ _

instance : Module ℝ SplitE8Lie where
  one_smul x := by ext <;> exact one_smul ℝ _
  mul_smul r s x := by ext <;> exact mul_smul r s _
  smul_zero r := by ext <;> exact smul_zero r
  smul_add r x y := by ext <;> exact smul_add r _ _
  add_smul r s x := by ext <;> exact add_smul r s _
  zero_smul x := by ext <;> exact zero_smul ℝ _

/-- Linear equivalence between `SplitE8Lie` and `NativeTitsCarrier`. -/
def splitE8LinearEquiv : SplitE8Lie ≃ₗ[ℝ] NativeTitsCarrier where
  toFun x := (x.g2, x.mixed, x.f4)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : Module.Finite ℝ SplitE8Lie :=
  let _free1 : Module.Free ℝ G2DerivationCarrier := Module.Free.of_divisionRing ℝ G2DerivationCarrier
  let _fin1 : Module.Finite ℝ G2DerivationCarrier :=
    Module.finite_of_finrank_pos (by rw [finrank_g2DerivationCarrier]; norm_num)
  let _free2 : Module.Free ℝ MixedCarrier := Module.Free.of_divisionRing ℝ MixedCarrier
  let _fin2 : Module.Finite ℝ MixedCarrier :=
    Module.finite_of_finrank_pos (by rw [finrank_mixedCarrier]; norm_num)
  let _free3 : Module.Free ℝ F4DerivationCarrier := Module.Free.of_divisionRing ℝ F4DerivationCarrier
  let _fin3 : Module.Finite ℝ F4DerivationCarrier :=
    Module.finite_of_finrank_pos (by rw [finrank_f4DerivationCarrier]; norm_num)
  Module.Finite.equiv splitE8LinearEquiv.symm

/-- `SplitE8Lie` has exact real dimension `248 = 14 + 182 + 52`. -/
theorem finrank_splitE8Lie : Module.finrank ℝ SplitE8Lie = 248 := by
  rw [splitE8LinearEquiv.finrank_eq, finrank_nativeTitsCarrier]

/-- Lift of `G₂` action on `MixedCarrier`: `D ⬝ (a ⊗ x) = (g2Act D a) ⊗ x`. -/
def g2MixedActLM : G2DerivationCarrier →ₗ[ℝ] MixedCarrier →ₗ[ℝ] MixedCarrier where
  toFun D := TensorProduct.map (g2ActLM D) LinearMap.id
  map_add' D₁ D₂ := by
    apply TensorProduct.ext'
    intro a x
    simp [TensorProduct.add_tmul]
  map_smul' r D := by
    apply TensorProduct.ext'
    intro a x
    simp [TensorProduct.smul_tmul]

@[simp] theorem g2MixedActLM_tmul (D : G2DerivationCarrier)
    (a : splitOctonionTraceZero) (x : h3TraceZero) :
    g2MixedActLM D (a ⊗ₜ[ℝ] x) = (g2Act D a) ⊗ₜ[ℝ] x := rfl

/-- Lift of `F₄` action on `MixedCarrier`: `D ⬝ (a ⊗ x) = a ⊗ (f4Act D x)`. -/
def f4MixedActLM : F4DerivationCarrier →ₗ[ℝ] MixedCarrier →ₗ[ℝ] MixedCarrier where
  toFun D := TensorProduct.map LinearMap.id (f4ActLM D)
  map_add' D₁ D₂ := by
    apply TensorProduct.ext'
    intro a x
    simp [TensorProduct.tmul_add]
  map_smul' r D := by
    apply TensorProduct.ext'
    intro a x
    simp [TensorProduct.smul_tmul']

@[simp] theorem f4MixedActLM_tmul (D : F4DerivationCarrier)
    (a : splitOctonionTraceZero) (x : h3TraceZero) :
    f4MixedActLM D (a ⊗ₜ[ℝ] x) = a ⊗ₜ[ℝ] (f4Act D x) := rfl

private def mixedBilLift {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : splitOctonionTraceZero →ₗ[ℝ] h3TraceZero →ₗ[ℝ]
      splitOctonionTraceZero →ₗ[ℝ] h3TraceZero →ₗ[ℝ] E) :
    MixedCarrier →ₗ[ℝ] MixedCarrier →ₗ[ℝ] E :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun x => TensorProduct.lift (F a x)
          map_add' := fun x₁ x₂ => by
            apply TensorProduct.ext'; intro b y; simp
          map_smul' := fun r x => by
            apply TensorProduct.ext'; intro b y; simp }
      map_add' := fun a₁ a₂ => by
        apply LinearMap.ext; intro x; apply TensorProduct.ext'; intro b y; simp
      map_smul' := fun r a => by
        apply LinearMap.ext; intro x; apply TensorProduct.ext'; intro b y; simp }

@[simp] private theorem mixedBilLift_tmul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : splitOctonionTraceZero →ₗ[ℝ] h3TraceZero →ₗ[ℝ]
      splitOctonionTraceZero →ₗ[ℝ] h3TraceZero →ₗ[ℝ] E)
    (a b : splitOctonionTraceZero) (x y : h3TraceZero) :
    mixedBilLift F (a ⊗ₜ[ℝ] x) (b ⊗ₜ[ℝ] y) = F a x b y := by
  simp [mixedBilLift]

/-- Mixed-to-`G₂` Magic Square bracket component:
`a ⊗ x, b ⊗ y ↦ (1/3) * traceBilin x y • g2Inner a b`. -/
def mixedToG2LM : MixedCarrier →ₗ[ℝ] MixedCarrier →ₗ[ℝ] G2DerivationCarrier :=
  mixedBilLift
    { toFun := fun a =>
        { toFun := fun x =>
            { toFun := fun b =>
                { toFun := fun y => ((1 / 3 : ℝ) * traceBilin x.1 y.1) • g2Inner a b
                  map_add' := fun y₁ y₂ => by
                    simp only [Submodule.coe_add, traceBilin_add_right, mul_add, add_smul]
                  map_smul' := fun r y => by
                    simp only [SetLike.val_smul, traceBilin_smul_right, RingHom.id_apply]
                    module }
              map_add' := fun b₁ b₂ => by
                apply LinearMap.ext; intro y
                simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
                  ← g2InnerLM_apply, map_add, smul_add]
              map_smul' := fun r b => by
                apply LinearMap.ext; intro y
                simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
                  ← g2InnerLM_apply, map_smul, RingHom.id_apply]
                module }
          map_add' := fun x₁ x₂ => by
            apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
              Submodule.coe_add, traceBilin_add_left, mul_add, add_smul]
          map_smul' := fun r x => by
            apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
            simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
              SetLike.val_smul, traceBilin_smul_left, RingHom.id_apply]
            module }
      map_add' := fun a₁ a₂ => by
        apply LinearMap.ext; intro x; apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
          ← g2InnerLM_apply, map_add, smul_add]
      map_smul' := fun r a => by
        apply LinearMap.ext; intro x; apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
          ← g2InnerLM_apply, map_smul, RingHom.id_apply]
        module }

@[simp] theorem mixedToG2LM_tmul (a b : splitOctonionTraceZero) (x y : h3TraceZero) :
    mixedToG2LM (a ⊗ₜ[ℝ] x) (b ⊗ₜ[ℝ] y) =
      ((1 / 3 : ℝ) * traceBilin x.1 y.1) • g2Inner a b := by
  simp [mixedToG2LM]

/-- Mixed-to-`F₄` Magic Square bracket component:
`a ⊗ x, b ⊗ y ↦ (-2) * zornBilin a b • f4Inner x y`. -/
def mixedToF4LM : MixedCarrier →ₗ[ℝ] MixedCarrier →ₗ[ℝ] F4DerivationCarrier :=
  mixedBilLift
    { toFun := fun a =>
        { toFun := fun x =>
            { toFun := fun b =>
                { toFun := fun y => ((-2 : ℝ) * zornBilin a.1 b.1) • f4Inner x y
                  map_add' := fun y₁ y₂ => by
                    simp only [← f4InnerLM_apply, map_add, smul_add]
                  map_smul' := fun r y => by
                    simp only [← f4InnerLM_apply, map_smul, RingHom.id_apply]
                    module }
              map_add' := fun b₁ b₂ => by
                apply LinearMap.ext; intro y
                change ((-2 : ℝ) * zornBilin a.1 (b₁ + b₂).1) • f4Inner x y =
                  ((-2 : ℝ) * zornBilin a.1 b₁.1) • f4Inner x y +
                    ((-2 : ℝ) * zornBilin a.1 b₂.1) • f4Inner x y
                simp only [Submodule.coe_add, zornBilin_add_right, mul_add, add_smul]
              map_smul' := fun r b => by
                apply LinearMap.ext; intro y
                change ((-2 : ℝ) * zornBilin a.1 (r • b).1) • f4Inner x y =
                  r • (((-2 : ℝ) * zornBilin a.1 b.1) • f4Inner x y)
                simp only [SetLike.val_smul, zornBilin_smul_right]
                rw [mul_left_comm, mul_smul] }
          map_add' := fun x₁ x₂ => by
            apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
            simp only [LinearMap.add_apply, ← f4InnerLM_apply, map_add, smul_add]
            rfl
          map_smul' := fun r x => by
            apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
            change ((-2 : ℝ) * zornBilin a.1 b.1) • f4Inner (r • x) y =
              r • (((-2 : ℝ) * zornBilin a.1 b.1) • f4Inner x y)
            simp only [← f4InnerLM_apply, map_smul, LinearMap.smul_apply]
            rw [smul_comm] }
      map_add' := fun a₁ a₂ => by
        apply LinearMap.ext; intro x; apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
        change ((-2 : ℝ) * zornBilin (a₁ + a₂).1 b.1) • f4Inner x y =
          ((-2 : ℝ) * zornBilin a₁.1 b.1) • f4Inner x y +
            ((-2 : ℝ) * zornBilin a₂.1 b.1) • f4Inner x y
        simp only [Submodule.coe_add, zornBilin_add_left, mul_add, add_smul]
      map_smul' := fun r a => by
        apply LinearMap.ext; intro x; apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
        change ((-2 : ℝ) * zornBilin (r • a).1 b.1) • f4Inner x y =
          r • (((-2 : ℝ) * zornBilin a.1 b.1) • f4Inner x y)
        simp only [SetLike.val_smul, zornBilin_smul_left]
        rw [mul_left_comm, mul_smul] }

@[simp] theorem mixedToF4LM_tmul (a b : splitOctonionTraceZero) (x y : h3TraceZero) :
    mixedToF4LM (a ⊗ₜ[ℝ] x) (b ⊗ₜ[ℝ] y) =
      ((-2 : ℝ) * zornBilin a.1 b.1) • f4Inner x y := by
  simp [mixedToF4LM]

/-- Mixed-to-Mixed Magic Square bracket component:
`a ⊗ x, b ⊗ y ↦ (zornComm0 a b) ⊗ (h3Mul0 x y)`. -/
def mixedToMixedLM : MixedCarrier →ₗ[ℝ] MixedCarrier →ₗ[ℝ] MixedCarrier :=
  mixedBilLift
    { toFun := fun a =>
        { toFun := fun x =>
            { toFun := fun b =>
                { toFun := fun y => (zornComm0 a b) ⊗ₜ[ℝ] (h3Mul0 x y)
                  map_add' := fun y₁ y₂ => by
                    simp only [← h3Mul0LM_apply, map_add, TensorProduct.tmul_add]
                  map_smul' := fun r y => by
                    simp only [← h3Mul0LM_apply, map_smul, TensorProduct.tmul_smul,
                      RingHom.id_apply] }
              map_add' := fun b₁ b₂ => by
                apply LinearMap.ext; intro y
                change (zornComm0 a (b₁ + b₂)) ⊗ₜ[ℝ] (h3Mul0 x y) =
                  (zornComm0 a b₁) ⊗ₜ[ℝ] (h3Mul0 x y) + (zornComm0 a b₂) ⊗ₜ[ℝ] (h3Mul0 x y)
                simp only [← zornComm0LM_apply, map_add, TensorProduct.add_tmul]
              map_smul' := fun r b => by
                apply LinearMap.ext; intro y
                change (zornComm0 a (r • b)) ⊗ₜ[ℝ] (h3Mul0 x y) =
                  r • ((zornComm0 a b) ⊗ₜ[ℝ] (h3Mul0 x y))
                simp only [← zornComm0LM_apply, map_smul, TensorProduct.smul_tmul,
                  TensorProduct.tmul_smul] }
          map_add' := fun x₁ x₂ => by
            apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
            simp only [LinearMap.add_apply, ← h3Mul0LM_apply, map_add, TensorProduct.tmul_add]
            rfl
          map_smul' := fun r x => by
            apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
            change (zornComm0 a b) ⊗ₜ[ℝ] (h3Mul0 (r • x) y) =
              r • ((zornComm0 a b) ⊗ₜ[ℝ] (h3Mul0 x y))
            simp only [← h3Mul0LM_apply, map_smul, LinearMap.smul_apply, TensorProduct.tmul_smul] }
      map_add' := fun a₁ a₂ => by
        apply LinearMap.ext; intro x; apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
        change (zornComm0 (a₁ + a₂) b) ⊗ₜ[ℝ] (h3Mul0 x y) =
          (zornComm0 a₁ b) ⊗ₜ[ℝ] (h3Mul0 x y) + (zornComm0 a₂ b) ⊗ₜ[ℝ] (h3Mul0 x y)
        simp only [← zornComm0LM_apply, map_add, LinearMap.add_apply, TensorProduct.add_tmul]
      map_smul' := fun r a => by
        apply LinearMap.ext; intro x; apply LinearMap.ext; intro b; apply LinearMap.ext; intro y
        change (zornComm0 (r • a) b) ⊗ₜ[ℝ] (h3Mul0 x y) =
          r • ((zornComm0 a b) ⊗ₜ[ℝ] (h3Mul0 x y))
        simp only [← zornComm0LM_apply, map_smul, LinearMap.smul_apply,
          TensorProduct.smul_tmul, TensorProduct.tmul_smul] }

@[simp] theorem mixedToMixedLM_tmul (a b : splitOctonionTraceZero) (x y : h3TraceZero) :
    mixedToMixedLM (a ⊗ₜ[ℝ] x) (b ⊗ₜ[ℝ] y) = (zornComm0 a b) ⊗ₜ[ℝ] (h3Mul0 x y) := by
  simp only [mixedToMixedLM, mixedBilLift_tmul]
  rfl

/-- Full bilinear Magic Square bracket `SplitE8Lie →ₗ[ℝ] SplitE8Lie →ₗ[ℝ] SplitE8Lie`. -/
def magicBracketLM : SplitE8Lie →ₗ[ℝ] SplitE8Lie →ₗ[ℝ] SplitE8Lie where
  toFun X :=
    { toFun := fun Y =>
        { g2 := ⁅X.g2, Y.g2⁆ + mixedToG2LM X.mixed Y.mixed
          mixed := g2MixedActLM X.g2 Y.mixed - g2MixedActLM Y.g2 X.mixed +
            f4MixedActLM X.f4 Y.mixed - f4MixedActLM Y.f4 X.mixed +
            mixedToMixedLM X.mixed Y.mixed
          f4 := ⁅X.f4, Y.f4⁆ + mixedToF4LM X.mixed Y.mixed }
      map_add' Y₁ Y₂ := by
        apply SplitE8Lie.ext <;>
          simp only [SplitE8Lie.add_g2, SplitE8Lie.add_mixed, SplitE8Lie.add_f4,
            lie_add, map_add, LinearMap.add_apply] <;> abel
      map_smul' r Y := by
        apply SplitE8Lie.ext <;>
          simp only [SplitE8Lie.smul_g2, SplitE8Lie.smul_mixed, SplitE8Lie.smul_f4,
            lie_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply] <;> module }
  map_add' X₁ X₂ := by
    apply LinearMap.ext; intro Y; apply SplitE8Lie.ext <;>
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
        SplitE8Lie.add_g2, SplitE8Lie.add_mixed, SplitE8Lie.add_f4,
        add_lie, map_add] <;> abel
  map_smul' r X := by
    apply LinearMap.ext; intro Y; apply SplitE8Lie.ext <;>
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
        SplitE8Lie.smul_g2, SplitE8Lie.smul_mixed, SplitE8Lie.smul_f4,
        smul_lie, map_smul, RingHom.id_apply] <;> module

private theorem mixedToG2LM_antisymm (m₁ m₂ : MixedCarrier) :
    mixedToG2LM m₂ m₁ = -mixedToG2LM m₁ m₂ := by
  induction m₁ using TensorProduct.inductionOn with
  | add u₁ u₂ ih₁ ih₂ => simp [ih₁, ih₂]; abel
  | tmul a x =>
    induction m₂ using TensorProduct.inductionOn with
    | add v₁ v₂ ih₁ ih₂ => simp [ih₁, ih₂]; abel
    | tmul b y =>
      simp only [mixedToG2LM_tmul, traceBilin_symm y.1 x.1, g2Inner_antisymm a b, smul_neg]

private theorem mixedToF4LM_antisymm (m₁ m₂ : MixedCarrier) :
    mixedToF4LM m₂ m₁ = -mixedToF4LM m₁ m₂ := by
  induction m₁ using TensorProduct.inductionOn with
  | add u₁ u₂ ih₁ ih₂ => simp [ih₁, ih₂]; abel
  | tmul a x =>
    induction m₂ using TensorProduct.inductionOn with
    | add v₁ v₂ ih₁ ih₂ => simp [ih₁, ih₂]; abel
    | tmul b y =>
      simp only [mixedToF4LM_tmul, zornBilin_symm b.1 a.1, f4Inner_antisymm x y, smul_neg]

private theorem mixedToMixedLM_antisymm (m₁ m₂ : MixedCarrier) :
    mixedToMixedLM m₂ m₁ = -mixedToMixedLM m₁ m₂ := by
  induction m₁ using TensorProduct.inductionOn with
  | add u₁ u₂ ih₁ ih₂ => simp [ih₁, ih₂]; abel
  | tmul a x =>
    induction m₂ using TensorProduct.inductionOn with
    | add v₁ v₂ ih₁ ih₂ => simp [ih₁, ih₂]; abel
    | tmul b y =>
      simp only [mixedToMixedLM_tmul, zornComm0_antisymm a b, h3Mul0_comm y x,
        TensorProduct.neg_tmul]

theorem magicBracketLM_antisymm (X Y : SplitE8Lie) :
    magicBracketLM Y X = -magicBracketLM X Y := by
  apply SplitE8Lie.ext
  · simp only [magicBracketLM, LinearMap.coe_mk, AddHom.coe_mk, SplitE8Lie.neg_g2,
      mixedToG2LM_antisymm X.mixed Y.mixed]
    rw [← lie_skew X.g2 Y.g2]
    abel
  · simp only [magicBracketLM, LinearMap.coe_mk, AddHom.coe_mk, SplitE8Lie.neg_mixed,
      mixedToMixedLM_antisymm X.mixed Y.mixed]
    abel
  · simp only [magicBracketLM, LinearMap.coe_mk, AddHom.coe_mk, SplitE8Lie.neg_f4,
      mixedToF4LM_antisymm X.mixed Y.mixed]
    rw [← lie_skew X.f4 Y.f4]
    abel

theorem magicBracketLM_self (X : SplitE8Lie) : magicBracketLM X X = 0 := by
  have h := magicBracketLM_antisymm X X
  have h2 : (2 : ℝ) • magicBracketLM X X = 0 := by
    rw [two_smul]
    nth_rw 2 [h]
    exact add_neg_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-! ### Embeddings and Projections -/

/-- Canonical embedding `G₂(2) →ₗ[ℝ] SplitE8Lie`. -/
def embedG2LM : G2DerivationCarrier →ₗ[ℝ] SplitE8Lie where
  toFun D := ⟨D, 0, 0⟩
  map_add' _ _ := by apply SplitE8Lie.ext <;> simp
  map_smul' _ _ := by apply SplitE8Lie.ext <;> simp

@[simp] private theorem embedG2LM_g2 (D : G2DerivationCarrier) : (embedG2LM D).g2 = D := rfl
@[simp] private theorem embedG2LM_mixed (D : G2DerivationCarrier) : (embedG2LM D).mixed = 0 := rfl
@[simp] private theorem embedG2LM_f4 (D : G2DerivationCarrier) : (embedG2LM D).f4 = 0 := rfl

/-- Canonical embedding `MixedCarrier →ₗ[ℝ] SplitE8Lie`. -/
def embedMixed : MixedCarrier →ₗ[ℝ] SplitE8Lie where
  toFun m := ⟨0, m, 0⟩
  map_add' _ _ := by apply SplitE8Lie.ext <;> simp
  map_smul' _ _ := by apply SplitE8Lie.ext <;> simp

@[simp] private theorem embedMixed_g2 (m : MixedCarrier) : (embedMixed m).g2 = 0 := rfl
@[simp] private theorem embedMixed_mixed (m : MixedCarrier) : (embedMixed m).mixed = m := rfl
@[simp] private theorem embedMixed_f4 (m : MixedCarrier) : (embedMixed m).f4 = 0 := rfl

/-- Canonical embedding `F₄(4) →ₗ[ℝ] SplitE8Lie`. -/
def embedF4LM : F4DerivationCarrier →ₗ[ℝ] SplitE8Lie where
  toFun D := ⟨0, 0, D⟩
  map_add' _ _ := by apply SplitE8Lie.ext <;> simp
  map_smul' _ _ := by apply SplitE8Lie.ext <;> simp

@[simp] private theorem embedF4LM_g2 (D : F4DerivationCarrier) : (embedF4LM D).g2 = 0 := rfl
@[simp] private theorem embedF4LM_mixed (D : F4DerivationCarrier) : (embedF4LM D).mixed = 0 := rfl
@[simp] private theorem embedF4LM_f4 (D : F4DerivationCarrier) : (embedF4LM D).f4 = D := rfl

/-- Bilinear pure-tensor embedding `a ↦ x ↦ embedMixed (a ⊗ₜ[ℝ] x)`. -/
def embedTensor : splitOctonionTraceZero →ₗ[ℝ] h3TraceZero →ₗ[ℝ] SplitE8Lie :=
  LinearMap.mk₂ ℝ (fun a x => embedMixed (a ⊗ₜ[ℝ] x))
    (fun a₁ a₂ x => by simp [TensorProduct.add_tmul])
    (fun r a x => by simp [TensorProduct.smul_tmul])
    (fun a x₁ x₂ => by simp [TensorProduct.tmul_add])
    (fun r a x => by simp [TensorProduct.tmul_smul])

@[simp] theorem embedTensor_apply (a : splitOctonionTraceZero) (x : h3TraceZero) :
    embedTensor a x = embedMixed (a ⊗ₜ[ℝ] x) := rfl

/-- Field projection `SplitE8Lie →ₗ[ℝ] G2DerivationCarrier`. -/
def projG2 : SplitE8Lie →ₗ[ℝ] G2DerivationCarrier where
  toFun X := X.g2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Field projection `SplitE8Lie →ₗ[ℝ] MixedCarrier`. -/
def projMixed : SplitE8Lie →ₗ[ℝ] MixedCarrier where
  toFun X := X.mixed
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Field projection `SplitE8Lie →ₗ[ℝ] F4DerivationCarrier`. -/
def projF4 : SplitE8Lie →ₗ[ℝ] F4DerivationCarrier where
  toFun X := X.f4
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Idempotent projector onto the `G₂` summand in `SplitE8Lie`. -/
def projG2Sub : SplitE8Lie →ₗ[ℝ] SplitE8Lie := embedG2LM.comp projG2

/-- Idempotent projector onto the `Mixed` summand in `SplitE8Lie`. -/
def projMixedSub : SplitE8Lie →ₗ[ℝ] SplitE8Lie := embedMixed.comp projMixed

/-- Idempotent projector onto the `F₄` summand in `SplitE8Lie`. -/
def projF4Sub : SplitE8Lie →ₗ[ℝ] SplitE8Lie := embedF4LM.comp projF4

inductive SplitE8Grade : Type
  | g2 | mixed | f4
  deriving DecidableEq, Inhabited

instance : Fintype SplitE8Grade where
  elems := {.g2, .mixed, .f4}
  complete g := by cases g <;> simp

def gradeProj : SplitE8Grade → SplitE8Lie →ₗ[ℝ] SplitE8Lie
  | .g2 => projG2Sub
  | .mixed => projMixedSub
  | .f4 => projF4Sub

theorem gradeProj_sum (X : SplitE8Lie) : (∑ i : SplitE8Grade, gradeProj i X) = X := by
  have huniv : (Finset.univ : Finset SplitE8Grade) = {.g2, .mixed, .f4} := by
    ext g; cases g <;> simp
  rw [huniv]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq,
    not_false_eq_true, or_self, Finset.sum_singleton, gradeProj, projG2Sub, projMixedSub, projF4Sub,
    LinearMap.comp_apply]
  apply SplitE8Lie.ext <;> simp [embedG2LM, embedMixed, embedF4LM, projG2, projMixed, projF4]

/-! ### Graded Bracket Identities and Jacobi Proof -/

private theorem magicBracket_g2_g2 (D₁ D₂ : G2DerivationCarrier) :
    magicBracketLM (embedG2LM D₁) (embedG2LM D₂) = embedG2LM ⁅D₁, D₂⁆ := by
  apply SplitE8Lie.ext <;> simp [magicBracketLM, embedG2LM]

private theorem magicBracket_f4_f4 (D₁ D₂ : F4DerivationCarrier) :
    magicBracketLM (embedF4LM D₁) (embedF4LM D₂) = embedF4LM ⁅D₁, D₂⁆ := by
  apply SplitE8Lie.ext <;> simp [magicBracketLM, embedF4LM]

private theorem magicBracket_g2_f4 (D₁ : G2DerivationCarrier) (D₂ : F4DerivationCarrier) :
    magicBracketLM (embedG2LM D₁) (embedF4LM D₂) = 0 := by
  apply SplitE8Lie.ext <;> simp [magicBracketLM, embedG2LM, embedF4LM]

private theorem magicBracket_f4_g2 (D₁ : F4DerivationCarrier) (D₂ : G2DerivationCarrier) :
    magicBracketLM (embedF4LM D₁) (embedG2LM D₂) = 0 := by
  apply SplitE8Lie.ext <;> simp [magicBracketLM, embedG2LM, embedF4LM]

private theorem magicBracket_g2_mixed (D : G2DerivationCarrier) (m : MixedCarrier) :
    magicBracketLM (embedG2LM D) (embedMixed m) = embedMixed (g2MixedActLM D m) := by
  apply SplitE8Lie.ext <;> simp [magicBracketLM, embedG2LM, embedMixed]

private theorem magicBracket_mixed_g2 (m : MixedCarrier) (D : G2DerivationCarrier) :
    magicBracketLM (embedMixed m) (embedG2LM D) = embedMixed (-g2MixedActLM D m) := by
  rw [magicBracketLM_antisymm, magicBracket_g2_mixed, map_neg]

private theorem magicBracket_f4_mixed (D : F4DerivationCarrier) (m : MixedCarrier) :
    magicBracketLM (embedF4LM D) (embedMixed m) = embedMixed (f4MixedActLM D m) := by
  apply SplitE8Lie.ext <;> simp [magicBracketLM, embedF4LM, embedMixed]

private theorem magicBracket_mixed_f4 (m : MixedCarrier) (D : F4DerivationCarrier) :
    magicBracketLM (embedMixed m) (embedF4LM D) = embedMixed (-f4MixedActLM D m) := by
  rw [magicBracketLM_antisymm, magicBracket_f4_mixed, map_neg]

private theorem magicBracket_mixed_mixed (m₁ m₂ : MixedCarrier) :
    magicBracketLM (embedMixed m₁) (embedMixed m₂) =
      embedG2LM (mixedToG2LM m₁ m₂) + embedMixed (mixedToMixedLM m₁ m₂) +
        embedF4LM (mixedToF4LM m₁ m₂) := by
  apply SplitE8Lie.ext <;> simp [magicBracketLM, embedG2LM, embedMixed, embedF4LM]

private theorem defect_swap₁₂ (x y z : SplitE8Lie) :
    leibnizDefect magicBracketLM y x z = -leibnizDefect magicBracketLM x y z := by
  simp only [leibnizDefect]
  rw [magicBracketLM_antisymm x y, map_neg, LinearMap.neg_apply]
  abel

private theorem defect_swap₂₃ (x y z : SplitE8Lie) :
    leibnizDefect magicBracketLM x z y = -leibnizDefect magicBracketLM x y z := by
  simp only [leibnizDefect]
  rw [magicBracketLM_antisymm y z, magicBracketLM_antisymm (magicBracketLM x z) y, map_neg,
    magicBracketLM_antisymm z (magicBracketLM x y)]
  abel

private theorem defect_cycle (x y z : SplitE8Lie) :
    leibnizDefect magicBracketLM y z x = leibnizDefect magicBracketLM x y z := by
  rw [defect_swap₂₃ y x z, defect_swap₁₂ x y z, neg_neg]

private theorem defect_g2_g2_g2 (D₁ D₂ D₃ : G2DerivationCarrier) :
    leibnizDefect magicBracketLM (embedG2LM D₁) (embedG2LM D₂) (embedG2LM D₃) = 0 := by
  have hz : ⁅D₁, ⁅D₂, D₃⁆⁆ - ⁅⁅D₁, D₂⁆, D₃⁆ - ⁅D₂, ⁅D₁, D₃⁆⁆ = 0 := by
    rw [leibniz_lie D₁ D₂ D₃]; abel
  rw [leibnizDefect, magicBracket_g2_g2, magicBracket_g2_g2, magicBracket_g2_g2,
    magicBracket_g2_g2, magicBracket_g2_g2, magicBracket_g2_g2,
    ← map_sub, ← map_sub]
  exact (congrArg embedG2LM hz).trans (map_zero embedG2LM)

private theorem defect_f4_f4_f4 (D₁ D₂ D₃ : F4DerivationCarrier) :
    leibnizDefect magicBracketLM (embedF4LM D₁) (embedF4LM D₂) (embedF4LM D₃) = 0 := by
  have hz : ⁅D₁, ⁅D₂, D₃⁆⁆ - ⁅⁅D₁, D₂⁆, D₃⁆ - ⁅D₂, ⁅D₁, D₃⁆⁆ = 0 := by
    rw [leibniz_lie D₁ D₂ D₃]; abel
  rw [leibnizDefect, magicBracket_f4_f4, magicBracket_f4_f4, magicBracket_f4_f4,
    magicBracket_f4_f4, magicBracket_f4_f4, magicBracket_f4_f4,
    ← map_sub, ← map_sub, hz, map_zero]

private theorem defect_g2_g2_f4 (D₁ D₂ : G2DerivationCarrier) (D₃ : F4DerivationCarrier) :
    leibnizDefect magicBracketLM (embedG2LM D₁) (embedG2LM D₂) (embedF4LM D₃) = 0 := by
  simp only [leibnizDefect, magicBracket_g2_f4, magicBracket_g2_g2, map_zero, sub_self]

private theorem defect_g2_f4_f4 (D₁ : G2DerivationCarrier) (D₂ D₃ : F4DerivationCarrier) :
    leibnizDefect magicBracketLM (embedG2LM D₁) (embedF4LM D₂) (embedF4LM D₃) = 0 := by
  simp only [leibnizDefect, magicBracket_g2_f4, magicBracket_f4_f4, map_zero, LinearMap.zero_apply,
    sub_self]

private theorem defect_g2_g2_mixed (D₁ D₂ : G2DerivationCarrier) (m : MixedCarrier) :
    leibnizDefect magicBracketLM (embedG2LM D₁) (embedG2LM D₂) (embedMixed m) = 0 := by
  induction m using TensorProduct.inductionOn with
  | add m₁ m₂ ih₁ ih₂ =>
    rw [map_add, leibnizDefect_add_right, ih₁, ih₂, add_zero]
  | tmul a x =>
    simp only [leibnizDefect, magicBracket_g2_mixed, magicBracket_g2_g2, g2MixedActLM_tmul,
      g2Act_lie]
    apply SplitE8Lie.ext
    · simp only [SplitE8Lie.sub_g2, SplitE8Lie.zero_g2, embedMixed_g2]; abel
    · simp only [SplitE8Lie.sub_mixed, SplitE8Lie.zero_mixed, embedMixed_mixed,
        TensorProduct.sub_tmul]; abel
    · simp only [SplitE8Lie.sub_f4, SplitE8Lie.zero_f4, embedMixed_f4]; abel

private theorem defect_f4_f4_mixed (D₁ D₂ : F4DerivationCarrier) (m : MixedCarrier) :
    leibnizDefect magicBracketLM (embedF4LM D₁) (embedF4LM D₂) (embedMixed m) = 0 := by
  induction m using TensorProduct.inductionOn with
  | add m₁ m₂ ih₁ ih₂ =>
    rw [map_add, leibnizDefect_add_right, ih₁, ih₂, add_zero]
  | tmul a x =>
    simp only [leibnizDefect, magicBracket_f4_mixed, magicBracket_f4_f4, f4MixedActLM_tmul,
      f4Act_lie]
    apply SplitE8Lie.ext
    · simp only [SplitE8Lie.sub_g2, SplitE8Lie.zero_g2, embedMixed_g2]; abel
    · simp only [SplitE8Lie.sub_mixed, SplitE8Lie.zero_mixed, embedMixed_mixed,
        TensorProduct.tmul_sub]; abel
    · simp only [SplitE8Lie.sub_f4, SplitE8Lie.zero_f4, embedMixed_f4]; abel

private theorem defect_g2_f4_mixed (D₁ : G2DerivationCarrier) (D₂ : F4DerivationCarrier)
    (m : MixedCarrier) :
    leibnizDefect magicBracketLM (embedG2LM D₁) (embedF4LM D₂) (embedMixed m) = 0 := by
  induction m using TensorProduct.inductionOn with
  | add m₁ m₂ ih₁ ih₂ =>
    rw [map_add, leibnizDefect_add_right, ih₁, ih₂, add_zero]
  | tmul a x =>
    simp only [leibnizDefect, magicBracket_f4_mixed, magicBracket_g2_f4, magicBracket_g2_mixed,
      map_zero, LinearMap.zero_apply, sub_zero, g2MixedActLM_tmul, f4MixedActLM_tmul]
    exact sub_self _

private theorem defect_g2_mixed_mixed (D : G2DerivationCarrier) (m₁ m₂ : MixedCarrier) :
    leibnizDefect magicBracketLM (embedG2LM D) (embedMixed m₁) (embedMixed m₂) = 0 := by
  induction m₁ using TensorProduct.inductionOn with
  | add u₁ u₂ ih₁ ih₂ =>
    rw [map_add, leibnizDefect_add_mid, ih₁, ih₂, add_zero]
  | tmul a x =>
    induction m₂ using TensorProduct.inductionOn with
    | add v₁ v₂ ih₁ ih₂ =>
      rw [map_add, leibnizDefect_add_right, ih₁, ih₂, add_zero]
    | tmul b y =>
      simp only [leibnizDefect, magicBracket_mixed_mixed, magicBracket_g2_mixed,
        g2MixedActLM_tmul, map_add, magicBracket_g2_g2, magicBracket_g2_f4,
        mixedToG2LM_tmul, mixedToMixedLM_tmul, mixedToF4LM_tmul, add_zero]
      apply SplitE8Lie.ext
      · simp only [SplitE8Lie.sub_g2, SplitE8Lie.add_g2, SplitE8Lie.zero_g2,
          embedG2LM_g2, embedMixed_g2, embedF4LM_g2, lie_smul, g2_covariant, smul_add]
        abel
      · simp only [SplitE8Lie.sub_mixed, SplitE8Lie.add_mixed, SplitE8Lie.zero_mixed,
          embedG2LM_mixed, embedMixed_mixed, embedF4LM_mixed, g2Act_zornComm0,
          TensorProduct.add_tmul]
        abel
      · simp only [SplitE8Lie.sub_f4, SplitE8Lie.add_f4, SplitE8Lie.zero_f4,
          embedG2LM_f4, embedMixed_f4, embedF4LM_f4]
        have hskew := zornBilin_deriv_skew D a b
        have hsum : ((-2 : ℝ) * zornBilin (g2Act D a).1 b.1) • f4Inner x y +
            ((-2 : ℝ) * zornBilin a.1 (g2Act D b).1) • f4Inner x y = 0 := by
          rw [← add_smul]
          have hc : (-2 : ℝ) * zornBilin (g2Act D a).1 b.1 +
              (-2 : ℝ) * zornBilin a.1 (g2Act D b).1 = 0 := by
            simp only [g2Act_coe]; linarith
          rw [hc, zero_smul]
        have hre :
            (0 + 0 - (0 + 0 + ((-2 : ℝ) * zornBilin (g2Act D a).1 b.1) • f4Inner x y) -
              (0 + 0 + ((-2 : ℝ) * zornBilin a.1 (g2Act D b).1) • f4Inner x y)) =
            -(((-2 : ℝ) * zornBilin (g2Act D a).1 b.1) • f4Inner x y +
              ((-2 : ℝ) * zornBilin a.1 (g2Act D b).1) • f4Inner x y) := by abel
        rw [hre, hsum, neg_zero]

private theorem defect_f4_mixed_mixed (D : F4DerivationCarrier) (m₁ m₂ : MixedCarrier) :
    leibnizDefect magicBracketLM (embedF4LM D) (embedMixed m₁) (embedMixed m₂) = 0 := by
  induction m₁ using TensorProduct.inductionOn with
  | add u₁ u₂ ih₁ ih₂ =>
    rw [map_add, leibnizDefect_add_mid, ih₁, ih₂, add_zero]
  | tmul a x =>
    induction m₂ using TensorProduct.inductionOn with
    | add v₁ v₂ ih₁ ih₂ =>
      rw [map_add, leibnizDefect_add_right, ih₁, ih₂, add_zero]
    | tmul b y =>
      simp only [leibnizDefect, magicBracket_mixed_mixed, magicBracket_f4_mixed,
        f4MixedActLM_tmul, map_add, magicBracket_f4_g2, magicBracket_f4_f4,
        mixedToG2LM_tmul, mixedToMixedLM_tmul, mixedToF4LM_tmul, zero_add]
      apply SplitE8Lie.ext
      · simp only [SplitE8Lie.sub_g2, SplitE8Lie.add_g2, SplitE8Lie.zero_g2,
          embedG2LM_g2, embedMixed_g2, embedF4LM_g2]
        have hskew := f4_derivation_traceBilin_skew0 D x y
        simp only [f4Act_coe] at hskew
        have hc : (1 / 3 : ℝ) * traceBilin (f4Act D x).1 y.1 +
            (1 / 3 : ℝ) * traceBilin x.1 (f4Act D y).1 = 0 := by
          simp only [f4Act_coe]; linarith
        have hsum : ((1 / 3 : ℝ) * traceBilin (f4Act D x).1 y.1) • g2Inner a b +
            ((1 / 3 : ℝ) * traceBilin x.1 (f4Act D y).1) • g2Inner a b = 0 := by
          rw [← add_smul, hc, zero_smul]
        have hre :
            (0 + 0 - (((1 / 3 : ℝ) * traceBilin (f4Act D x).1 y.1) • g2Inner a b + 0 + 0) -
              (((1 / 3 : ℝ) * traceBilin x.1 (f4Act D y).1) • g2Inner a b + 0 + 0)) =
            -(((1 / 3 : ℝ) * traceBilin (f4Act D x).1 y.1) • g2Inner a b +
              ((1 / 3 : ℝ) * traceBilin x.1 (f4Act D y).1) • g2Inner a b) := by abel
        rw [hre, hsum, neg_zero]
      · simp only [SplitE8Lie.sub_mixed, SplitE8Lie.add_mixed, SplitE8Lie.zero_mixed,
          embedG2LM_mixed, embedMixed_mixed, embedF4LM_mixed, f4Act_h3Mul0,
          TensorProduct.tmul_add]
        abel
      · simp only [SplitE8Lie.sub_f4, SplitE8Lie.add_f4, SplitE8Lie.zero_f4,
          embedG2LM_f4, embedMixed_f4, embedF4LM_f4, lie_smul, f4_covariant, smul_add]
        abel

private def assoc0 (u v w : splitOctonionTraceZero) : splitOctonionTraceZero :=
  ⟨_root_.associator u.1 v.1 w.1, by
    change (ZornVectorMatrix.associator u.1 v.1 w.1).trace = 0
    exact ZornVectorMatrix.trace_associator u.1 v.1 w.1⟩

private theorem defect_mixed_mixed_mixed_tmul
    (a b c : splitOctonionTraceZero) (x y z : h3TraceZero) :
    leibnizDefect magicBracketLM (embedTensor a x) (embedTensor b y) (embedTensor c z) = 0 := by
  have hdef : leibnizDefect magicBracketLM (embedTensor a x) (embedTensor b y) (embedTensor c z) =
      magicBracketLM (embedTensor a x) (magicBracketLM (embedTensor b y) (embedTensor c z)) +
      magicBracketLM (embedTensor b y) (magicBracketLM (embedTensor c z) (embedTensor a x)) +
      magicBracketLM (embedTensor c z) (magicBracketLM (embedTensor a x) (embedTensor b y)) := by
    simp only [leibnizDefect]
    rw [magicBracketLM_antisymm (embedTensor c z) (embedTensor a x),
      magicBracketLM_antisymm (magicBracketLM (embedTensor a x) (embedTensor b y)) (embedTensor c z),
      map_neg]
    abel
  rw [hdef]
  have hterm (u v w : splitOctonionTraceZero) (p q r : h3TraceZero) :
      magicBracketLM (embedTensor u p) (magicBracketLM (embedTensor v q) (embedTensor w r)) =
        embedG2LM (((1 / 3 : ℝ) * traceBilin p.1 (h3Mul0 q r).1) • g2Inner u (zornComm0 v w)) +
        embedF4LM (((-2 : ℝ) * zornBilin u.1 (zornComm0 v w).1) • f4Inner p (h3Mul0 q r)) +
        embedMixed (
          (-((1 / 3 : ℝ) * traceBilin q.1 r.1) • g2Act (g2Inner v w) u) ⊗ₜ[ℝ] p +
          u ⊗ₜ[ℝ] (-((-2 : ℝ) * zornBilin v.1 w.1) • f4Act (f4Inner q r) p) +
          (zornComm0 u (zornComm0 v w)) ⊗ₜ[ℝ] (h3Mul0 p (h3Mul0 q r))) := by
    simp only [embedTensor_apply, magicBracket_mixed_mixed, map_add,
      magicBracket_mixed_g2, magicBracket_mixed_f4,
      mixedToG2LM_tmul, mixedToF4LM_tmul, mixedToMixedLM_tmul,
      map_smul, g2MixedActLM_tmul, f4MixedActLM_tmul,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    apply SplitE8Lie.ext
    · simp
    · simp only [SplitE8Lie.add_mixed, SplitE8Lie.neg_mixed, SplitE8Lie.smul_mixed,
        embedG2LM_mixed, embedF4LM_mixed, embedMixed_mixed, neg_smul, smul_neg,
        zero_add, add_zero, smul_zero]
      abel
    · simp
  rw [hterm a b c x y z, hterm b c a y z x, hterm c a b z x y]
  apply SplitE8Lie.ext
  · -- G₂ component: cyclic trace factor × stanDer_comm_cyclic_zero
    simp only [SplitE8Lie.add_g2, SplitE8Lie.zero_g2, embedG2LM_g2, embedF4LM_g2, embedMixed_g2,
      add_zero]
    rw [h3_traceBilin_mul_cyclic y z x, h3_traceBilin_mul_cyclic z x y]
    rw [← smul_add, ← smul_add, stanDer_comm_cyclic_zero a b c, smul_zero]
  · -- Mixed component: decomposes into Kleinfeld traceBilin term + symmetric C(a,b,c) ⊗ ∑ D^Jor
    simp only [SplitE8Lie.add_mixed, SplitE8Lie.zero_mixed, embedG2LM_mixed, embedF4LM_mixed,
      embedMixed_mixed, zero_add, add_zero]
    rw [h3Mul0_assoc_decompose x y z, h3Mul0_assoc_decompose y z x, h3Mul0_assoc_decompose z x y]
    simp only [TensorProduct.tmul_add, TensorProduct.tmul_sub, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul]
    -- 1. Cyclic sum of [u, [v, w]] for P₀
    have hP0_cyc :
        zornComm0 a (zornComm0 b c) + zornComm0 b (zornComm0 c a) + zornComm0 c (zornComm0 a b) =
          (-6 : ℝ) • assoc0 a b c := by
      apply Subtype.ext
      exact ZornVectorMatrix.zornJacobiator_eq_neg_six_smul_zornAssociator a.1 b.1 c.1
    -- 2. Kleinfeld cancellation for each of the 3 traceBilin lines (⟨y,z⟩•x, ⟨z,x⟩•y, ⟨x,y⟩•z)
    have hK (u v w : splitOctonionTraceZero) (r : ℝ) (p : h3TraceZero) :
        -((1 / 3 : ℝ) * r) • (g2Act (g2Inner v w) u) ⊗ₜ[ℝ] p +
          ((1 / 6 : ℝ) * r) • (((-6 : ℝ) • assoc0 u v w) ⊗ₜ[ℝ] p) -
          ((1 / 3 : ℝ) * r) • (zornComm0 u (zornComm0 v w)) ⊗ₜ[ℝ] p = 0 := by
      have hvec : -((1 / 3 : ℝ) * r) • g2Act (g2Inner v w) u - r • assoc0 u v w -
          ((1 / 3 : ℝ) * r) • zornComm0 u (zornComm0 v w) = 0 := by
        apply Subtype.ext
        have hsub : -((1 / 3 : ℝ) * r) • (g2Act (g2Inner v w) u).1 - r • (assoc0 u v w).1 -
            ((1 / 3 : ℝ) * r) • (zornComm0 u (zornComm0 v w)).1 =
            r • (-_root_.associator u.1 v.1 w.1 -
              (1 / 3 : ℝ) • (u.1 * (v.1 * w.1 - w.1 * v.1) - (v.1 * w.1 - w.1 * v.1) * u.1) -
              (1 / 3 : ℝ) • (g2Act (g2Inner v w) u).1) := by
          change -((1 / 3 : ℝ) * r) • (g2Act (g2Inner v w) u).1 - r • _root_.associator u.1 v.1 w.1 -
            ((1 / 3 : ℝ) * r) • (u.1 * (v.1 * w.1 - w.1 * v.1) - (v.1 * w.1 - w.1 * v.1) * u.1) = _
          simp only [smul_sub, smul_smul]
          module
        simp only [Submodule.coe_sub, SetLike.val_smul, Submodule.coe_zero]
        rw [hsub, show _root_.associator u.1 v.1 w.1 = ZornVectorMatrix.zornAssociator u.1 v.1 w.1 from rfl,
          kleinfeld_traceZero_combo u v w, smul_zero]
      have htmul :
          (-((1 / 3 : ℝ) * r) • g2Act (g2Inner v w) u - r • assoc0 u v w -
            ((1 / 3 : ℝ) * r) • zornComm0 u (zornComm0 v w)) ⊗ₜ[ℝ] p = 0 := by
        rw [hvec, TensorProduct.zero_tmul]
      simp only [TensorProduct.sub_tmul, TensorProduct.smul_tmul, TensorProduct.tmul_smul] at htmul
      have hre :
          -((1 / 3 : ℝ) * r) • (g2Act (g2Inner v w) u) ⊗ₜ[ℝ] p +
            ((1 / 6 : ℝ) * r) • (((-6 : ℝ) • assoc0 u v w) ⊗ₜ[ℝ] p) -
            ((1 / 3 : ℝ) * r) • (zornComm0 u (zornComm0 v w)) ⊗ₜ[ℝ] p =
          -((1 / 3 : ℝ) * r) • g2Act (g2Inner v w) u ⊗ₜ[ℝ] p -
            r • (assoc0 u v w) ⊗ₜ[ℝ] p -
            ((1 / 3 : ℝ) * r) • zornComm0 u (zornComm0 v w) ⊗ₜ[ℝ] p := by
        rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul,
          show ((1 / 6 : ℝ) * r) * (-6 : ℝ) = -r from by ring, neg_smul]
        abel
      rw [hre]
      simpa [neg_smul] using htmul
    have hKa := hK a b c (traceBilin y.1 z.1) x
    have hKb := hK b c a (traceBilin z.1 x.1) y
    have hKc := hK c a b (traceBilin x.1 y.1) z
    have hK_assoc_b : assoc0 b c a = assoc0 a b c := by
      apply Subtype.ext
      exact alternative_associator_cycle zorn_left_alternative zorn_right_alternative a.1 b.1 c.1
    have hK_assoc_c : assoc0 c a b = assoc0 a b c := by
      apply Subtype.ext
      exact (alternative_associator_cycle zorn_left_alternative zorn_right_alternative b.1 c.1 a.1).trans
        (alternative_associator_cycle zorn_left_alternative zorn_right_alternative a.1 b.1 c.1)
    -- 3. Symmetric C(a, b, c) for the D^Jor terms
    let C0 (u v w : splitOctonionTraceZero) : splitOctonionTraceZero :=
      (1 / 3 : ℝ) • (zornComm0 v (zornComm0 w u) - zornComm0 w (zornComm0 u v)) +
        (2 * zornBilin v.1 w.1) • u
    have hC0_eq (u v w : splitOctonionTraceZero) :
        C0 u v w = (2 / 3 : ℝ) •
          (zornBilin v.1 w.1 • u + zornBilin w.1 u.1 • v + zornBilin u.1 v.1 • w) := by
      apply Subtype.ext
      have hid := octonion_comm_double_identity u v w
      have hid3 := congrArg (fun s : VZ => (1 / 3 : ℝ) • s) hid
      simp only [smul_add, smul_smul, ← mul_assoc] at hid3
      have h36 : (1 / 3 : ℝ) * (6 : ℝ) = 2 := by norm_num
      have h32 : (1 / 3 : ℝ) * (2 : ℝ) = 2 / 3 := by norm_num
      rw [h36, h32] at hid3
      simpa [C0, zornComm0_coe, smul_add, smul_sub, smul_smul] using hid3
    have hC_symm_b : C0 b c a = C0 a b c := by
      rw [hC0_eq, hC0_eq]; congr 1; abel
    have hC_symm_c : C0 c a b = C0 a b c := by
      rw [hC0_eq, hC0_eq]; congr 1; abel
    have hDJor_cyc : f4Act (f4Inner y z) x + f4Act (f4Inner z x) y + f4Act (f4Inner x y) z = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_add, f4Act_coe, f4Inner, h3ZornJordanInnerDerivation_apply,
        Submodule.coe_zero]
      rw [mul_comm y.1 z.1, mul_comm z.1 x.1, mul_comm x.1 y.1]
      abel
    have hC_vanish :
        (C0 a b c) ⊗ₜ[ℝ] (f4Act (f4Inner y z) x) +
        (C0 b c a) ⊗ₜ[ℝ] (f4Act (f4Inner z x) y) +
        (C0 c a b) ⊗ₜ[ℝ] (f4Act (f4Inner x y) z) = 0 := by
      rw [hC_symm_b, hC_symm_c, ← TensorProduct.tmul_add, ← TensorProduct.tmul_add, hDJor_cyc,
        TensorProduct.tmul_zero]
    -- Expand `hP0_cyc` inside the P₀ part, and combine `hKa, hKb, hKc, hC_vanish`:
    have hP0_expand :
        (1 / 6 : ℝ) • ((zornComm0 a (zornComm0 b c) + zornComm0 b (zornComm0 c a) +
          zornComm0 c (zornComm0 a b)) ⊗ₜ[ℝ]
            (traceBilin y.1 z.1 • x + traceBilin z.1 x.1 • y + traceBilin x.1 y.1 • z)) =
        (1 / 6 : ℝ) • (((-6 : ℝ) • assoc0 a b c) ⊗ₜ[ℝ]
            (traceBilin y.1 z.1 • x + traceBilin z.1 x.1 • y + traceBilin x.1 y.1 • z)) := by
      rw [hP0_cyc]
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul, smul_add] at hP0_expand
    simp only [C0, TensorProduct.add_tmul, TensorProduct.sub_tmul, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul] at hC_vanish
    rw [hK_assoc_b] at hKb
    rw [hK_assoc_c] at hKc
    simp only [← mul_smul] at hKa hKb hKc hP0_expand hC_vanish ⊢
    have hP0_diff :
        ((((1 / 6 * traceBilin y.1 z.1) • zornComm0 a (zornComm0 b c) ⊗ₜ[ℝ] x +
            (1 / 6 * traceBilin z.1 x.1) • zornComm0 a (zornComm0 b c) ⊗ₜ[ℝ] y +
            (1 / 6 * traceBilin x.1 y.1) • zornComm0 a (zornComm0 b c) ⊗ₜ[ℝ] z) +
          ((1 / 6 * traceBilin y.1 z.1) • zornComm0 b (zornComm0 c a) ⊗ₜ[ℝ] x +
            (1 / 6 * traceBilin z.1 x.1) • zornComm0 b (zornComm0 c a) ⊗ₜ[ℝ] y +
            (1 / 6 * traceBilin x.1 y.1) • zornComm0 b (zornComm0 c a) ⊗ₜ[ℝ] z)) +
          ((1 / 6 * traceBilin y.1 z.1) • zornComm0 c (zornComm0 a b) ⊗ₜ[ℝ] x +
            (1 / 6 * traceBilin z.1 x.1) • zornComm0 c (zornComm0 a b) ⊗ₜ[ℝ] y +
            (1 / 6 * traceBilin x.1 y.1) • zornComm0 c (zornComm0 a b) ⊗ₜ[ℝ] z)) -
        ((1 / 6 * -6 * traceBilin y.1 z.1) • (assoc0 a b c) ⊗ₜ[ℝ] x +
          (1 / 6 * -6 * traceBilin z.1 x.1) • (assoc0 a b c) ⊗ₜ[ℝ] y +
          (1 / 6 * -6 * traceBilin x.1 y.1) • (assoc0 a b c) ⊗ₜ[ℝ] z) = 0 := by
      have hp := sub_eq_zero.mpr hP0_expand
      simp only [show ∀ t : ℝ, (1 / 6 : ℝ) * (t * -6) = 1 / 6 * -6 * t from fun _ => by ring] at hp
      have hre :
          ((((1 / 6 * traceBilin y.1 z.1) • zornComm0 a (zornComm0 b c) ⊗ₜ[ℝ] x +
              (1 / 6 * traceBilin z.1 x.1) • zornComm0 a (zornComm0 b c) ⊗ₜ[ℝ] y +
              (1 / 6 * traceBilin x.1 y.1) • zornComm0 a (zornComm0 b c) ⊗ₜ[ℝ] z) +
            ((1 / 6 * traceBilin y.1 z.1) • zornComm0 b (zornComm0 c a) ⊗ₜ[ℝ] x +
              (1 / 6 * traceBilin z.1 x.1) • zornComm0 b (zornComm0 c a) ⊗ₜ[ℝ] y +
              (1 / 6 * traceBilin x.1 y.1) • zornComm0 b (zornComm0 c a) ⊗ₜ[ℝ] z)) +
            ((1 / 6 * traceBilin y.1 z.1) • zornComm0 c (zornComm0 a b) ⊗ₜ[ℝ] x +
              (1 / 6 * traceBilin z.1 x.1) • zornComm0 c (zornComm0 a b) ⊗ₜ[ℝ] y +
              (1 / 6 * traceBilin x.1 y.1) • zornComm0 c (zornComm0 a b) ⊗ₜ[ℝ] z)) =
          (((1 / 6 * traceBilin y.1 z.1) • zornComm0 a (zornComm0 b c) ⊗ₜ[ℝ] x +
              (1 / 6 * traceBilin y.1 z.1) • zornComm0 b (zornComm0 c a) ⊗ₜ[ℝ] x +
              (1 / 6 * traceBilin y.1 z.1) • zornComm0 c (zornComm0 a b) ⊗ₜ[ℝ] x) +
            ((1 / 6 * traceBilin z.1 x.1) • zornComm0 a (zornComm0 b c) ⊗ₜ[ℝ] y +
              (1 / 6 * traceBilin z.1 x.1) • zornComm0 b (zornComm0 c a) ⊗ₜ[ℝ] y +
              (1 / 6 * traceBilin z.1 x.1) • zornComm0 c (zornComm0 a b) ⊗ₜ[ℝ] y)) +
            ((1 / 6 * traceBilin x.1 y.1) • zornComm0 a (zornComm0 b c) ⊗ₜ[ℝ] z +
              (1 / 6 * traceBilin x.1 y.1) • zornComm0 b (zornComm0 c a) ⊗ₜ[ℝ] z +
              (1 / 6 * traceBilin x.1 y.1) • zornComm0 c (zornComm0 a b) ⊗ₜ[ℝ] z) := by
        abel
      rw [hre]
      exact hp
    simp only [← TensorProduct.smul_tmul', smul_smul] at hKa hKb hKc
    have hzero : ∀ {u v : MixedCarrier}, u = 0 → v = 0 → u + v = 0 := by
      rintro u v rfl rfl; exact add_zero 0
    have hcomb := hzero (hzero (hzero hKa hKb) (hzero hKc hC_vanish)) hP0_diff
    refine Eq.trans ?_ hcomb
    module
  · -- F₄ component: cyclic zornBilin factor × f4Inner_mul_cyclic_zero
    simp only [SplitE8Lie.add_f4, SplitE8Lie.zero_f4, embedG2LM_f4, embedF4LM_f4, embedMixed_f4,
      add_zero, zero_add]
    rw [zornBilin_comm_cyclic a b c, zornBilin_comm_cyclic b c a]
    rw [← smul_add, ← smul_add, f4Inner_mul_cyclic_zero x y z, smul_zero]

private theorem defect_mixed_mixed_mixed (m₁ m₂ m₃ : MixedCarrier) :
    leibnizDefect magicBracketLM (embedMixed m₁) (embedMixed m₂) (embedMixed m₃) = 0 := by
  induction m₁ using TensorProduct.inductionOn with
  | add u₁ u₂ ih₁ ih₂ =>
    rw [map_add, leibnizDefect_add_left, ih₁, ih₂, add_zero]
  | tmul a x =>
    induction m₂ using TensorProduct.inductionOn with
    | add v₁ v₂ ih₁ ih₂ =>
      rw [map_add, leibnizDefect_add_mid, ih₁, ih₂, add_zero]
    | tmul b y =>
      induction m₃ using TensorProduct.inductionOn with
      | add w₁ w₂ ih₁ ih₂ =>
        rw [map_add, leibnizDefect_add_right, ih₁, ih₂, add_zero]
      | tmul c z =>
        exact defect_mixed_mixed_mixed_tmul a b c x y z

private theorem defect_all_cells (i j k : SplitE8Grade) (X Y Z : SplitE8Lie) :
    leibnizDefect magicBracketLM (gradeProj i X) (gradeProj j Y) (gradeProj k Z) = 0 := by
  cases i <;> cases j <;> cases k <;>
    simp only [gradeProj, projG2Sub, projMixedSub, projF4Sub, LinearMap.comp_apply]
  · exact defect_g2_g2_g2 _ _ _
  · exact defect_g2_g2_mixed _ _ _
  · exact defect_g2_g2_f4 _ _ _
  · rw [defect_swap₂₃, defect_g2_g2_mixed, neg_zero]
  · exact defect_g2_mixed_mixed _ _ _
  · rw [defect_swap₂₃, defect_g2_f4_mixed, neg_zero]
  · rw [defect_swap₂₃, defect_g2_g2_f4, neg_zero]
  · exact defect_g2_f4_mixed _ _ _
  · exact defect_g2_f4_f4 _ _ _
  · rw [← defect_cycle, defect_g2_g2_mixed]
  · rw [defect_swap₁₂, defect_g2_mixed_mixed, neg_zero]
  · rw [defect_swap₁₂, defect_swap₂₃, defect_g2_f4_mixed, neg_zero, neg_zero]
  · rw [defect_cycle, defect_g2_mixed_mixed]
  · exact defect_mixed_mixed_mixed _ _ _
  · rw [defect_cycle, defect_f4_mixed_mixed]
  · rw [defect_cycle, defect_swap₂₃, defect_g2_f4_mixed, neg_zero]
  · rw [defect_swap₁₂, defect_f4_mixed_mixed, neg_zero]
  · rw [← defect_cycle, defect_f4_f4_mixed]
  · rw [← defect_cycle, defect_g2_g2_f4]
  · rw [defect_swap₁₂, defect_g2_f4_mixed, neg_zero]
  · rw [defect_swap₁₂, defect_swap₂₃, defect_g2_f4_f4, neg_zero, neg_zero]
  · rw [defect_cycle, defect_g2_f4_mixed]
  · exact defect_f4_mixed_mixed _ _ _
  · rw [defect_swap₂₃, defect_f4_f4_mixed, neg_zero]
  · rw [defect_cycle, defect_g2_f4_f4]
  · exact defect_f4_f4_mixed _ _ _
  · exact defect_f4_f4_f4 _ _ _

theorem magicBracketLM_leibniz (X Y Z : SplitE8Lie) :
    magicBracketLM X (magicBracketLM Y Z) =
      magicBracketLM (magicBracketLM X Y) Z + magicBracketLM Y (magicBracketLM X Z) := by
  have h := global_leibniz_of_homogeneous magicBracketLM gradeProj gradeProj_sum defect_all_cells X Y Z
  dsimp [leibnizDefect] at h
  have hsub : magicBracketLM X (magicBracketLM Y Z) - magicBracketLM (magicBracketLM X Y) Z =
      magicBracketLM Y (magicBracketLM X Z) := sub_eq_zero.mp h
  rw [eq_add_of_sub_eq' hsub, add_comm]

instance SplitE8Lie.instLieRing : LieRing SplitE8Lie where
  bracket X Y := magicBracketLM X Y
  add_lie X₁ X₂ Y := by
    change magicBracketLM (X₁ + X₂) Y = magicBracketLM X₁ Y + magicBracketLM X₂ Y
    simp [map_add]
  lie_add X Y₁ Y₂ := by
    change magicBracketLM X (Y₁ + Y₂) = magicBracketLM X Y₁ + magicBracketLM X Y₂
    simp [map_add]
  lie_self X := magicBracketLM_self X
  leibniz_lie X Y Z := by
    change magicBracketLM X (magicBracketLM Y Z) =
      magicBracketLM (magicBracketLM X Y) Z + magicBracketLM Y (magicBracketLM X Z)
    exact magicBracketLM_leibniz X Y Z

instance SplitE8Lie.instLieAlgebra : LieAlgebra ℝ SplitE8Lie where
  lie_smul r X Y := by
    change magicBracketLM X (r • Y) = r • magicBracketLM X Y
    simp [map_smul]

end MagicSquareBracket

/-! ## 5. Lie Embeddings and Bracket Evaluation Lemmas -/

section EmbeddingsAndBrackets

/-- Lie algebra embedding `G₂(2) →ₗ⁅ℝ⁆ SplitE8Lie`. -/
def embedG2 : G2DerivationCarrier →ₗ⁅ℝ⁆ SplitE8Lie :=
  { embedG2LM with
    map_lie' := fun {D₁ D₂} => (magicBracket_g2_g2 D₁ D₂).symm }

/-- Lie algebra embedding `F₄(4) →ₗ⁅ℝ⁆ SplitE8Lie`. -/
def embedF4 : F4DerivationCarrier →ₗ⁅ℝ⁆ SplitE8Lie :=
  { embedF4LM with
    map_lie' := fun {D₁ D₂} => (magicBracket_f4_f4 D₁ D₂).symm }

@[simp] theorem embedG2_apply (D : G2DerivationCarrier) :
    embedG2 D = ⟨D, 0, 0⟩ := rfl

@[simp] theorem embedF4_apply (D : F4DerivationCarrier) :
    embedF4 D = ⟨0, 0, D⟩ := rfl

@[simp] theorem embedMixed_apply (m : MixedCarrier) :
    embedMixed m = ⟨0, m, 0⟩ := rfl

@[simp] theorem bracket_g2_g2 (D₁ D₂ : G2DerivationCarrier) :
    ⁅embedG2 D₁, embedG2 D₂⁆ = embedG2 ⁅D₁, D₂⁆ :=
  magicBracket_g2_g2 D₁ D₂

@[simp] theorem bracket_f4_f4 (D₁ D₂ : F4DerivationCarrier) :
    ⁅embedF4 D₁, embedF4 D₂⁆ = embedF4 ⁅D₁, D₂⁆ :=
  magicBracket_f4_f4 D₁ D₂

@[simp] theorem bracket_g2_f4 (D₁ : G2DerivationCarrier) (D₂ : F4DerivationCarrier) :
    ⁅embedG2 D₁, embedF4 D₂⁆ = 0 :=
  magicBracket_g2_f4 D₁ D₂

@[simp] theorem bracket_f4_g2 (D₁ : F4DerivationCarrier) (D₂ : G2DerivationCarrier) :
    ⁅embedF4 D₁, embedG2 D₂⁆ = 0 :=
  magicBracket_f4_g2 D₁ D₂

@[simp] theorem bracket_g2_mixed (D : G2DerivationCarrier) (m : MixedCarrier) :
    ⁅embedG2 D, embedMixed m⁆ = embedMixed (g2MixedActLM D m) :=
  magicBracket_g2_mixed D m

@[simp] theorem bracket_mixed_g2 (m : MixedCarrier) (D : G2DerivationCarrier) :
    ⁅embedMixed m, embedG2 D⁆ = -embedMixed (g2MixedActLM D m) := by
  change magicBracketLM (embedMixed m) (embedG2LM D) = _
  rw [magicBracket_mixed_g2, map_neg]

@[simp] theorem bracket_g2_tensor (D : G2DerivationCarrier)
    (a : splitOctonionTraceZero) (x : h3TraceZero) :
    ⁅embedG2 D, embedTensor a x⁆ = embedTensor (g2Act D a) x := by
  change magicBracketLM (embedG2LM D) (embedMixed (a ⊗ₜ[ℝ] x)) = _
  rw [magicBracket_g2_mixed, g2MixedActLM_tmul, embedTensor_apply]

@[simp] theorem bracket_tensor_g2 (a : splitOctonionTraceZero) (x : h3TraceZero)
    (D : G2DerivationCarrier) :
    ⁅embedTensor a x, embedG2 D⁆ = -embedTensor (g2Act D a) x := by
  change magicBracketLM (embedMixed (a ⊗ₜ[ℝ] x)) (embedG2LM D) = _
  rw [magicBracket_mixed_g2, g2MixedActLM_tmul, map_neg, embedTensor_apply]

@[simp] theorem bracket_f4_mixed (D : F4DerivationCarrier) (m : MixedCarrier) :
    ⁅embedF4 D, embedMixed m⁆ = embedMixed (f4MixedActLM D m) :=
  magicBracket_f4_mixed D m

@[simp] theorem bracket_mixed_f4 (m : MixedCarrier) (D : F4DerivationCarrier) :
    ⁅embedMixed m, embedF4 D⁆ = -embedMixed (f4MixedActLM D m) := by
  change magicBracketLM (embedMixed m) (embedF4LM D) = _
  rw [magicBracket_mixed_f4, map_neg]

@[simp] theorem bracket_f4_tensor (D : F4DerivationCarrier)
    (a : splitOctonionTraceZero) (x : h3TraceZero) :
    ⁅embedF4 D, embedTensor a x⁆ = embedTensor a (f4Act D x) := by
  change magicBracketLM (embedF4LM D) (embedMixed (a ⊗ₜ[ℝ] x)) = _
  rw [magicBracket_f4_mixed, f4MixedActLM_tmul, embedTensor_apply]

@[simp] theorem bracket_tensor_f4 (a : splitOctonionTraceZero) (x : h3TraceZero)
    (D : F4DerivationCarrier) :
    ⁅embedTensor a x, embedF4 D⁆ = -embedTensor a (f4Act D x) := by
  change magicBracketLM (embedMixed (a ⊗ₜ[ℝ] x)) (embedF4LM D) = _
  rw [magicBracket_mixed_f4, f4MixedActLM_tmul, map_neg, embedTensor_apply]

@[simp] theorem bracket_mixed_mixed (m₁ m₂ : MixedCarrier) :
    ⁅embedMixed m₁, embedMixed m₂⁆ =
      embedG2 (mixedToG2LM m₁ m₂) + embedMixed (mixedToMixedLM m₁ m₂) +
        embedF4 (mixedToF4LM m₁ m₂) :=
  magicBracket_mixed_mixed m₁ m₂

@[simp] theorem bracket_tensor_tensor (a b : splitOctonionTraceZero) (x y : h3TraceZero) :
    ⁅embedTensor a x, embedTensor b y⁆ =
      embedG2 (((1 / 3 : ℝ) * traceBilin x.1 y.1) • g2Inner a b) +
      embedTensor (zornComm0 a b) (h3Mul0 x y) +
      embedF4 (((-2 : ℝ) * zornBilin a.1 b.1) • f4Inner x y) := by
  change magicBracketLM (embedMixed (a ⊗ₜ[ℝ] x)) (embedMixed (b ⊗ₜ[ℝ] y)) = _
  rw [magicBracket_mixed_mixed, mixedToG2LM_tmul, mixedToMixedLM_tmul, mixedToF4LM_tmul]
  rfl

end EmbeddingsAndBrackets

/-! ## 6. Concrete Basis Elements, Evaluation Lemmas, Witness & Cartan APIs (for M6b) -/

section ConcreteElementsAndCartan

/-- Canonical diagonal imaginary split octonion `e₀ = E11 - E22 = ⟨1, 0, 0, -1⟩`. -/
def zornE0 : splitOctonionTraceZero :=
  ⟨ZornVectorMatrix.diagonal 1 (-1), by
    change (ZornVectorMatrix.diagonal (1 : ℝ) (-1)).trace = 0
    simp [ZornVectorMatrix.diagonal, ZornVectorMatrix.trace]⟩

/-- Chiral upper basis element `U i` as a traceless split octonion. -/
def zornU (i : Fin 3) : splitOctonionTraceZero :=
  ⟨ZornVectorMatrix.U i, by
    change (ZornVectorMatrix.U i).trace = 0
    simp [ZornVectorMatrix.U, ZornVectorMatrix.trace]⟩

/-- Chiral lower basis element `V i` as a traceless split octonion. -/
def zornV (i : Fin 3) : splitOctonionTraceZero :=
  ⟨ZornVectorMatrix.V i, by
    change (ZornVectorMatrix.V i).trace = 0
    simp [ZornVectorMatrix.V, ZornVectorMatrix.trace]⟩

/-- Traceless diagonal Albert element `h3_diag₁ - h3_diag₂`. -/
def h3DiagZero₁ : h3TraceZero :=
  ⟨h3_diag₁ - h3_diag₂, by
    change (h3_diag₁ - h3_diag₂).α₁ + (h3_diag₁ - h3_diag₂).α₂ + (h3_diag₁ - h3_diag₂).α₃ = 0
    change (1 - 0 : ℝ) + (0 - 1) + (0 - 0) = 0
    norm_num⟩

/-- Traceless diagonal Albert element `h3_diag₂ - h3_diag₃`. -/
def h3DiagZero₂ : h3TraceZero :=
  ⟨h3_diag₂ - h3_diag₃, by
    change (h3_diag₂ - h3_diag₃).α₁ + (h3_diag₂ - h3_diag₃).α₂ + (h3_diag₂ - h3_diag₃).α₃ = 0
    change (0 - 0 : ℝ) + (1 - 0) + (0 - 1) = 0
    norm_num⟩

/-- Off-diagonal `(1,2)` Jordan element inside `h3TraceZero`. -/
def h3EmbedJ12 (z : VZ) : h3TraceZero :=
  ⟨InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 z, by
    change linearTrace (InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 z) = 0
    simp [linearTrace, InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12]⟩

/-- Off-diagonal `(2,3)` Jordan element inside `h3TraceZero`. -/
def h3EmbedJ23 (z : VZ) : h3TraceZero :=
  ⟨embedJ23 z, by
    change linearTrace (embedJ23 z) = 0
    simp [linearTrace, embedJ23]⟩

/-- Off-diagonal `(3,1)` Jordan element inside `h3TraceZero`. -/
def h3EmbedJ31 (z : VZ) : h3TraceZero :=
  ⟨embedJ31 z, by
    change linearTrace (embedJ31 z) = 0
    simp [linearTrace, embedJ31]⟩

@[simp] theorem zornE0_coe : (zornE0 : VZ) = ZornVectorMatrix.diagonal 1 (-1) := rfl
@[simp] theorem zornU_coe (i : Fin 3) : (zornU i : VZ) = ZornVectorMatrix.U i := rfl
@[simp] theorem zornV_coe (i : Fin 3) : (zornV i : VZ) = ZornVectorMatrix.V i := rfl
@[simp] theorem h3DiagZero₁_coe : (h3DiagZero₁ : H3Zorn ℝ) = h3_diag₁ - h3_diag₂ := rfl
@[simp] theorem h3DiagZero₂_coe : (h3DiagZero₂ : H3Zorn ℝ) = h3_diag₂ - h3_diag₃ := rfl
@[simp] theorem h3EmbedJ12_coe (z : VZ) :
    (h3EmbedJ12 z : H3Zorn ℝ) = InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 z := rfl
@[simp] theorem h3EmbedJ23_coe (z : VZ) : (h3EmbedJ23 z : H3Zorn ℝ) = embedJ23 z := rfl
@[simp] theorem h3EmbedJ31_coe (z : VZ) : (h3EmbedJ31 z : H3Zorn ℝ) = embedJ31 z := rfl

@[simp] theorem zornBilin_zornE0_self : zornBilin zornE0.1 zornE0.1 = -2 := by
  simp [zornBilin, zornE0, ZornVectorMatrix.diagonal, ZornVectorMatrix.conj,
    ZornVectorMatrix.mul, ZornVectorMatrix.trace, ZornVec3.dot]

@[simp] theorem zornBilin_zornE0_zornU (i : Fin 3) : zornBilin zornE0.1 (zornU i).1 = 0 := by
  fin_cases i <;>
    simp [zornBilin, zornE0, zornU, ZornVectorMatrix.diagonal, ZornVectorMatrix.U,
      ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.trace, ZornVec3.dot,
      ZornVec3.basis]

@[simp] theorem zornBilin_zornE0_zornV (i : Fin 3) : zornBilin zornE0.1 (zornV i).1 = 0 := by
  fin_cases i <;>
    simp [zornBilin, zornE0, zornV, ZornVectorMatrix.diagonal, ZornVectorMatrix.V,
      ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.trace, ZornVec3.dot,
      ZornVec3.basis]

@[simp] theorem zornComm0_zornE0_zornU (i : Fin 3) :
    zornComm0 zornE0 (zornU i) = (2 : ℝ) • zornU i := by
  apply Subtype.ext
  have hc := ZornVectorMatrix.commutator_diagonal_offDiagonal (1 : ℝ) (-1) (ZornVec3.basis i) 0
  change ZornVectorMatrix.commutator (ZornVectorMatrix.diagonal 1 (-1))
      (ZornVectorMatrix.offDiagonal (ZornVec3.basis i) 0) = (2 : ℝ) • ZornVectorMatrix.U i
  rw [hc]
  apply ZornVectorMatrix.ext <;>
    simp [ZornVectorMatrix.U, ZornVectorMatrix.offDiagonal, ZornVectorMatrix.smul]
  all_goals try (funext k; fin_cases k <;> simp [ZornVec3.basis] <;> ring)

@[simp] theorem zornComm0_zornE0_zornV (i : Fin 3) :
    zornComm0 zornE0 (zornV i) = (-2 : ℝ) • zornV i := by
  apply Subtype.ext
  have hc := ZornVectorMatrix.commutator_diagonal_offDiagonal (1 : ℝ) (-1) 0 (ZornVec3.basis i)
  change ZornVectorMatrix.commutator (ZornVectorMatrix.diagonal 1 (-1))
      (ZornVectorMatrix.offDiagonal 0 (ZornVec3.basis i)) = (-2 : ℝ) • ZornVectorMatrix.V i
  rw [hc]
  apply ZornVectorMatrix.ext <;>
    simp [ZornVectorMatrix.V, ZornVectorMatrix.offDiagonal, ZornVectorMatrix.smul,
      ZornVectorMatrix.neg]
  all_goals try (funext k; fin_cases i <;> fin_cases k <;> simp [ZornVec3.basis] <;> norm_num)

private theorem h3DiagZero₁_off :
    h3DiagZero₁.1.a = 0 ∧ h3DiagZero₁.1.b = 0 ∧ h3DiagZero₁.1.c = 0 :=
  ⟨sub_self _, sub_self _, sub_self _⟩

private theorem h3DiagZero₂_off :
    h3DiagZero₂.1.a = 0 ∧ h3DiagZero₂.1.b = 0 ∧ h3DiagZero₂.1.c = 0 :=
  ⟨sub_self _, sub_self _, sub_self _⟩

private theorem vz_trace_zero_mul (u : VZ) :
    (ZornVectorMatrix.mul (0 : VZ) u).trace = 0 := by
  simp [ZornVectorMatrix.mul, ZornVectorMatrix.trace, ZornVectorMatrix.zero, ZornVec3.dot]

@[simp] theorem traceBilin_h3DiagZero₁_h3EmbedJ23 (w : VZ) :
    traceBilin h3DiagZero₁.1 (h3EmbedJ23 w).1 = 0 := by
  simp only [traceBilin, h3DiagZero₁_off.1, h3DiagZero₁_off.2.1, h3DiagZero₁_off.2.2,
    h3EmbedJ23_coe, embedJ23, vz_trace_zero_mul, mul_zero, add_zero]

@[simp] theorem traceBilin_h3DiagZero₁_h3EmbedJ12 (w : VZ) :
    traceBilin h3DiagZero₁.1 (h3EmbedJ12 w).1 = 0 := by
  simp only [traceBilin, h3DiagZero₁_off.1, h3DiagZero₁_off.2.1, h3DiagZero₁_off.2.2,
    h3EmbedJ12_coe, InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12,
    vz_trace_zero_mul, mul_zero, add_zero]

@[simp] theorem traceBilin_h3DiagZero₁_h3EmbedJ31 (w : VZ) :
    traceBilin h3DiagZero₁.1 (h3EmbedJ31 w).1 = 0 := by
  simp only [traceBilin, h3DiagZero₁_off.1, h3DiagZero₁_off.2.1, h3DiagZero₁_off.2.2,
    h3EmbedJ31_coe, embedJ31, vz_trace_zero_mul, mul_zero, add_zero]

@[simp] theorem h3Mul0_h3DiagZero₁_h3EmbedJ23 (w : VZ) :
    h3Mul0 h3DiagZero₁ (h3EmbedJ23 w) = (-1 / 2 : ℝ) • h3EmbedJ23 w := by
  apply Subtype.ext
  rw [h3Mul0_coe, traceBilin_h3DiagZero₁_h3EmbedJ23]
  simp only [mul_zero, zero_smul, sub_zero, SetLike.val_smul, h3DiagZero₁_coe, h3EmbedJ23_coe,
    sub_mul, h3_diag₁_mul_embedJ23, h3_diag₂_mul_embedJ23, zero_sub]
  module

@[simp] theorem h3Mul0_h3DiagZero₁_h3EmbedJ31 (w : VZ) :
    h3Mul0 h3DiagZero₁ (h3EmbedJ31 w) = (1 / 2 : ℝ) • h3EmbedJ31 w := by
  apply Subtype.ext
  rw [h3Mul0_coe, traceBilin_h3DiagZero₁_h3EmbedJ31]
  simp only [mul_zero, zero_smul, sub_zero, SetLike.val_smul, h3DiagZero₁_coe, h3EmbedJ31_coe,
    sub_mul, h3_diag₁_mul_embedJ31, h3_diag₂_mul_embedJ31, sub_zero]

@[simp] theorem h3Mul0_h3DiagZero₁_h3EmbedJ12 (w : VZ) :
    h3Mul0 h3DiagZero₁ (h3EmbedJ12 w) = 0 := by
  apply Subtype.ext
  rw [h3Mul0_coe, traceBilin_h3DiagZero₁_h3EmbedJ12]
  simp only [mul_zero, zero_smul, h3DiagZero₁_coe, h3EmbedJ12_coe, sub_mul,
    h3_diag₁_mul_embedJ12, h3_diag₂_mul_embedJ12, sub_self, Submodule.coe_zero]

@[simp] theorem h3Mul0_h3DiagZero₂_h3EmbedJ12 (w : VZ) :
    h3Mul0 h3DiagZero₂ (h3EmbedJ12 w) = (1 / 2 : ℝ) • h3EmbedJ12 w := by
  apply Subtype.ext
  have htb : traceBilin h3DiagZero₂.1 (h3EmbedJ12 w).1 = 0 := by
    simp only [traceBilin, h3DiagZero₂_off.1, h3DiagZero₂_off.2.1, h3DiagZero₂_off.2.2,
      h3EmbedJ12_coe, InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12,
      vz_trace_zero_mul, mul_zero, add_zero]
  rw [h3Mul0_coe, htb]
  simp only [mul_zero, zero_smul, sub_zero, SetLike.val_smul, h3DiagZero₂_coe, h3EmbedJ12_coe,
    sub_mul, h3_diag₂_mul_embedJ12, h3_diag₃_mul_embedJ12, sub_zero]

@[simp] theorem h3Mul0_h3DiagZero₂_h3EmbedJ23 (w : VZ) :
    h3Mul0 h3DiagZero₂ (h3EmbedJ23 w) = 0 := by
  apply Subtype.ext
  have htb : traceBilin h3DiagZero₂.1 (h3EmbedJ23 w).1 = 0 := by
    simp only [traceBilin, h3DiagZero₂_off.1, h3DiagZero₂_off.2.1, h3DiagZero₂_off.2.2,
      h3EmbedJ23_coe, embedJ23, vz_trace_zero_mul, mul_zero, add_zero]
  rw [h3Mul0_coe, htb]
  simp only [mul_zero, zero_smul, h3DiagZero₂_coe, h3EmbedJ23_coe, sub_mul,
    h3_diag₂_mul_embedJ23, h3_diag₃_mul_embedJ23, sub_self, Submodule.coe_zero]

@[simp] theorem h3Mul0_h3DiagZero₂_h3EmbedJ31 (w : VZ) :
    h3Mul0 h3DiagZero₂ (h3EmbedJ31 w) = (-1 / 2 : ℝ) • h3EmbedJ31 w := by
  apply Subtype.ext
  have htb : traceBilin h3DiagZero₂.1 (h3EmbedJ31 w).1 = 0 := by
    simp only [traceBilin, h3DiagZero₂_off.1, h3DiagZero₂_off.2.1, h3DiagZero₂_off.2.2,
      h3EmbedJ31_coe, embedJ31, vz_trace_zero_mul, mul_zero, add_zero]
  rw [h3Mul0_coe, htb]
  simp only [mul_zero, zero_smul, sub_zero, SetLike.val_smul, h3DiagZero₂_coe, h3EmbedJ31_coe,
    sub_mul, h3_diag₂_mul_embedJ31, h3_diag₃_mul_embedJ31, zero_sub]
  module

/-- Concrete non-trivial bracket witness in `SplitE8Lie`:
`⁅e₀ ⊗ (h3_diag₁ - h3_diag₂), U 0 ⊗ h3_off₂₃ 0⁆ = -(U 0 ⊗ h3_off₂₃ 0) ≠ 0`. -/
theorem exists_bracket_ne_zero : ∃ x y : SplitE8Lie, ⁅x, y⁆ ≠ 0 := by
  refine ⟨embedTensor zornE0 h3DiagZero₁, embedTensor (zornU 0) (h3EmbedJ23 (zorn_basis 0)), ?_⟩
  rw [bracket_tensor_tensor, traceBilin_h3DiagZero₁_h3EmbedJ23, zornBilin_zornE0_zornU,
    zornComm0_zornE0_zornU, h3Mul0_h3DiagZero₁_h3EmbedJ23]
  simp only [mul_zero, zero_smul, map_zero, zero_add, add_zero, embedTensor_apply,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul]
  norm_num
  intro h
  have hm : -((zornU 0) ⊗ₜ[ℝ] (h3EmbedJ23 (zorn_basis 0))) = (0 : MixedCarrier) := by
    have h' := congrArg projMixed h
    simpa [embedMixed, projMixed] using h'
  have hnz : (zornU 0) ⊗ₜ[ℝ] (h3EmbedJ23 (zorn_basis 0)) ≠ (0 : MixedCarrier) := by
    let f1 : splitOctonionTraceZero →ₗ[ℝ] ℝ :=
      { toFun := fun a => a.1.v 0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let f2 : h3TraceZero →ₗ[ℝ] ℝ :=
      { toFun := fun x => x.1.b.a
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let f : MixedCarrier →ₗ[ℝ] ℝ :=
      TensorProduct.lift (LinearMap.lsmul ℝ ℝ |>.compl₂ f2 |>.comp f1)
    intro h0
    have hf := congrArg f h0
    have hfval : f ((zornU 0) ⊗ₜ[ℝ] (h3EmbedJ23 (zorn_basis 0))) = 1 := by
      change (zornU 0).1.v 0 * (h3EmbedJ23 (zorn_basis 0)).1.b.a = 1
      simp [zornU, ZornVectorMatrix.U, ZornVec3.basis, h3EmbedJ23, embedJ23, zorn_basis]
    rw [hfval, map_zero] at hf
    exact one_ne_zero hf
  exact hnz (neg_eq_zero.mp hm)

/-- Canonical 2D split Cartan basis of `G₂(2)` in `G2DerivationCarrier` (`VDer`),
corresponding to `parameterUnit 6` and `parameterUnit 13` (mapped to `canonicalZornDerivations`
via `vectorCanonicalLieEquiv`). -/
def g2CartanBasis : Fin 2 → G2DerivationCarrier
  | 0 => InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation
      (fun i => if i = 6 then 1 else 0)
  | 1 => InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation
      (fun i => if i = 13 then 1 else 0)

theorem g2CartanBasis_apply_zornE0 (i : Fin 2) :
    g2Act (g2CartanBasis i) zornE0 = 0 := by
  fin_cases i <;> apply Subtype.ext <;> apply ZornVectorMatrix.ext <;>
    simp [g2CartanBasis, InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation,
      InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterAction, zornE0,
      ZornVectorMatrix.diagonal, ZornVectorMatrix.zero]

theorem g2CartanBasis_apply_zornU (i : Fin 2) (k : Fin 3) :
    g2Act (g2CartanBasis i) (zornU k) =
      (match i, k with
      | 0, 0 => (1 : ℝ)
      | 0, 1 => -1
      | 0, 2 => 0
      | 1, 0 => 1
      | 1, 1 => 0
      | 1, 2 => -1) • zornU k := by
  fin_cases i <;> fin_cases k <;> apply Subtype.ext <;> apply ZornVectorMatrix.ext
  all_goals
    simp [g2CartanBasis, InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation,
      InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterAction, zornU,
      ZornVectorMatrix.U, ZornVectorMatrix.zero, ZornVectorMatrix.neg]
  all_goals try (funext j; fin_cases j <;> simp [ZornVec3.basis])

theorem g2CartanBasis_apply_zornV (i : Fin 2) (k : Fin 3) :
    g2Act (g2CartanBasis i) (zornV k) =
      (match i, k with
      | 0, 0 => (-1 : ℝ)
      | 0, 1 => 1
      | 0, 2 => 0
      | 1, 0 => -1
      | 1, 1 => 0
      | 1, 2 => 1) • zornV k := by
  fin_cases i <;> fin_cases k <;> apply Subtype.ext <;> apply ZornVectorMatrix.ext
  all_goals
    simp [g2CartanBasis, InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation,
      InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterAction, zornV,
      ZornVectorMatrix.V, ZornVectorMatrix.zero, ZornVectorMatrix.neg]
  all_goals try (funext j; fin_cases j <;> simp [ZornVec3.basis])

theorem g2CartanBasis_comm (i j : Fin 2) :
    ⁅g2CartanBasis i, g2CartanBasis j⁆ = 0 := by
  fin_cases i <;> fin_cases j <;> apply ZornVectorMatrix.Derivation.ext <;> intro X
  · simp
  · change (g2CartanBasis 0) ((g2CartanBasis 1) X) - (g2CartanBasis 1) ((g2CartanBasis 0) X) = 0
    apply ZornVectorMatrix.ext <;>
      simp [g2CartanBasis, InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation,
        InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterAction, ZornVectorMatrix.zero]
  · change (g2CartanBasis 1) ((g2CartanBasis 0) X) - (g2CartanBasis 0) ((g2CartanBasis 1) X) = 0
    apply ZornVectorMatrix.ext <;>
      simp [g2CartanBasis, InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation,
        InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterAction, ZornVectorMatrix.zero]
  · simp

theorem g2CartanBasis_linearIndependent : LinearIndependent ℝ g2CartanBasis := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hp : InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.symm
      (∑ i, c i • g2CartanBasis i) =
      c 0 • (fun i : Fin 14 => if i = 6 then (1 : ℝ) else 0) +
        c 1 • (fun i : Fin 14 => if i = 13 then (1 : ℝ) else 0) := by
    rw [map_sum, Fin.sum_univ_two, map_smul, map_smul]
    change c 0 • (InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv
          (fun i => if i = 6 then 1 else 0))) +
      c 1 • (InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv
          (fun i => if i = 13 then 1 else 0))) = _
    simp only [InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.symm_apply_apply]
  have h1 : (InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.symm
      (∑ i, c i • g2CartanBasis i)) 6 = 0 := by rw [hc, map_zero]; rfl
  have h2 : (InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.symm
      (∑ i, c i • g2CartanBasis i)) 13 = 0 := by rw [hc, map_zero]; rfl
  rw [hp] at h1 h2
  have hc0 : c 0 = 0 := by simpa using h1
  have hc1 : c 1 = 0 := by simpa using h2
  intro i; fin_cases i <;> assumption

private theorem h3_diag₁_eq_basis : h3_diag₁ = h3ZornBasis 0 := by
  apply h3ZornBasis.repr.injective
  ext r
  have hr : (h3ZornBasis.repr h3_diag₁) r = h3ZornCoordEquiv h3_diag₁ r :=
    Module.Basis.ofEquivFun_repr_apply h3ZornCoordEquiv h3_diag₁ r
  rw [hr, h3ZornBasis.repr_self, Finsupp.single_apply]
  fin_cases r <;>
    simp [h3ZornCoordEquiv, h3ZornCoordinateLM, h3ZornCoordinate, h3_diag₁, ZornVectorMatrix.zero]

private theorem h3_diag₂_eq_basis : h3_diag₂ = h3ZornBasis 1 := by
  apply h3ZornBasis.repr.injective
  ext r
  have hr : (h3ZornBasis.repr h3_diag₂) r = h3ZornCoordEquiv h3_diag₂ r :=
    Module.Basis.ofEquivFun_repr_apply h3ZornCoordEquiv h3_diag₂ r
  rw [hr, h3ZornBasis.repr_self, Finsupp.single_apply]
  fin_cases r <;>
    simp [h3ZornCoordEquiv, h3ZornCoordinateLM, h3ZornCoordinate, h3_diag₂, ZornVectorMatrix.zero]

private theorem h3_diag₃_eq_basis : h3_diag₃ = h3ZornBasis 2 := by
  apply h3ZornBasis.repr.injective
  ext r
  have hr : (h3ZornBasis.repr h3_diag₃) r = h3ZornCoordEquiv h3_diag₃ r :=
    Module.Basis.ofEquivFun_repr_apply h3ZornCoordEquiv h3_diag₃ r
  rw [hr, h3ZornBasis.repr_self, Finsupp.single_apply]
  fin_cases r <;>
    simp [h3ZornCoordEquiv, h3ZornCoordinateLM, h3ZornCoordinate, h3_diag₃, ZornVectorMatrix.zero]

private theorem h3_one_eq_basis_sum :
    (1 : H3Zorn ℝ) = h3ZornBasis 0 + h3ZornBasis 1 + h3ZornBasis 2 := by
  rw [← h3_diag₁_eq_basis, ← h3_diag₂_eq_basis, ← h3_diag₃_eq_basis]
  apply H3Zorn.ext_h3 <;>
    simp [h3_diag₁, h3_diag₂, h3_diag₃, one_readback, add_readback, ZornVectorMatrix.add_zero]

private theorem e6SimpleH_one_mem_f4 (i : Fin 6)
    (h0 : h3zornWeight 0 i = 0) (h1 : h3zornWeight 1 i = 0) (h2 : h3zornWeight 2 i = 0) :
    (e6SimpleH i : Module.End ℝ (H3Zorn ℝ)) ∈ H3ZornF4Derivations := by
  apply h3zorn_cubic_unit_stabilizer_le_F4
  refine ⟨(e6SimpleH i).2, ?_⟩
  change (e6SimpleH i : Module.End ℝ (H3Zorn ℝ)) (1 : H3Zorn ℝ) = 0
  rw [h3_one_eq_basis_sum, map_add, map_add, e6SimpleH_apply_basis, e6SimpleH_apply_basis,
    e6SimpleH_apply_basis, h0, h1, h2]
  simp

private theorem e6SimpleH_sum_mem_f4 (i j : Fin 6)
    (h0 : h3zornWeight 0 i + h3zornWeight 0 j = 0)
    (h1 : h3zornWeight 1 i + h3zornWeight 1 j = 0)
    (h2 : h3zornWeight 2 i + h3zornWeight 2 j = 0) :
    ((e6SimpleH i + e6SimpleH j : h3zornCubicStabilizer) : Module.End ℝ (H3Zorn ℝ)) ∈
      H3ZornF4Derivations := by
  apply h3zorn_cubic_unit_stabilizer_le_F4
  refine ⟨(e6SimpleH i + e6SimpleH j).2, ?_⟩
  change ((e6SimpleH i : Module.End ℝ (H3Zorn ℝ)) +
    (e6SimpleH j : Module.End ℝ (H3Zorn ℝ))) (1 : H3Zorn ℝ) = 0
  rw [LinearMap.add_apply, h3_one_eq_basis_sum, map_add, map_add, map_add, map_add,
    e6SimpleH_apply_basis, e6SimpleH_apply_basis, e6SimpleH_apply_basis,
    e6SimpleH_apply_basis, e6SimpleH_apply_basis, e6SimpleH_apply_basis]
  have hs (k : Fin 27) (hk : h3zornWeight k i + h3zornWeight k j = 0) :
      (h3zornWeight k i : ℝ) • h3ZornBasis k + (h3zornWeight k j : ℝ) • h3ZornBasis k = 0 := by
    rw [← add_smul, ← Int.cast_add, hk, Int.cast_zero, zero_smul]
  have h0' := hs 0 h0
  have h1' := hs 1 h1
  have h2' := hs 2 h2
  have hre :
      ((h3zornWeight 0 i : ℝ) • h3ZornBasis 0 + (h3zornWeight 1 i : ℝ) • h3ZornBasis 1 +
          (h3zornWeight 2 i : ℝ) • h3ZornBasis 2) +
        ((h3zornWeight 0 j : ℝ) • h3ZornBasis 0 + (h3zornWeight 1 j : ℝ) • h3ZornBasis 1 +
          (h3zornWeight 2 j : ℝ) • h3ZornBasis 2) =
      ((h3zornWeight 0 i : ℝ) • h3ZornBasis 0 + (h3zornWeight 0 j : ℝ) • h3ZornBasis 0) +
        ((h3zornWeight 1 i : ℝ) • h3ZornBasis 1 + (h3zornWeight 1 j : ℝ) • h3ZornBasis 1) +
        ((h3zornWeight 2 i : ℝ) • h3ZornBasis 2 + (h3zornWeight 2 j : ℝ) • h3ZornBasis 2) := by
    abel
  rw [hre, h0', h1', h2', add_zero, add_zero]

/-- Canonical 4D split Cartan basis of `F₄(4)` in `F4DerivationCarrier`:
`[e6SimpleH 1, e6SimpleH 3, e6SimpleH 0 + e6SimpleH 5, e6SimpleH 2 + e6SimpleH 4]`. -/
def f4CartanBasis : Fin 4 → F4DerivationCarrier
  | 0 => ⟨(e6SimpleH 1 : Module.End ℝ (H3Zorn ℝ)),
      e6SimpleH_one_mem_f4 1 (by decide) (by decide) (by decide)⟩
  | 1 => ⟨(e6SimpleH 3 : Module.End ℝ (H3Zorn ℝ)),
      e6SimpleH_one_mem_f4 3 (by decide) (by decide) (by decide)⟩
  | 2 => ⟨((e6SimpleH 0 + e6SimpleH 5 : h3zornCubicStabilizer) : Module.End ℝ (H3Zorn ℝ)),
      e6SimpleH_sum_mem_f4 0 5 (by decide) (by decide) (by decide)⟩
  | 3 => ⟨((e6SimpleH 2 + e6SimpleH 4 : h3zornCubicStabilizer) : Module.End ℝ (H3Zorn ℝ)),
      e6SimpleH_sum_mem_f4 2 4 (by decide) (by decide) (by decide)⟩

private theorem f4CartanBasis_coe_e6 (i : Fin 4) :
    (f4CartanBasis i : Module.End ℝ (H3Zorn ℝ)) =
      match i with
      | 0 => (e6SimpleH 1 : Module.End ℝ (H3Zorn ℝ))
      | 1 => (e6SimpleH 3 : Module.End ℝ (H3Zorn ℝ))
      | 2 => ((e6SimpleH 0 + e6SimpleH 5 : h3zornCubicStabilizer) : Module.End ℝ (H3Zorn ℝ))
      | 3 => ((e6SimpleH 2 + e6SimpleH 4 : h3zornCubicStabilizer) : Module.End ℝ (H3Zorn ℝ)) := by
  fin_cases i <;> rfl

theorem f4CartanBasis_comm (i j : Fin 4) :
    ⁅f4CartanBasis i, f4CartanBasis j⁆ = 0 := by
  apply Subtype.ext
  have hcomm_e6 (a b : h3zornCubicStabilizer) (h : ⁅a, b⁆ = 0) :
      ⁅(a : Module.End ℝ (H3Zorn ℝ)), (b : Module.End ℝ (H3Zorn ℝ))⁆ = 0 :=
    congrArg Subtype.val h
  fin_cases i <;> fin_cases j <;>
    simp only [f4CartanBasis, Submodule.coe_zero]
  all_goals
    change ⁅_, _⁆ = (0 : Module.End ℝ (H3Zorn ℝ))
  · exact hcomm_e6 _ _ (e6SimpleH_comm 1 1)
  · exact hcomm_e6 _ _ (e6SimpleH_comm 1 3)
  · rw [Submodule.coe_add, lie_add, hcomm_e6 _ _ (e6SimpleH_comm 1 0),
      hcomm_e6 _ _ (e6SimpleH_comm 1 5), add_zero]
  · rw [Submodule.coe_add, lie_add, hcomm_e6 _ _ (e6SimpleH_comm 1 2),
      hcomm_e6 _ _ (e6SimpleH_comm 1 4), add_zero]
  · exact hcomm_e6 _ _ (e6SimpleH_comm 3 1)
  · exact hcomm_e6 _ _ (e6SimpleH_comm 3 3)
  · rw [Submodule.coe_add, lie_add, hcomm_e6 _ _ (e6SimpleH_comm 3 0),
      hcomm_e6 _ _ (e6SimpleH_comm 3 5), add_zero]
  · rw [Submodule.coe_add, lie_add, hcomm_e6 _ _ (e6SimpleH_comm 3 2),
      hcomm_e6 _ _ (e6SimpleH_comm 3 4), add_zero]
  · rw [Submodule.coe_add, add_lie, hcomm_e6 _ _ (e6SimpleH_comm 0 1),
      hcomm_e6 _ _ (e6SimpleH_comm 5 1), add_zero]
  · rw [Submodule.coe_add, add_lie, hcomm_e6 _ _ (e6SimpleH_comm 0 3),
      hcomm_e6 _ _ (e6SimpleH_comm 5 3), add_zero]
  · rw [Submodule.coe_add, add_lie, lie_add, lie_add,
      hcomm_e6 _ _ (e6SimpleH_comm 0 0), hcomm_e6 _ _ (e6SimpleH_comm 0 5),
      hcomm_e6 _ _ (e6SimpleH_comm 5 0), hcomm_e6 _ _ (e6SimpleH_comm 5 5), add_zero, add_zero]
  · rw [Submodule.coe_add, Submodule.coe_add, add_lie, lie_add, lie_add,
      hcomm_e6 _ _ (e6SimpleH_comm 0 2), hcomm_e6 _ _ (e6SimpleH_comm 0 4),
      hcomm_e6 _ _ (e6SimpleH_comm 5 2), hcomm_e6 _ _ (e6SimpleH_comm 5 4), add_zero, add_zero]
  · rw [Submodule.coe_add, add_lie, hcomm_e6 _ _ (e6SimpleH_comm 2 1),
      hcomm_e6 _ _ (e6SimpleH_comm 4 1), add_zero]
  · rw [Submodule.coe_add, add_lie, hcomm_e6 _ _ (e6SimpleH_comm 2 3),
      hcomm_e6 _ _ (e6SimpleH_comm 4 3), add_zero]
  · rw [Submodule.coe_add, Submodule.coe_add, add_lie, lie_add, lie_add,
      hcomm_e6 _ _ (e6SimpleH_comm 2 0), hcomm_e6 _ _ (e6SimpleH_comm 2 5),
      hcomm_e6 _ _ (e6SimpleH_comm 4 0), hcomm_e6 _ _ (e6SimpleH_comm 4 5), add_zero, add_zero]
  · rw [Submodule.coe_add, add_lie, lie_add, lie_add,
      hcomm_e6 _ _ (e6SimpleH_comm 2 2), hcomm_e6 _ _ (e6SimpleH_comm 2 4),
      hcomm_e6 _ _ (e6SimpleH_comm 4 2), hcomm_e6 _ _ (e6SimpleH_comm 4 4), add_zero, add_zero]

theorem f4CartanBasis_linearIndependent : LinearIndependent ℝ f4CartanBasis := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc_e6 :
      c 2 • e6SimpleH 0 + c 0 • e6SimpleH 1 + c 3 • e6SimpleH 2 +
      c 1 • e6SimpleH 3 + c 3 • e6SimpleH 4 + c 2 • e6SimpleH 5 = 0 := by
    apply Subtype.ext
    have hval := congrArg (fun D : F4DerivationCarrier => (D : Module.End ℝ (H3Zorn ℝ))) hc
    simp only [Fin.sum_univ_four, f4CartanBasis] at hval ⊢
    change c 2 • (e6SimpleH 0 : Module.End ℝ (H3Zorn ℝ)) +
        c 0 • (e6SimpleH 1 : Module.End ℝ (H3Zorn ℝ)) +
        c 3 • (e6SimpleH 2 : Module.End ℝ (H3Zorn ℝ)) +
        c 1 • (e6SimpleH 3 : Module.End ℝ (H3Zorn ℝ)) +
        c 3 • (e6SimpleH 4 : Module.End ℝ (H3Zorn ℝ)) +
        c 2 • (e6SimpleH 5 : Module.End ℝ (H3Zorn ℝ)) = 0
    have hval' :
        c 0 • (e6SimpleH 1 : Module.End ℝ (H3Zorn ℝ)) +
          c 1 • (e6SimpleH 3 : Module.End ℝ (H3Zorn ℝ)) +
          c 2 • ((e6SimpleH 0 : Module.End ℝ (H3Zorn ℝ)) +
            (e6SimpleH 5 : Module.End ℝ (H3Zorn ℝ))) +
          c 3 • ((e6SimpleH 2 : Module.End ℝ (H3Zorn ℝ)) +
            (e6SimpleH 4 : Module.End ℝ (H3Zorn ℝ))) = 0 := by
      simpa [Submodule.coe_add, SetLike.val_smul, Submodule.coe_zero] using hval
    rw [smul_add, smul_add] at hval'
    rw [← hval']
    abel
  have hlin := Fintype.linearIndependent_iff.mp e6SimpleH_linearIndependent
    (fun k : Fin 6 => match k with
      | 0 => c 2 | 1 => c 0 | 2 => c 3 | 3 => c 1 | 4 => c 3 | 5 => c 2)
    (by simpa [Fin.sum_univ_six, add_assoc] using hc_e6)
  intro i
  fin_cases i
  · exact hlin 1
  · exact hlin 3
  · exact hlin 0
  · exact hlin 2

/-- Integer weight of `f4CartanBasis i` on `h3ZornBasis k`. -/
def f4CartanWeight (k : Fin 27) (i : Fin 4) : ℤ :=
  match i with
  | 0 => h3zornWeight k 1
  | 1 => h3zornWeight k 3
  | 2 => h3zornWeight k 0 + h3zornWeight k 5
  | 3 => h3zornWeight k 2 + h3zornWeight k 4

theorem f4CartanBasis_apply_basis (i : Fin 4) (k : Fin 27) :
    (f4CartanBasis i : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis k) =
      (f4CartanWeight k i : ℝ) • h3ZornBasis k := by
  fin_cases i
  · exact e6SimpleH_apply_basis 1 k
  · exact e6SimpleH_apply_basis 3 k
  · change ((e6SimpleH 0 : Module.End ℝ (H3Zorn ℝ)) +
      (e6SimpleH 5 : Module.End ℝ (H3Zorn ℝ))) (h3ZornBasis k) = _
    dsimp only [f4CartanWeight]
    rw [LinearMap.add_apply, e6SimpleH_apply_basis, e6SimpleH_apply_basis, Int.cast_add, add_smul]
  · change ((e6SimpleH 2 : Module.End ℝ (H3Zorn ℝ)) +
      (e6SimpleH 4 : Module.End ℝ (H3Zorn ℝ))) (h3ZornBasis k) = _
    dsimp only [f4CartanWeight]
    rw [LinearMap.add_apply, e6SimpleH_apply_basis, e6SimpleH_apply_basis, Int.cast_add, add_smul]

theorem f4CartanBasis_apply_diag₁ (i : Fin 4) :
    (f4CartanBasis i : Module.End ℝ (H3Zorn ℝ)) h3_diag₁ = 0 := by
  have hw : f4CartanWeight 0 i = 0 := by fin_cases i <;> decide
  rw [h3_diag₁_eq_basis, f4CartanBasis_apply_basis, hw, Int.cast_zero, zero_smul]

theorem f4CartanBasis_apply_diag₂ (i : Fin 4) :
    (f4CartanBasis i : Module.End ℝ (H3Zorn ℝ)) h3_diag₂ = 0 := by
  have hw : f4CartanWeight 1 i = 0 := by fin_cases i <;> decide
  rw [h3_diag₂_eq_basis, f4CartanBasis_apply_basis, hw, Int.cast_zero, zero_smul]

theorem f4CartanBasis_apply_diag₃ (i : Fin 4) :
    (f4CartanBasis i : Module.End ℝ (H3Zorn ℝ)) h3_diag₃ = 0 := by
  have hw : f4CartanWeight 2 i = 0 := by fin_cases i <;> decide
  rw [h3_diag₃_eq_basis, f4CartanBasis_apply_basis, hw, Int.cast_zero, zero_smul]

theorem f4CartanBasis_apply_h3DiagZero₁ (i : Fin 4) :
    f4Act (f4CartanBasis i) h3DiagZero₁ = 0 := by
  apply Subtype.ext
  simp [f4Act_coe, h3DiagZero₁_coe, f4CartanBasis_apply_diag₁, f4CartanBasis_apply_diag₂]

theorem f4CartanBasis_apply_h3DiagZero₂ (i : Fin 4) :
    f4Act (f4CartanBasis i) h3DiagZero₂ = 0 := by
  apply Subtype.ext
  simp [f4Act_coe, h3DiagZero₂_coe, f4CartanBasis_apply_diag₂, f4CartanBasis_apply_diag₃]

end ConcreteElementsAndCartan

end InfoGeometry.Algebra.MagicSquareTitsBracket

end noncomputable section
