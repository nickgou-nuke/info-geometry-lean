/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Canonical.PeirceModularBridge
import InfoGeometry.Canonical.IntegralModularShears
import InfoGeometry.Core.JordanMultiplicationClosure
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Meta.EpistemicCompilerChain
import InfoGeometry.Meta.MetaEpistemicCompiler

/-!
# CAPA-Decomposed Modular Parabolic–Cyclotomic, Left-Multiplication Jordan Lift, and Nambu Defect Synthesis

This module formalizes **Stream 4** under the `QMS-SOP-IAA-001` / OpenGauss protocol,
where every theorem is decomposed into consumer-minimal atomic lemmas (`< 20` lines each),
accompanied by non-vacuity matrix witnesses, refutation boundaries, and a 4-node diamond
causal poset (`ModularParabolicNambuArchetype`) certified by the Lean 4 Meta Epistemic Compiler:

1. **Node 0 (`rootPairParabolicSeed`)**:
   Dual roots of zero `(d, B)` (`d² = 0`, `B² = 0`, `d B d = d`, `B d B = B`), opposite
   parabolic shears `1 + d` and `1 - B` with two-sided inverses `(1 + d)(1 - d) = 1` and
   `(1 - B)(1 + B) = 1`, simplex poles `P₊ = d B`, `P₋ = B d`, active support `Δ = P₊ + P₋`,
   harmonic zero-mode `P₀ = 1 - Δ`, and the central-on-subgroup sign involution `P₀ - Δ`
   satisfying `(P₀ - Δ)² = 1`.
2. **Node 1 (`doubleShearHexality`)**:
   Double parabolic shear `Λ₆ = (1 + d)(1 - B)` and its reverse-order inverse
   `Λ₆⁻¹ = (1 + B)(1 - d)`, proving `Λ₆ * Λ₆⁻¹ = 1`, `Λ₆⁻¹ * Λ₆ = 1`,
   `Λ₆ + Λ₆⁻¹ = 2 • P₀ + Δ`, the exact harmonic defect `Λ₆² - Λ₆ + 1 = P₀`,
   `Λ₆³ = P₀ - Δ`, and `Λ₆⁶ = 1`.
3. **Node 2 (`tripleShearBruhatQuartic`)**:
   Triple parabolic shear `w_J = (1 + d)(1 - B)(1 + d) = P₀ + (d - B)` and its inverse
   `w_J⁻¹ = (1 - d)(1 + B)(1 - d)`, proving `w_J * w_J⁻¹ = 1`, `w_J² = P₀ - Δ`,
   `w_J⁴ = 1`, the braid identity `(1 + d)(1 - B)(1 + d) = (1 - B)(1 + d)(1 - B)`,
   and pole conjugation `w_J P₊ w_J⁻¹ = P₋`.
4. **Node 3 (`modularCenterAndNambuSynthesis`)**:
   - The universal modular relation `w_J² = Λ₆³ = P₀ - Δ`, bridged to the native
     `PresentedGroup` homomorphism `ParabolicModularRepresentation.representation : ModularRelationsGroup →* Aˣ`
     and surjective `SL(2, ℤ)` representation `IntegralModularShears.integralRepresentation_surjective`.
   - Left-multiplication Jordan lift `L_X(Y) = X ∘ Y = X Y + Y X` in `Module.End R A`,
     associative Jordan multiplication closure `[L_X, L_Y](Z) = [[X, Y], Z]`, and the
     antisymmetric Nambu 3-bracket decomposition
     `Nambu3(X, Y, Z) = [X, Y] Z + [Y, Z] X + [Z, X] Y`.
   - Refutation boundary `parabolic_shears_commute_iff_poles_eq` proving
     `(1 + d)(1 - B) = (1 - B)(1 + d) ↔ P₊ = P₋`, together with a concrete `Matrix (Fin 2) (Fin 2) ℤ`
     non-commuting witness.
-/

namespace InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis

open Matrix

section UniversalRingLayer

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

/-!
## 1. Core Definitions: Dual Roots of Zero, Simplex Poles, Parabolic Shears, & Nambu 3-Bracket
-/

/-- Symmetrized Jordan anticommutator `{X, Y} = X Y + Y X`. -/
def jordanProd (X Y : A) : A := X * Y + Y * X

/-- Antisymmetric Lie commutator `[X, Y] = X Y - Y X`. -/
def lieBracket (X Y : A) : A := X * Y - Y * X

/-- Associative Nambu 3-bracket (cyclic commutator sum)
    `[X, Y, Z]_Nambu = [X, Y] Z + [Y, Z] X + [Z, X] Y`. -/
def nambuTripleBracket (X Y Z : A) : A :=
  lieBracket X Y * Z + lieBracket Y Z * X + lieBracket Z X * Y

/-- Reflexive square-zero pair `(d, B)`: two dual roots of zero (`d² = 0`, `B² = 0`)
    forming a partial isomorphism (`d B d = d`, `B d B = B`). -/
structure IsDualRootOfZeroPair (d B : A) : Prop where
  d_sq : d * d = 0
  B_sq : B * B = 0
  dBd : d * B * d = d
  BdB : B * d * B = B

/-- Infinity-pole idempotent `P₊ = d B`. -/
def polePlus (d B : A) : A := d * B

/-- Zero-pole idempotent `P₋ = B d`. -/
def poleMinus (d B : A) : A := B * d

/-- Active 2-pole support idempotent `Δ = P₊ + P₋`. -/
def activeSupport (d B : A) : A := polePlus d B + poleMinus d B

/-- Harmonic zero-mode idempotent `P₀ = 1 - Δ`. -/
def poleZeroMode (d B : A) : A := 1 - activeSupport d B

/-- Double parabolic shear product `Λ₆ = (1 + d) * (1 - B)`. -/
def parabolicHexalityOp (d B : A) : A := (1 + d) * (1 - B)

/-- Inverse double parabolic shear product `Λ₆⁻¹ = (1 + B) * (1 - d)`. -/
def parabolicHexalityOpInv (d B : A) : A := (1 + B) * (1 - d)

/-- Triple parabolic shear product `w_J = (1 + d) * (1 - B) * (1 + d)`. -/
def bruhatQuarticOp (d B : A) : A := (1 + d) * (1 - B) * (1 + d)

/-- Inverse triple parabolic shear product `w_J⁻¹ = (1 - d) * (1 + B) * (1 - d)`. -/
def bruhatQuarticOpInv (d B : A) : A := (1 - d) * (1 + B) * (1 - d)

/-!
## 2. Node 0 Atomic Lemmas: Peirce Absorption & Parabolic Unipotent Inverses
-/

lemma one_add_mul_one_sub_of_sq_zero {x : A} (hx : x * x = 0) :
    (1 + x) * (1 - x) = 1 := by
  calc (1 + x) * (1 - x) = 1 - x * x := by noncomm_ring
    _ = 1 := by rw [hx, sub_zero]

lemma one_sub_mul_one_add_of_sq_zero {x : A} (hx : x * x = 0) :
    (1 - x) * (1 + x) = 1 := by
  calc (1 - x) * (1 + x) = 1 - x * x := by noncomm_ring
    _ = 1 := by rw [hx, sub_zero]

lemma polePlus_idem {d B : A} (h : IsDualRootOfZeroPair d B) :
    polePlus d B * polePlus d B = polePlus d B := by
  unfold polePlus
  calc (d * B) * (d * B) = (d * B * d) * B := by noncomm_ring
    _ = d * B := by rw [h.dBd]

lemma poleMinus_idem {d B : A} (h : IsDualRootOfZeroPair d B) :
    poleMinus d B * poleMinus d B = poleMinus d B := by
  unfold poleMinus
  calc (B * d) * (B * d) = (B * d * B) * d := by noncomm_ring
    _ = B * d := by rw [h.BdB]

lemma polePlus_mul_poleMinus {d B : A} (h : IsDualRootOfZeroPair d B) :
    polePlus d B * poleMinus d B = 0 := by
  unfold polePlus poleMinus
  calc (d * B) * (B * d) = d * (B * B) * d := by noncomm_ring
    _ = 0 := by rw [h.B_sq, mul_zero, zero_mul]

lemma poleMinus_mul_polePlus {d B : A} (h : IsDualRootOfZeroPair d B) :
    poleMinus d B * polePlus d B = 0 := by
  unfold poleMinus polePlus
  calc (B * d) * (d * B) = B * (d * d) * B := by noncomm_ring
    _ = 0 := by rw [h.d_sq, mul_zero, zero_mul]

lemma activeSupport_idem {d B : A} (h : IsDualRootOfZeroPair d B) :
    activeSupport d B * activeSupport d B = activeSupport d B := by
  unfold activeSupport
  rw [add_mul, mul_add, mul_add, polePlus_idem h, polePlus_mul_poleMinus h,
      poleMinus_mul_polePlus h, poleMinus_idem h, add_zero, zero_add]

lemma poleZeroMode_idem {d B : A} (h : IsDualRootOfZeroPair d B) :
    poleZeroMode d B * poleZeroMode d B = poleZeroMode d B := by
  unfold poleZeroMode
  calc (1 - activeSupport d B) * (1 - activeSupport d B)
    _ = 1 - 2 • activeSupport d B + activeSupport d B * activeSupport d B := by noncomm_ring
    _ = 1 - activeSupport d B := by rw [activeSupport_idem h]; abel

lemma centerInvolution_sq_one {d B : A} (h : IsDualRootOfZeroPair d B) :
    (poleZeroMode d B - activeSupport d B) * (poleZeroMode d B - activeSupport d B) = 1 := by
  unfold poleZeroMode
  calc (1 - activeSupport d B - activeSupport d B) *
       (1 - activeSupport d B - activeSupport d B)
    _ = 1 - 4 • activeSupport d B + 4 • (activeSupport d B * activeSupport d B) := by
        noncomm_ring
    _ = 1 := by rw [activeSupport_idem h]; abel

/-!
## 3. Node 1 Atomic Lemmas: Double Shear Hexality `Λ₆ = (1 + d)(1 - B)`
-/

lemma parabolicHexalityOp_mul_inv {d B : A} (h : IsDualRootOfZeroPair d B) :
    parabolicHexalityOp d B * parabolicHexalityOpInv d B = 1 := by
  exact (InfoGeometry.Core.ParabolicShearRelations.double_inverse h.d_sq h.B_sq).1

lemma parabolicHexalityOpInv_mul {d B : A} (h : IsDualRootOfZeroPair d B) :
    parabolicHexalityOpInv d B * parabolicHexalityOp d B = 1 := by
  exact (InfoGeometry.Core.ParabolicShearRelations.double_inverse h.d_sq h.B_sq).2

lemma parabolicHexalityOp_add_inv (d B : A) :
    parabolicHexalityOp d B + parabolicHexalityOpInv d B =
      2 • poleZeroMode d B + activeSupport d B := by
  exact InfoGeometry.Core.ParabolicShearRelations.double_inverse_sum d B

lemma parabolicHexalityOp_sq {d B : A} (h : IsDualRootOfZeroPair d B) :
    parabolicHexalityOp d B * parabolicHexalityOp d B =
      poleZeroMode d B + d - B - polePlus d B := by
  have hdq :=
    InfoGeometry.Core.ParabolicShearRelations.double_quadratic_defect
      h.d_sq h.B_sq h.dBd h.BdB
  calc parabolicHexalityOp d B * parabolicHexalityOp d B
    _ = (InfoGeometry.Core.ParabolicShearRelations.doubleShear d B *
         InfoGeometry.Core.ParabolicShearRelations.doubleShear d B -
         InfoGeometry.Core.ParabolicShearRelations.doubleShear d B + 1) +
        InfoGeometry.Core.ParabolicShearRelations.doubleShear d B - 1 := by
        unfold parabolicHexalityOp InfoGeometry.Core.ParabolicShearRelations.doubleShear
        noncomm_ring
    _ = poleZeroMode d B + d - B - polePlus d B := by
        rw [hdq]
        unfold InfoGeometry.Core.ParabolicShearRelations.doubleShear
          poleZeroMode activeSupport polePlus poleMinus
        noncomm_ring

lemma parabolicHexalityOp_quadratic_defect {d B : A} (h : IsDualRootOfZeroPair d B) :
    parabolicHexalityOp d B * parabolicHexalityOp d B - parabolicHexalityOp d B + 1 =
      poleZeroMode d B := by
  exact InfoGeometry.Core.ParabolicShearRelations.double_quadratic_defect
    h.d_sq h.B_sq h.dBd h.BdB

lemma parabolicHexalityOp_cube {d B : A} (h : IsDualRootOfZeroPair d B) :
    parabolicHexalityOp d B ^ 3 = poleZeroMode d B - activeSupport d B := by
  exact InfoGeometry.Core.ParabolicShearRelations.double_cube
    h.d_sq h.B_sq h.dBd h.BdB

lemma parabolicHexalityOp_pow_six {d B : A} (h : IsDualRootOfZeroPair d B) :
    parabolicHexalityOp d B ^ 6 = 1 := by
  exact (InfoGeometry.Core.ParabolicShearRelations.power_relations
    h.d_sq h.B_sq h.dBd h.BdB).2.1

/-!
## 4. Node 2 Atomic Lemmas: Triple Shear Bruhat Quartic `w_J = (1 + d)(1 - B)(1 + d)`
-/

lemma bruhatQuarticOp_eq_zeroMode_add_sub {d B : A} (h : IsDualRootOfZeroPair d B) :
    bruhatQuarticOp d B = poleZeroMode d B + (d - B) := by
  exact InfoGeometry.Core.ParabolicShearRelations.triple_expansion h.d_sq h.dBd

lemma bruhatQuarticOp_braid {d B : A} (h : IsDualRootOfZeroPair d B) :
    (1 + d) * (1 - B) * (1 + d) = (1 - B) * (1 + d) * (1 - B) := by
  exact InfoGeometry.Core.ParabolicShearRelations.shear_braid
    h.d_sq h.B_sq h.dBd h.BdB

lemma bruhatQuarticOp_mul_inv {d B : A} (h : IsDualRootOfZeroPair d B) :
    bruhatQuarticOp d B * bruhatQuarticOpInv d B = 1 := by
  unfold bruhatQuarticOp bruhatQuarticOpInv
  calc ((1 + d) * (1 - B) * (1 + d)) * ((1 - d) * (1 + B) * (1 - d))
    _ = (1 + d) * (1 - B) * ((1 + d) * (1 - d)) * (1 + B) * (1 - d) := by simp only [mul_assoc]
    _ = ((1 + d) * (1 - B)) * ((1 + B) * (1 - d)) := by
        rw [one_add_mul_one_sub_of_sq_zero h.d_sq, mul_one]; simp only [mul_assoc]
    _ = 1 := parabolicHexalityOp_mul_inv h

lemma hodgeDiff_sq {d B : A} (h : IsDualRootOfZeroPair d B) :
    (d - B) * (d - B) = -activeSupport d B := by
  unfold activeSupport polePlus poleMinus
  calc (d - B) * (d - B) = d * d - (d * B + B * d) + B * B := by noncomm_ring
    _ = -(d * B + B * d) := by rw [h.d_sq, h.B_sq]; abel

lemma poleZeroMode_mul_hodgeDiff {d B : A} (h : IsDualRootOfZeroPair d B) :
    poleZeroMode d B * (d - B) = 0 := by
  have hd_dB : (d * B) * d = d := h.dBd
  have hBd_d : (B * d) * d = 0 := by rw [mul_assoc, h.d_sq, mul_zero]
  have hdB_B : (d * B) * B = 0 := by rw [mul_assoc, h.B_sq, mul_zero]
  have hBd_B : (B * d) * B = B := h.BdB
  unfold poleZeroMode activeSupport polePlus poleMinus
  calc (1 - (d * B + B * d)) * (d - B)
    _ = (d - (d * B) * d - (B * d) * d) - (B - (d * B) * B - (B * d) * B) := by noncomm_ring
    _ = 0 := by rw [hd_dB, hBd_d, hdB_B, hBd_B]; abel

lemma hodgeDiff_mul_poleZeroMode {d B : A} (h : IsDualRootOfZeroPair d B) :
    (d - B) * poleZeroMode d B = 0 := by
  have hd_dB : d * (d * B) = 0 := by rw [← mul_assoc, h.d_sq, zero_mul]
  have hd_Bd : d * (B * d) = d := by rw [← mul_assoc, h.dBd]
  have hB_dB : B * (d * B) = B := by rw [← mul_assoc, h.BdB]
  have hB_Bd : B * (B * d) = 0 := by rw [← mul_assoc, h.B_sq, zero_mul]
  unfold poleZeroMode activeSupport polePlus poleMinus
  calc (d - B) * (1 - (d * B + B * d))
    _ = (d - d * (d * B) - d * (B * d)) - (B - B * (d * B) - B * (B * d)) := by noncomm_ring
    _ = 0 := by rw [hd_dB, hd_Bd, hB_dB, hB_Bd]; abel

lemma bruhatQuarticOp_sq {d B : A} (h : IsDualRootOfZeroPair d B) :
    bruhatQuarticOp d B * bruhatQuarticOp d B =
      poleZeroMode d B - activeSupport d B := by
  rw [bruhatQuarticOp_eq_zeroMode_add_sub h]
  calc (poleZeroMode d B + (d - B)) * (poleZeroMode d B + (d - B))
    _ = poleZeroMode d B * poleZeroMode d B + poleZeroMode d B * (d - B) +
        (d - B) * poleZeroMode d B + (d - B) * (d - B) := by noncomm_ring
    _ = poleZeroMode d B - activeSupport d B := by
        rw [poleZeroMode_idem h, poleZeroMode_mul_hodgeDiff h,
            hodgeDiff_mul_poleZeroMode h, hodgeDiff_sq h]
        abel

lemma bruhatQuarticOp_pow_four {d B : A} (h : IsDualRootOfZeroPair d B) :
    bruhatQuarticOp d B ^ 4 = 1 := by
  exact (InfoGeometry.Core.ParabolicShearRelations.power_relations
    h.d_sq h.B_sq h.dBd h.BdB).1

lemma bruhatQuarticOpInv_eq_zeroMode_sub_sub {d B : A} (h : IsDualRootOfZeroPair d B) :
    bruhatQuarticOpInv d B = poleZeroMode d B - (d - B) := by
  have h_neg : (-d) * (-B) * (-d) = -d := by
    calc (-d) * (-B) * (-d) = -(d * B * d) := by noncomm_ring
      _ = -d := by rw [h.dBd]
  have h_exp := InfoGeometry.Core.ParabolicShearRelations.triple_expansion
    (d := -d) (b := -B) (by noncomm_ring [h.d_sq]) h_neg
  unfold bruhatQuarticOpInv poleZeroMode activeSupport polePlus poleMinus
  calc (1 - d) * (1 + B) * (1 - d)
    _ = InfoGeometry.Core.ParabolicShearRelations.tripleShear (-d) (-B) := by
        unfold InfoGeometry.Core.ParabolicShearRelations.tripleShear
          InfoGeometry.Core.ParabolicShearRelations.doubleShear
        noncomm_ring
    _ = 1 - (d * B + B * d) - (d - B) := by rw [h_exp]; noncomm_ring

lemma bruhatQuarticOp_mul_polePlus {d B : A} (h : IsDualRootOfZeroPair d B) :
    bruhatQuarticOp d B * polePlus d B = -B := by
  have hd_dB : d * (d * B) = 0 := by rw [← mul_assoc, h.d_sq, zero_mul]
  have hB_dB : B * (d * B) = B := by rw [← mul_assoc, h.BdB]
  have hdB_dB : (d * B) * (d * B) = d * B := polePlus_idem h
  rw [bruhatQuarticOp_eq_zeroMode_add_sub h]
  unfold poleZeroMode activeSupport polePlus poleMinus
  calc (1 - (d * B + B * d) + (d - B)) * (d * B)
    _ = (d * B - (d * B) * (d * B)) - B * (d * (d * B)) + d * (d * B) - B * (d * B) := by
        noncomm_ring
    _ = -B := by rw [hdB_dB, hd_dB, hB_dB, mul_zero]; abel

lemma bruhatQuarticOp_conj_polePlus {d B : A} (h : IsDualRootOfZeroPair d B) :
    bruhatQuarticOp d B * polePlus d B * bruhatQuarticOpInv d B = poleMinus d B := by
  have hB_dB : B * (d * B) = B := by rw [← mul_assoc, h.BdB]
  have hB_Bd : B * (B * d) = 0 := by rw [← mul_assoc, h.B_sq, zero_mul]
  rw [bruhatQuarticOp_mul_polePlus h, bruhatQuarticOpInv_eq_zeroMode_sub_sub h]
  unfold poleZeroMode activeSupport polePlus poleMinus
  calc (-B) * (1 - (d * B + B * d) - (d - B))
    _ = B * d - (B - B * (d * B)) + B * (B * d) - B * B := by noncomm_ring
    _ = B * d := by rw [hB_dB, hB_Bd, h.B_sq]; abel

/-!
## 5. Node 3: Left-Multiplication Jordan Lift, Nambu 3-Bracket, Refutation Boundary & Synthesis
-/

/-- Left-multiplication Jordan operator `L_X(Y) = X Y + Y X` in `Module.End R A` satisfies
    the commutator-derivation law `[L_X, L_Y](Z) = [[X, Y], Z]`. -/
lemma jordanLeft_commutator_eq_lieBracket (X Y Z : A) :
    (InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) X *
       InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) Y -
     InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) Y *
       InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := R) X) Z =
      lieBracket (lieBracket X Y) Z := by
  rw [InfoGeometry.Core.JordanMultiplicationClosure.commutator_apply]
  rfl

/-- Pauli exclusion / cyclic Nambu vanishing `[X, Y, X]_Nambu = 0` for any elements `X, Y : A`. -/
lemma nambuTripleBracket_self_vanish (X Y : A) :
    nambuTripleBracket X Y X = 0 := by
  unfold nambuTripleBracket lieBracket
  noncomm_ring

/-- **Refutation Boundary (`parabolic_shears_commute_iff_poles_eq`)**:
    The upper parabolic shear `1 + d` and lower parabolic shear `1 - B` commute
    (`(1 + d)(1 - B) = (1 - B)(1 + d)`) if and only if the infinity pole `P₊ = d B`
    equals the zero pole `P₋ = B d`. -/
theorem parabolic_shears_commute_iff_poles_eq (d B : A) :
    (1 + d) * (1 - B) = (1 - B) * (1 + d) ↔ polePlus d B = poleMinus d B := by
  unfold polePlus poleMinus
  have h_diff : (1 + d) * (1 - B) - (1 - B) * (1 + d) = B * d - d * B := by noncomm_ring
  constructor
  · intro h_eq
    have h_zero : B * d - d * B = 0 := by rw [← h_diff, h_eq, sub_self]
    exact (sub_eq_zero.mp h_zero).symm
  · intro h_poles
    have h_zero : (1 + d) * (1 - B) - (1 - B) * (1 + d) = 0 := by
      rw [h_diff, h_poles, sub_self]
    exact sub_eq_zero.mp h_zero

/-- **Master Parabolic-to-Cyclotomic Modular Theorem (`parabolic_shears_generate_modular_cyclotomics`)**:
    Combines Node 0, Node 1, and Node 2 into the universal modular group relations
    `w_J² = Λ₆³ = P₀ - Δ`, `w_J⁴ = 1`, `Λ₆⁶ = 1`, `Λ₆² - Λ₆ + 1 = P₀`, and `w_J P₊ w_J⁻¹ = P₋`. -/
theorem parabolic_shears_generate_modular_cyclotomics {d B : A}
    (h : IsDualRootOfZeroPair d B) :
    let Δ := activeSupport d B
    let P_0 := poleZeroMode d B
    let Λ₆ := parabolicHexalityOp d B
    let Λ₆_inv := parabolicHexalityOpInv d B
    let w_J := bruhatQuarticOp d B
    let w_J_inv := bruhatQuarticOpInv d B
    (Λ₆ * Λ₆_inv = 1 ∧ Λ₆_inv * Λ₆ = 1 ∧ w_J * w_J_inv = 1) ∧
    (Λ₆ + Λ₆_inv = 2 • P_0 + Δ ∧ Λ₆ * Λ₆ - Λ₆ + 1 = P_0) ∧
    (w_J * w_J = P_0 - Δ ∧ Λ₆ ^ 3 = P_0 - Δ ∧ w_J * w_J = Λ₆ ^ 3) ∧
    (w_J ^ 4 = 1 ∧ Λ₆ ^ 6 = 1 ∧ w_J * polePlus d B * w_J_inv = poleMinus d B) := by
  intro Δ P_0 Λ₆ Λ₆_inv w_J w_J_inv
  have h_wJ2 := bruhatQuarticOp_sq h
  have h_L63 := parabolicHexalityOp_cube h
  exact ⟨⟨parabolicHexalityOp_mul_inv h, parabolicHexalityOpInv_mul h,
          bruhatQuarticOp_mul_inv h⟩,
         ⟨parabolicHexalityOp_add_inv d B, parabolicHexalityOp_quadratic_defect h⟩,
         ⟨h_wJ2, h_L63, by rw [h_wJ2, h_L63]⟩,
         ⟨bruhatQuarticOp_pow_four h, parabolicHexalityOp_pow_six h,
          bruhatQuarticOp_conj_polePlus h⟩⟩

end UniversalRingLayer

/-!
## 6. Concrete Noncommutative Matrix Witness & `SL(2, ℤ)` Modular Bridge
-/

section ConcreteMatrixWitness

abbrev Mat2Z := Matrix (Fin 2) (Fin 2) ℤ

/-- Upper nilpotent root of zero `d₂ = E₀₁` in `Matrix (Fin 2) (Fin 2) ℤ`. -/
def matD2 : Mat2Z := !![0, 1; 0, 0]

/-- Lower nilpotent root of zero `B₂ = E₁₀` in `Matrix (Fin 2) (Fin 2) ℤ`. -/
def matB2 : Mat2Z := !![0, 0; 1, 0]

lemma mat2Z_isDualRootOfZeroPair : IsDualRootOfZeroPair matD2 matB2 where
  d_sq := by decide
  B_sq := by decide
  dBd := by decide
  BdB := by decide

/-- Concrete non-vacuity and refutation-boundary witness in `Matrix (Fin 2) (Fin 2) ℤ`:
    `(1 + d₂)(1 - B₂) ≠ (1 - B₂)(1 + d₂)`, `w_J² = Λ₆³ = -1`, `w_J⁴ = 1`, `Λ₆⁶ = 1`,
    and the native `SL(2, ℤ)` representation `IntegralModularShears.integralRepresentation`
    is surjective with `Subgroup.closure {S, U} = ⊤`. -/
theorem mat2Z_parabolic_shears_noncommuting_witness :
    (1 + matD2) * (1 - matB2) ≠ (1 - matB2) * (1 + matD2) ∧
    polePlus matD2 matB2 ≠ poleMinus matD2 matB2 ∧
    bruhatQuarticOp matD2 matB2 * bruhatQuarticOp matD2 matB2 =
      parabolicHexalityOp matD2 matB2 ^ 3 ∧
    bruhatQuarticOp matD2 matB2 ^ 4 = (1 : Mat2Z) ∧
    parabolicHexalityOp matD2 matB2 ^ 6 = (1 : Mat2Z) ∧
    Subgroup.closure
      ({InfoGeometry.Canonical.IntegralModularShears.S,
        InfoGeometry.Canonical.IntegralModularShears.U} :
        Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) = ⊤ ∧
    Function.Surjective InfoGeometry.Canonical.IntegralModularShears.integralRepresentation :=
  ⟨by decide, by decide, by decide, by decide, by decide,
   InfoGeometry.Canonical.IntegralModularShears.integral_generators,
   InfoGeometry.Canonical.IntegralModularShears.integralRepresentation_surjective⟩

end ConcreteMatrixWitness

/-!
## 7. Diamond Causal Poset (`ModularParabolicNambuArchetype`) & Meta Epistemic Compiler Certification
-/

section MetaEpistemicCompilerCertification

open InfoGeometry.MetaCompiler
open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.ProofCarryingSchedule
open InfoGeometry.Causal.CertifiedDependencyCompiler

/-- The 4-node diamond causal poset of Stream 4. -/
inductive ModularParabolicNambuArchetype where
  | rootPairParabolicSeed
  | doubleShearHexality
  | tripleShearBruhatQuartic
  | modularCenterAndNambuSynthesis
  deriving DecidableEq, Repr, Inhabited

namespace ModularParabolicNambuArchetype

private def equivFin : ModularParabolicNambuArchetype ≃ Fin 4 where
  toFun
    | .rootPairParabolicSeed => 0
    | .doubleShearHexality => 1
    | .tripleShearBruhatQuartic => 2
    | .modularCenterAndNambuSynthesis => 3
  invFun
    | 0 => .rootPairParabolicSeed
    | 1 => .doubleShearHexality
    | 2 => .tripleShearBruhatQuartic
    | _ => .modularCenterAndNambuSynthesis
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance instFintype : Fintype ModularParabolicNambuArchetype :=
  Fintype.ofEquiv (Fin 4) equivFin.symm

/-- Diamond prerequisite map:
    - `rootPairParabolicSeed` is the root (Node 0)
    - `doubleShearHexality` (Node 1) and `tripleShearBruhatQuartic` (Node 2) are incomparable branches above Node 0
    - `modularCenterAndNambuSynthesis` (Node 3) joins Node 1 and Node 2. -/
def prerequisites : ModularParabolicNambuArchetype → Finset ModularParabolicNambuArchetype
  | .rootPairParabolicSeed => {.rootPairParabolicSeed}
  | .doubleShearHexality => {.rootPairParabolicSeed, .doubleShearHexality}
  | .tripleShearBruhatQuartic => {.rootPairParabolicSeed, .tripleShearBruhatQuartic}
  | .modularCenterAndNambuSynthesis =>
      {.rootPairParabolicSeed, .doubleShearHexality,
       .tripleShearBruhatQuartic, .modularCenterAndNambuSynthesis}

instance instPartialOrder : PartialOrder ModularParabolicNambuArchetype where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro a b
    cases a <;> cases b <;> decide

instance instDecidableLE : DecidableLE ModularParabolicNambuArchetype := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

instance instDecidableLT : DecidableLT ModularParabolicNambuArchetype := fun a b =>
  decidable_of_iff (a ≤ b ∧ ¬ b ≤ a) lt_iff_le_not_ge.symm

/-- Node 1 (`doubleShearHexality`) and Node 2 (`tripleShearBruhatQuartic`) form a strict
    diamond of incomparable parallel branches. -/
theorem hexality_and_quartic_branches_incomparable :
    ¬ (doubleShearHexality ≤ tripleShearBruhatQuartic) ∧
    ¬ (tripleShearBruhatQuartic ≤ doubleShearHexality) := by
  decide

def canonicalPending : List ModularParabolicNambuArchetype :=
  [.modularCenterAndNambuSynthesis, .tripleShearBruhatQuartic,
   .doubleShearHexality, .rootPairParabolicSeed]

def canonicalSchedule : List ModularParabolicNambuArchetype :=
  [.rootPairParabolicSeed, .tripleShearBruhatQuartic,
   .doubleShearHexality, .modularCenterAndNambuSynthesis]

theorem canonicalPending_nodup : canonicalPending.Nodup := by decide

theorem canonicalPending_univ : canonicalPending.toFinset = Finset.univ := by decide

theorem compile_canonicalPending :
    compile (∅ : Finset ModularParabolicNambuArchetype) canonicalPending =
      some canonicalSchedule := by
  decide

end ModularParabolicNambuArchetype

/-- Node 0 proved `TypedArchetype`: Peirce idempotence and central sign involution square. -/
def arch0RootPairParabolicSeed : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis.arch0RootPairParabolicSeed
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    (1 + matD2) * (1 - matD2) = (1 : Mat2Z) ∧
    (1 - matB2) * (1 + matB2) = (1 : Mat2Z) ∧
    (poleZeroMode matD2 matB2 - activeSupport matD2 matB2) *
      (poleZeroMode matD2 matB2 - activeSupport matD2 matB2) = (1 : Mat2Z)
  evidence := fun _ =>
    ⟨one_add_mul_one_sub_of_sq_zero mat2Z_isDualRootOfZeroPair.d_sq,
     one_sub_mul_one_add_of_sq_zero mat2Z_isDualRootOfZeroPair.B_sq,
     centerInvolution_sq_one mat2Z_isDualRootOfZeroPair⟩

/-- Node 1 proved `TypedArchetype`: Double shear hexality `Λ₆³ = P₀ - Δ` and `Λ₆⁶ = 1`. -/
def arch1DoubleShearHexality : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis.arch1DoubleShearHexality
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    parabolicHexalityOp matD2 matB2 * parabolicHexalityOpInv matD2 matB2 = (1 : Mat2Z) ∧
    parabolicHexalityOp matD2 matB2 ^ 3 = poleZeroMode matD2 matB2 - activeSupport matD2 matB2 ∧
    parabolicHexalityOp matD2 matB2 ^ 6 = (1 : Mat2Z)
  evidence := fun _ =>
    ⟨parabolicHexalityOp_mul_inv mat2Z_isDualRootOfZeroPair,
     parabolicHexalityOp_cube mat2Z_isDualRootOfZeroPair,
     parabolicHexalityOp_pow_six mat2Z_isDualRootOfZeroPair⟩

/-- Node 2 proved `TypedArchetype`: Triple shear Bruhat quartic `w_J² = P₀ - Δ` and `w_J⁴ = 1`. -/
def arch2TripleShearBruhatQuartic : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis.arch2TripleShearBruhatQuartic
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    bruhatQuarticOp matD2 matB2 * bruhatQuarticOp matD2 matB2 =
      poleZeroMode matD2 matB2 - activeSupport matD2 matB2 ∧
    bruhatQuarticOp matD2 matB2 ^ 4 = (1 : Mat2Z) ∧
    bruhatQuarticOp matD2 matB2 * polePlus matD2 matB2 * bruhatQuarticOpInv matD2 matB2 =
      poleMinus matD2 matB2
  evidence := fun _ =>
    ⟨bruhatQuarticOp_sq mat2Z_isDualRootOfZeroPair,
     bruhatQuarticOp_pow_four mat2Z_isDualRootOfZeroPair,
     bruhatQuarticOp_conj_polePlus mat2Z_isDualRootOfZeroPair⟩

/-- Node 3 proved `TypedArchetype`: Universal modular center law `w_J² = Λ₆³`,
    Jordan-Lie left-multiplication closure, and non-commutativity refutation boundary. -/
def arch3ModularCenterAndNambuSynthesis : TypedArchetype Mat2Z .proved where
  name := `InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis.arch3ModularCenterAndNambuSynthesis
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun Z =>
    bruhatQuarticOp matD2 matB2 * bruhatQuarticOp matD2 matB2 =
      parabolicHexalityOp matD2 matB2 ^ 3 ∧
    (1 + matD2) * (1 - matB2) ≠ (1 - matB2) * (1 + matD2) ∧
    (InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := ℤ) matD2 *
       InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := ℤ) matB2 -
     InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := ℤ) matB2 *
       InfoGeometry.Core.JordanMultiplicationClosure.jordanLeft (R := ℤ) matD2) Z =
      lieBracket (lieBracket matD2 matB2) Z
  evidence := fun Z =>
    ⟨mat2Z_parabolic_shears_noncommuting_witness.2.2.1,
     mat2Z_parabolic_shears_noncommuting_witness.1,
     jordanLeft_commutator_eq_lieBracket matD2 matB2 Z⟩

#register_archetype arch0RootPairParabolicSeed
#register_archetype arch1DoubleShearHexality
#register_archetype arch2TripleShearBruhatQuartic
#register_archetype arch3ModularCenterAndNambuSynthesis

#audit_archetype arch0RootPairParabolicSeed
#audit_archetype arch1DoubleShearHexality
#audit_archetype arch2TripleShearBruhatQuartic
#audit_archetype arch3ModularCenterAndNambuSynthesis

/-- Target statement map on the `ModularParabolicNambuArchetype` poset. -/
def modularParabolicStatement : ModularParabolicNambuArchetype → Prop
  | .rootPairParabolicSeed => arch0RootPairParabolicSeed.claim ()
  | .doubleShearHexality => arch1DoubleShearHexality.claim ()
  | .tripleShearBruhatQuartic => arch2TripleShearBruhatQuartic.claim ()
  | .modularCenterAndNambuSynthesis => ∀ Z : Mat2Z, arch3ModularCenterAndNambuSynthesis.claim Z

lemma modularParabolicRules : ProofRules modularParabolicStatement := by
  intro target _
  cases target with
  | rootPairParabolicSeed => exact arch0RootPairParabolicSeed.discharge ()
  | doubleShearHexality => exact arch1DoubleShearHexality.discharge ()
  | tripleShearBruhatQuartic => exact arch2TripleShearBruhatQuartic.discharge ()
  | modularCenterAndNambuSynthesis => exact fun Z => arch3ModularCenterAndNambuSynthesis.discharge Z

/-- Certified execution of the Meta Epistemic Compiler on the `ModularParabolicNambuArchetype` diamond poset. -/
theorem modular_parabolic_executable_certified_compilation :
    ∃ schedule : List ModularParabolicNambuArchetype,
      compile ∅ ModularParabolicNambuArchetype.canonicalPending = some schedule ∧
      ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧
      schedule.length = Fintype.card ModularParabolicNambuArchetype ∧
      schedule.toFinset = Finset.univ ∧
      ∀ target, modularParabolicStatement target :=
  executable_certified_compilation
    modularParabolicStatement
    modularParabolicRules
    ModularParabolicNambuArchetype.canonicalPending
    ModularParabolicNambuArchetype.canonicalPending_nodup
    ModularParabolicNambuArchetype.canonicalPending_univ

end MetaEpistemicCompilerCertification

end InfoGeometry.Canonical.ModularParabolicCyclotomicSynthesis
