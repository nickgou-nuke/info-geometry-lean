/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Meta.EpistemicCompilerChain
import InfoGeometry.Meta.MetaEpistemicCompiler

/-!
# De Bruijn Name-Free Rotor–Alternation Cycle: Seed Localization, Harmonic Commutator Oscillator, and Moving Idempotent Projectors

This module formalizes **Stream 5** under the `QMS-SOP-IAA-001` / OpenGauss protocol,
translating the name-free de Bruijn $\lambda$-graph of a two-pole carrier with off-diagonal
nilpotent seeds into consumer-minimal atomic lemmas (`< 20` lines each), refutation boundaries,
noncommutative matrix witnesses, and a 4-node diamond causal poset (`DeBruijnRotorArchetype`)
certified by the Lean 4 Meta Epistemic Compiler.

Scope: the canonical algebraic archetypes are a reflexive square-zero pair,
an active-carrier Clifford system, a polynomial circular rotor family,
complementary moving idempotents, and squared-displacement/compression identities.
No topology or differential metric is constructed by these ring identities:


1. **Node 0 (`deBruijnOneHillTwoPoles`)**:
   - Single active carrier `Δ = P₊ + P₋` (`P₊ = d B`, `P₋ = B d`) with complementary
     zero-mode support `P₀ = 1 - Δ`.
   - Off-diagonal nilpotent seed localization `P₊ d P₋ = d` and `P₋ B P₊ = B`
     (`seed_off_diagonal_localization`).
   - Carrier invariance under the skew-Majorana wheel generator `J = d - B`:
     `[J, Δ] = 0` (`wheelGenerator_commutes_carrierSupport`).
2. **Node 1 (`infinitesimalAlternationOscillator`)**:
   - Instantaneous commutator velocity at the poles:
     `[J, P₊] = -Q₁` and `[J, P₋] = +Q₁`, where `Q₁ = d + B` (`lieBracket_wheel_polePlus`,
     `lieBracket_wheel_poleMinus`).
   - Coupled phase-polarization / transition-velocity system for `Γ = P₊ - P₋`:
     `[J, Γ] = -(2 • Q₁)` and `[J, Q₁] = 2 • Γ`.
   - Harmonic Alternation Oscillator Law (`harmonic_alternation_oscillator_law`):
     `[J, [J, Γ]] = -(4 • Γ)`.
3. **Node 2 (`algebraicCircularRotor`)**:
   - Algebraic circular rotor `R(c, s) = P₀ + c • Δ + s • J` over `[CommRing R] [Ring A] [Algebra R A]`.
   - Explicit moving projector & opposite-seed growth formulas
     (`movingPolePlus_explicit_formula`, `movingPoleMinus_explicit_formula`):
     `P₊(c, s) = R(c, s) P₊ R(c, -s) = (c * c) • P₊ + (s * s) • P₋ - (c * s) • Q₁` and
     `P₋(c, s) = R(c, s) P₋ R(c, -s) = (c * c) • P₋ + (s * s) • P₊ + (c * s) • Q₁`,
     proving that at `(c, s) = (0, 1)` the two poles trade places (`P₊(0, 1) = P₋`,
     `P₋(0, 1) = P₊`).
   - Exact action of the inverse rotor `R(c, -s) (R(c, s) P₊) = P₊`, moving idempotence
     `P₊(c, s) * P₊(c, s) = P₊(c, s)`, and carrier conservation
     `P₊(c, s) + P₋(c, s) = Δ` whenever `c * c + s * s = 1`.
4. **Node 3 (`movingIdempotentAndNonCommutingWitness`)**:
   - Refutation boundary (`no_turning_iff_seeds_vanish`):
     `[J, P₊] = 0 ↔ (d = 0 ∧ B = 0)` (no turning occurs without the off-diagonal nilpotent seeds).
   - Noncommutative `Matrix (Fin 2) (Fin 2) ℤ` witness (`mat2Z_rotor_alternation_witness`).
   - Diamond causal poset `DeBruijnRotorArchetype` certified via `#register_archetype`,
     `#audit_archetype`, and `executable_certified_compilation`.
-/

namespace InfoGeometry.Canonical.DeBruijnRotorAlternationCycle

open Matrix

section UniversalRotorAlternation

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

/-!
## 1. De Bruijn Name-Free Primitives: One Carrier `Δ`, Two Poles `P_±`, Two Nilpotent Seeds `d, B`
-/

/-- Symmetrized Jordan anticommutator `{X, Y} = X Y + Y X`. -/
def jordanProd (X Y : A) : A := X * Y + Y * X

/-- Antisymmetric Lie commutator (infinitesimal flow derivative) `[X, Y] = X Y - Y X`. -/
def lieBracket (X Y : A) : A := X * Y - Y * X

/-- Reflexive square-zero seed pair `(d, B)`: `d² = 0`, `B² = 0`, `d B d = d`, `B d B = B`. -/
structure IsDualSeedPair (d B : A) : Prop where
  d_sq : d * d = 0
  B_sq : B * B = 0
  dBd : d * B * d = d
  BdB : B * d * B = B

/-- First pole idempotent `P₊ = d B` ("side 1 of the carrier"). -/
def polePlus (d B : A) : A := d * B

/-- Second pole idempotent `P₋ = B d` ("side 2 of the same carrier"). -/
def poleMinus (d B : A) : A := B * d

/-- Total active carrier `Δ = P₊ + P₋` ("the single hill"). -/
def carrierSupport (d B : A) : A := polePlus d B + poleMinus d B

/-- Complementary zero-mode carrier `P₀ = 1 - Δ`. -/
def zeroModeSupport (d B : A) : A := 1 - carrierSupport d B

/-- Phase polarization `Γ = P₊ - P₋`. -/
def phasePolarization (d B : A) : A := polePlus d B - poleMinus d B

/-- Odd transition velocity `Q₁ = d + B`. -/
def transitionVelocity (d B : A) : A := d + B

/-- Skew-Majorana wheel generator `J = d - B` (`J² = -Δ`). -/
def wheelGenerator (d B : A) : A := d - B

/-- Algebraic circular rotor `R(c, s) = P₀ + c • Δ + s • J`. -/
def phaseRotor (c s : R) (d B : A) : A :=
  zeroModeSupport d B + c • carrierSupport d B + s • wheelGenerator d B

/-- Moving pole projection `P₊(c, s) = R(c, s) * P₊ * R(c, -s)`. -/
def movingPolePlus (c s : R) (d B : A) : A :=
  phaseRotor c s d B * polePlus d B * phaseRotor c (-s) d B

/-- Moving opposite pole projection `P₋(c, s) = R(c, s) * P₋ * R(c, -s)`. -/
def movingPoleMinus (c s : R) (d B : A) : A :=
  phaseRotor c s d B * poleMinus d B * phaseRotor c (-s) d B

/-!
## 2. Node 0 Atomic Lemmas: Seed Localization & Carrier Invariance `[J, Δ] = 0`
-/

lemma polePlus_idem {d B : A} (h : IsDualSeedPair d B) :
    polePlus d B * polePlus d B = polePlus d B := by
  unfold polePlus
  calc (d * B) * (d * B) = (d * B * d) * B := by noncomm_ring
    _ = d * B := by rw [h.dBd]

lemma poleMinus_idem {d B : A} (h : IsDualSeedPair d B) :
    poleMinus d B * poleMinus d B = poleMinus d B := by
  unfold poleMinus
  calc (B * d) * (B * d) = (B * d * B) * d := by noncomm_ring
    _ = B * d := by rw [h.BdB]

lemma polePlus_mul_poleMinus {d B : A} (h : IsDualSeedPair d B) :
    polePlus d B * poleMinus d B = 0 := by
  unfold polePlus poleMinus
  calc (d * B) * (B * d) = d * (B * B) * d := by noncomm_ring
    _ = 0 := by rw [h.B_sq, mul_zero, zero_mul]

lemma poleMinus_mul_polePlus {d B : A} (h : IsDualSeedPair d B) :
    poleMinus d B * polePlus d B = 0 := by
  unfold poleMinus polePlus
  calc (B * d) * (d * B) = B * (d * d) * B := by noncomm_ring
    _ = 0 := by rw [h.d_sq, mul_zero, zero_mul]

lemma carrierSupport_idem {d B : A} (h : IsDualSeedPair d B) :
    carrierSupport d B * carrierSupport d B = carrierSupport d B := by
  unfold carrierSupport
  rw [add_mul, mul_add, mul_add, polePlus_idem h, polePlus_mul_poleMinus h,
      poleMinus_mul_polePlus h, poleMinus_idem h, add_zero, zero_add]

lemma zeroModeSupport_idem {d B : A} (h : IsDualSeedPair d B) :
    zeroModeSupport d B * zeroModeSupport d B = zeroModeSupport d B := by
  unfold zeroModeSupport
  calc (1 - carrierSupport d B) * (1 - carrierSupport d B)
    _ = 1 - 2 • carrierSupport d B + carrierSupport d B * carrierSupport d B := by noncomm_ring
    _ = 1 - carrierSupport d B := by rw [carrierSupport_idem h]; abel

lemma transitionVelocity_sq {d B : A} (h : IsDualSeedPair d B) :
    transitionVelocity d B * transitionVelocity d B = carrierSupport d B := by
  unfold transitionVelocity carrierSupport polePlus poleMinus
  calc (d + B) * (d + B) = d * d + (d * B + B * d) + B * B := by noncomm_ring
    _ = d * B + B * d := by rw [h.d_sq, h.B_sq, zero_add, add_zero]

lemma wheelGenerator_sq {d B : A} (h : IsDualSeedPair d B) :
    wheelGenerator d B * wheelGenerator d B = -carrierSupport d B := by
  unfold wheelGenerator carrierSupport polePlus poleMinus
  calc (d - B) * (d - B) = d * d - (d * B + B * d) + B * B := by noncomm_ring
    _ = -(d * B + B * d) := by rw [h.d_sq, h.B_sq]; abel

lemma phasePolarization_sq {d B : A} (h : IsDualSeedPair d B) :
    phasePolarization d B * phasePolarization d B = carrierSupport d B := by
  unfold phasePolarization carrierSupport
  rw [sub_mul, mul_sub, mul_sub, polePlus_idem h, polePlus_mul_poleMinus h,
      poleMinus_mul_polePlus h, poleMinus_idem h]
  abel

lemma polePlus_mul_velocity {d B : A} (h : IsDualSeedPair d B) :
    polePlus d B * transitionVelocity d B = d := by
  have hdB_B : (d * B) * B = 0 := by rw [mul_assoc, h.B_sq, mul_zero]
  unfold polePlus transitionVelocity
  rw [mul_add, h.dBd, hdB_B, add_zero]

lemma velocity_mul_polePlus {d B : A} (h : IsDualSeedPair d B) :
    transitionVelocity d B * polePlus d B = B := by
  have hd_dB : d * (d * B) = 0 := by rw [← mul_assoc, h.d_sq, zero_mul]
  have hB_dB : B * (d * B) = B := by rw [← mul_assoc, h.BdB]
  unfold polePlus transitionVelocity
  rw [add_mul, hd_dB, hB_dB, zero_add]

lemma poleMinus_mul_velocity {d B : A} (h : IsDualSeedPair d B) :
    poleMinus d B * transitionVelocity d B = B := by
  have hBd_d : (B * d) * d = 0 := by rw [mul_assoc, h.d_sq, mul_zero]
  unfold poleMinus transitionVelocity
  rw [mul_add, hBd_d, h.BdB, zero_add]

lemma velocity_mul_poleMinus {d B : A} (h : IsDualSeedPair d B) :
    transitionVelocity d B * poleMinus d B = d := by
  have hd_Bd : d * (B * d) = d := by rw [← mul_assoc, h.dBd]
  have hB_Bd : B * (B * d) = 0 := by rw [← mul_assoc, h.B_sq, zero_mul]
  unfold poleMinus transitionVelocity
  rw [add_mul, hd_Bd, hB_Bd, add_zero]

lemma polarization_anticommutes_velocity {d B : A} (h : IsDualSeedPair d B) :
    jordanProd (phasePolarization d B) (transitionVelocity d B) = 0 := by
  unfold jordanProd phasePolarization
  rw [sub_mul, mul_sub, polePlus_mul_velocity h, poleMinus_mul_velocity h,
      velocity_mul_polePlus h, velocity_mul_poleMinus h]
  abel

/-- **Seed Localization Lemma**:
    `d` is the off-diagonal seed bridging `P₋ → P₊` (`P₊ d P₋ = d`),
    and `B` is the off-diagonal seed bridging `P₊ → P₋` (`P₋ B P₊ = B`). -/
lemma seed_off_diagonal_localization {d B : A} (h : IsDualSeedPair d B) :
    polePlus d B * d * poleMinus d B = d ∧
    poleMinus d B * B * polePlus d B = B := by
  refine ⟨?_, ?_⟩
  · unfold polePlus poleMinus
    calc (d * B) * d * (B * d) = (d * B * d) * B * d := by noncomm_ring
      _ = d := by rw [h.dBd, h.dBd]
  · unfold poleMinus polePlus
    calc (B * d) * B * (d * B) = (B * d * B) * d * B := by noncomm_ring
      _ = B := by rw [h.BdB, h.BdB]

/-- **Total Carrier Invariance (`[J, Δ] = 0`)**:
    The total carrier `Δ = P₊ + P₋` is stationary under the wheel generator `J = d - B`. -/
lemma wheelGenerator_commutes_carrierSupport {d B : A} (h : IsDualSeedPair d B) :
    lieBracket (wheelGenerator d B) (carrierSupport d B) = 0 := by
  have hd_dB : d * (d * B) = 0 := by rw [← mul_assoc, h.d_sq, zero_mul]
  have hd_Bd : d * (B * d) = d := by rw [← mul_assoc, h.dBd]
  have hB_dB : B * (d * B) = B := by rw [← mul_assoc, h.BdB]
  have hB_Bd : B * (B * d) = 0 := by rw [← mul_assoc, h.B_sq, zero_mul]
  have hBd_d : (B * d) * d = 0 := by rw [mul_assoc, h.d_sq, mul_zero]
  have hdB_B : (d * B) * B = 0 := by rw [mul_assoc, h.B_sq, mul_zero]
  unfold lieBracket wheelGenerator carrierSupport polePlus poleMinus
  calc (d - B) * (d * B + B * d) - (d * B + B * d) * (d - B)
    _ = (d * (d * B) + d * (B * d) - B * (d * B) - B * (B * d)) -
        ((d * B * d) - (d * B) * B + (B * d) * d - (B * d * B)) := by noncomm_ring
    _ = 0 := by rw [hd_dB, hd_Bd, hB_dB, hB_Bd, h.dBd, hdB_B, hBd_d, h.BdB]; abel

/-!
## 3. Node 1 Atomic Lemmas: Infinitesimal Alternation Oscillator `[J, [J, Γ]] = -4 Γ`
-/

lemma lieBracket_wheel_polePlus {d B : A} (h : IsDualSeedPair d B) :
    lieBracket (wheelGenerator d B) (polePlus d B) = -transitionVelocity d B := by
  have hd_dB : d * (d * B) = 0 := by rw [← mul_assoc, h.d_sq, zero_mul]
  have hB_dB : B * (d * B) = B := by rw [← mul_assoc, h.BdB]
  have hdB_B : (d * B) * B = 0 := by rw [mul_assoc, h.B_sq, mul_zero]
  unfold lieBracket wheelGenerator polePlus transitionVelocity
  calc (d - B) * (d * B) - (d * B) * (d - B)
    _ = d * (d * B) - B * (d * B) - (d * B * d) + (d * B) * B := by noncomm_ring
    _ = -(d + B) := by rw [hd_dB, hB_dB, h.dBd, hdB_B]; abel

lemma lieBracket_wheel_poleMinus {d B : A} (h : IsDualSeedPair d B) :
    lieBracket (wheelGenerator d B) (poleMinus d B) = transitionVelocity d B := by
  have hd_Bd : d * (B * d) = d := by rw [← mul_assoc, h.dBd]
  have hB_Bd : B * (B * d) = 0 := by rw [← mul_assoc, h.B_sq, zero_mul]
  have hBd_d : (B * d) * d = 0 := by rw [mul_assoc, h.d_sq, mul_zero]
  unfold lieBracket wheelGenerator poleMinus transitionVelocity
  calc (d - B) * (B * d) - (B * d) * (d - B)
    _ = d * (B * d) - B * (B * d) - (B * d) * d + (B * d * B) := by noncomm_ring
    _ = d + B := by rw [hd_Bd, hB_Bd, hBd_d, h.BdB]; abel

lemma lieBracket_wheel_polarization {d B : A} (h : IsDualSeedPair d B) :
    lieBracket (wheelGenerator d B) (phasePolarization d B) =
      -(2 • transitionVelocity d B) := by
  have h_sub : lieBracket (wheelGenerator d B) (phasePolarization d B) =
      lieBracket (wheelGenerator d B) (polePlus d B) -
      lieBracket (wheelGenerator d B) (poleMinus d B) := by
    unfold lieBracket phasePolarization; noncomm_ring
  rw [h_sub, lieBracket_wheel_polePlus h, lieBracket_wheel_poleMinus h, two_nsmul]
  abel

lemma lieBracket_wheel_velocity (d B : A) :
    lieBracket (wheelGenerator d B) (transitionVelocity d B) =
      2 • phasePolarization d B := by
  unfold lieBracket wheelGenerator transitionVelocity phasePolarization polePlus poleMinus
  calc (d - B) * (d + B) - (d + B) * (d - B)
    _ = 2 • (d * B - B * d) := by rw [two_nsmul]; noncomm_ring

/-- **Harmonic Alternation Oscillator Law (`[J, [J, Γ]] = -(4 • Γ)`)**:
    The second commutator of the phase polarization `Γ = P₊ - P₋` along the wheel `J`
    is strictly restoring (`-4 • Γ`). -/
theorem harmonic_alternation_oscillator_law {d B : A} (h : IsDualSeedPair d B) :
    lieBracket (wheelGenerator d B)
      (lieBracket (wheelGenerator d B) (phasePolarization d B)) =
      -(4 • phasePolarization d B) := by
  rw [lieBracket_wheel_polarization h]
  have h_lin : ∀ X Y : A, lieBracket X (-(2 • Y)) = -(2 • lieBracket X Y) := by
    intro X Y; unfold lieBracket; rw [two_nsmul, two_nsmul]; noncomm_ring
  rw [h_lin, lieBracket_wheel_velocity d B]
  have h_smul : 2 • (2 • phasePolarization d B) = 4 • phasePolarization d B :=
    (mul_nsmul (phasePolarization d B) 2 2).symm
  rw [h_smul]

/-!
## 4. Node 2 Atomic Lemmas: Algebraic Circular Rotor & Seed Growth Formula
-/

lemma phaseRotor_mul_polePlus {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    phaseRotor c s d B * polePlus d B = c • polePlus d B - s • B := by
  have h_P0_Pp : zeroModeSupport d B * polePlus d B = 0 := by
    unfold zeroModeSupport carrierSupport
    rw [sub_mul, one_mul, add_mul, polePlus_idem h, poleMinus_mul_polePlus h, add_zero, sub_self]
  have h_Delta_Pp : carrierSupport d B * polePlus d B = polePlus d B := by
    unfold carrierSupport
    rw [add_mul, polePlus_idem h, poleMinus_mul_polePlus h, add_zero]
  have h_J_Pp : wheelGenerator d B * polePlus d B = -B := by
    unfold wheelGenerator polePlus
    calc (d - B) * (d * B) = (d * d) * B - (B * d * B) := by noncomm_ring
      _ = -B := by rw [h.d_sq, h.BdB, zero_mul, zero_sub]
  unfold phaseRotor
  rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc,
      h_P0_Pp, h_Delta_Pp, h_J_Pp, smul_neg, zero_add, sub_eq_add_neg]

lemma polePlus_mul_phaseRotor_neg {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    polePlus d B * phaseRotor c (-s) d B = c • polePlus d B - s • d := by
  have h_Pp_P0 : polePlus d B * zeroModeSupport d B = 0 := by
    unfold zeroModeSupport carrierSupport
    rw [mul_sub, mul_one, mul_add, polePlus_idem h, polePlus_mul_poleMinus h, add_zero, sub_self]
  have h_Pp_Delta : polePlus d B * carrierSupport d B = polePlus d B := by
    unfold carrierSupport
    rw [mul_add, polePlus_idem h, polePlus_mul_poleMinus h, add_zero]
  have h_Pp_J : polePlus d B * wheelGenerator d B = d := by
    unfold wheelGenerator polePlus
    calc (d * B) * (d - B) = (d * B * d) - d * (B * B) := by noncomm_ring
      _ = d := by rw [h.dBd, h.B_sq, mul_zero, sub_zero]
  unfold phaseRotor
  rw [mul_add, mul_add, mul_smul_comm, mul_smul_comm,
      h_Pp_P0, h_Pp_Delta, h_Pp_J, neg_smul, zero_add, sub_eq_add_neg]

lemma B_mul_phaseRotor_neg {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    B * phaseRotor c (-s) d B = c • B - s • poleMinus d B := by
  have hB_Pp : B * polePlus d B = B := by unfold polePlus; rw [← mul_assoc, h.BdB]
  have hB_Pm : B * poleMinus d B = 0 := by unfold poleMinus; rw [← mul_assoc, h.B_sq, zero_mul]
  have hB_Delta : B * carrierSupport d B = B := by
    unfold carrierSupport; rw [mul_add, hB_Pp, hB_Pm, add_zero]
  have hB_P0 : B * zeroModeSupport d B = 0 := by
    unfold zeroModeSupport; rw [mul_sub, mul_one, hB_Delta, sub_self]
  have hB_J : B * wheelGenerator d B = poleMinus d B := by
    unfold wheelGenerator poleMinus; rw [mul_sub, h.B_sq, sub_zero]
  unfold phaseRotor
  rw [mul_add, mul_add, mul_smul_comm, mul_smul_comm,
      hB_P0, hB_Delta, hB_J, neg_smul, zero_add, sub_eq_add_neg]

lemma movingPolePlus_eq {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    movingPolePlus c s d B =
      (c * c) • polePlus d B + (s * s) • poleMinus d B -
      (c * s) • transitionVelocity d B := by
  unfold movingPolePlus
  rw [phaseRotor_mul_polePlus h c s, sub_mul, smul_mul_assoc, smul_mul_assoc,
      polePlus_mul_phaseRotor_neg h c s, B_mul_phaseRotor_neg h c s,
      smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul,
      mul_comm s c]
  unfold transitionVelocity
  rw [smul_add]
  abel

/-- **Explicit Moving Projector & Opposite-Seed Growth Formula (`P₊(c, s)`)**:
    At any rotor parameters `(c, s)`, the rotated pole `P₊(c, s) = R(c, s) P₊ R(c, -s)` is:
    `P₊(c, s) = (c * c) • P₊ + (s * s) • P₋ - (c * s) • Q₁`.
    At `c = 0, s = 1`, `P₊(0, 1) = P₋` (the two poles trade places). -/
theorem movingPolePlus_explicit_formula {d B : A}
    (h : IsDualSeedPair d B) (c s : R) :
    movingPolePlus c s d B =
      (c * c) • polePlus d B + (s * s) • poleMinus d B -
      (c * s) • transitionVelocity d B ∧
    movingPolePlus (0 : R) (1 : R) d B = poleMinus d B := by
  refine ⟨movingPolePlus_eq h c s, ?_⟩
  rw [movingPolePlus_eq h (0 : R) (1 : R)]
  simp only [mul_zero, zero_smul, mul_one, one_smul, zero_add, sub_zero]

lemma phaseRotor_mul_poleMinus {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    phaseRotor c s d B * poleMinus d B = c • poleMinus d B + s • d := by
  have h_P0_Pm : zeroModeSupport d B * poleMinus d B = 0 := by
    unfold zeroModeSupport carrierSupport
    rw [sub_mul, one_mul, add_mul, polePlus_mul_poleMinus h, poleMinus_idem h, zero_add, sub_self]
  have h_Delta_Pm : carrierSupport d B * poleMinus d B = poleMinus d B := by
    unfold carrierSupport
    rw [add_mul, polePlus_mul_poleMinus h, poleMinus_idem h, zero_add]
  have h_J_Pm : wheelGenerator d B * poleMinus d B = d := by
    unfold wheelGenerator poleMinus
    calc (d - B) * (B * d) = (d * B * d) - (B * B) * d := by noncomm_ring
      _ = d := by rw [h.dBd, h.B_sq, zero_mul, sub_zero]
  unfold phaseRotor
  rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc,
      h_P0_Pm, h_Delta_Pm, h_J_Pm, zero_add]

lemma poleMinus_mul_phaseRotor_neg {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    poleMinus d B * phaseRotor c (-s) d B = c • poleMinus d B + s • B := by
  have h_Pm_P0 : poleMinus d B * zeroModeSupport d B = 0 := by
    unfold zeroModeSupport carrierSupport
    rw [mul_sub, mul_one, mul_add, poleMinus_mul_polePlus h, poleMinus_idem h, zero_add, sub_self]
  have h_Pm_Delta : poleMinus d B * carrierSupport d B = poleMinus d B := by
    unfold carrierSupport
    rw [mul_add, poleMinus_mul_polePlus h, poleMinus_idem h, zero_add]
  have h_Pm_J : poleMinus d B * wheelGenerator d B = -B := by
    unfold wheelGenerator poleMinus
    calc (B * d) * (d - B) = B * (d * d) - (B * d * B) := by noncomm_ring
      _ = -B := by rw [h.d_sq, h.BdB, mul_zero, zero_sub]
  unfold phaseRotor
  rw [mul_add, mul_add, mul_smul_comm, mul_smul_comm,
      h_Pm_P0, h_Pm_Delta, h_Pm_J, smul_neg, neg_smul, neg_neg, zero_add]

lemma d_mul_phaseRotor_neg {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    d * phaseRotor c (-s) d B = c • d + s • polePlus d B := by
  have hd_Pp : d * polePlus d B = 0 := by unfold polePlus; rw [← mul_assoc, h.d_sq, zero_mul]
  have hd_Pm : d * poleMinus d B = d := by unfold poleMinus; rw [← mul_assoc, h.dBd]
  have hd_Delta : d * carrierSupport d B = d := by
    unfold carrierSupport; rw [mul_add, hd_Pp, hd_Pm, zero_add]
  have hd_P0 : d * zeroModeSupport d B = 0 := by
    unfold zeroModeSupport; rw [mul_sub, mul_one, hd_Delta, sub_self]
  have hd_J : d * wheelGenerator d B = -polePlus d B := by
    unfold wheelGenerator polePlus; rw [mul_sub, h.d_sq, zero_sub]
  unfold phaseRotor
  rw [mul_add, mul_add, mul_smul_comm, mul_smul_comm,
      hd_P0, hd_Delta, hd_J, smul_neg, neg_smul, neg_neg, zero_add]

lemma movingPoleMinus_eq {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    movingPoleMinus c s d B =
      (c * c) • poleMinus d B + (s * s) • polePlus d B +
      (c * s) • transitionVelocity d B := by
  unfold movingPoleMinus
  rw [phaseRotor_mul_poleMinus h c s, add_mul, smul_mul_assoc, smul_mul_assoc,
      poleMinus_mul_phaseRotor_neg h c s, d_mul_phaseRotor_neg h c s,
      smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
      mul_comm s c]
  unfold transitionVelocity
  rw [smul_add]
  abel

/-- **Explicit Opposite Moving Projector (`P₋(c, s)`)**:
    `P₋(c, s) = (c * c) • P₋ + (s * s) • P₊ + (c * s) • Q₁` and `P₋(0, 1) = P₊`. -/
theorem movingPoleMinus_explicit_formula {d B : A}
    (h : IsDualSeedPair d B) (c s : R) :
    movingPoleMinus c s d B =
      (c * c) • poleMinus d B + (s * s) • polePlus d B +
      (c * s) • transitionVelocity d B ∧
    movingPoleMinus (0 : R) (1 : R) d B = polePlus d B := by
  refine ⟨movingPoleMinus_eq h c s, ?_⟩
  rw [movingPoleMinus_eq h (0 : R) (1 : R)]
  simp only [mul_zero, zero_smul, mul_one, one_smul, zero_add, add_zero]

/-- **Carrier Conservation (`P₊(c, s) + P₋(c, s) = Δ`)**:
    Whenever `c * c + s * s = 1`, the sum of the moving poles equals the stationary carrier `Δ`. -/
theorem movingPoles_sum_eq_carrierSupport {d B : A}
    (h : IsDualSeedPair d B) (c s : R) (hcs : c * c + s * s = 1) :
    movingPolePlus c s d B + movingPoleMinus c s d B = carrierSupport d B := by
  rw [(movingPolePlus_explicit_formula h c s).1, (movingPoleMinus_explicit_formula h c s).1]
  calc ((c * c) • polePlus d B + (s * s) • poleMinus d B - (c * s) • transitionVelocity d B) +
       ((c * c) • poleMinus d B + (s * s) • polePlus d B + (c * s) • transitionVelocity d B)
    _ = (c * c + s * s) • polePlus d B + (c * c + s * s) • poleMinus d B := by
        rw [add_smul, add_smul]; abel
    _ = carrierSupport d B := by
        rw [hcs, one_smul, one_smul]; rfl

lemma phaseRotor_mul_B {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    phaseRotor c s d B * B = c • B + s • polePlus d B := by
  have hPp_B : polePlus d B * B = 0 := by unfold polePlus; rw [mul_assoc, h.B_sq, mul_zero]
  have hPm_B : poleMinus d B * B = B := h.BdB
  have hDelta_B : carrierSupport d B * B = B := by
    unfold carrierSupport; rw [add_mul, hPp_B, hPm_B, zero_add]
  have hP0_B : zeroModeSupport d B * B = 0 := by
    unfold zeroModeSupport; rw [sub_mul, one_mul, hDelta_B, sub_self]
  have hJ_B : wheelGenerator d B * B = polePlus d B := by
    unfold wheelGenerator polePlus; rw [sub_mul, h.B_sq, sub_zero]
  unfold phaseRotor
  rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, hP0_B, hDelta_B, hJ_B, zero_add]

lemma phaseRotor_neg_mul_phaseRotor_mul_polePlus {d B : A}
    (h : IsDualSeedPair d B) (c s : R) (hcs : c * c + s * s = 1) :
    phaseRotor c (-s) d B * (phaseRotor c s d B * polePlus d B) = polePlus d B := by
  rw [phaseRotor_mul_polePlus h c s, mul_sub, mul_smul_comm, mul_smul_comm,
      phaseRotor_mul_polePlus h c (-s), phaseRotor_mul_B h c (-s),
      neg_smul, sub_neg_eq_add, neg_smul, smul_add, smul_add, smul_neg,
      smul_smul, smul_smul, smul_smul, smul_smul, mul_comm c s]
  calc (c * c) • polePlus d B + (s * c) • B - ((s * c) • B + -((s * s) • polePlus d B))
    _ = (c * c + s * s) • polePlus d B := by rw [add_smul]; abel
    _ = polePlus d B := by rw [hcs, one_smul]

/-- **Moving Projector Idempotence (`P₊(c, s)² = P₊(c, s)`)**:
    Whenever `c * c + s * s = 1`, the rotated pole `P₊(c, s)` is an exact idempotent projector. -/
theorem movingPolePlus_idem {d B : A}
    (h : IsDualSeedPair d B) (c s : R) (hcs : c * c + s * s = 1) :
    movingPolePlus c s d B * movingPolePlus c s d B = movingPolePlus c s d B := by
  unfold movingPolePlus
  calc (phaseRotor c s d B * polePlus d B * phaseRotor c (-s) d B) *
       (phaseRotor c s d B * polePlus d B * phaseRotor c (-s) d B)
    _ = phaseRotor c s d B * polePlus d B *
        (phaseRotor c (-s) d B * (phaseRotor c s d B * polePlus d B)) *
        phaseRotor c (-s) d B := by simp only [mul_assoc]
    _ = phaseRotor c s d B * (polePlus d B * polePlus d B) * phaseRotor c (-s) d B := by
        rw [phaseRotor_neg_mul_phaseRotor_mul_polePlus h c s hcs]; simp only [mul_assoc]
    _ = phaseRotor c s d B * polePlus d B * phaseRotor c (-s) d B := by rw [polePlus_idem h]

/-- **Polarization Decomposition of the Moving Projector**:
    `P₊(c, s) - P₊ = -s • (s • Γ + c • Q₁)` whenever `c * c + s * s = 1`. -/
lemma movingPolePlus_sub_polePlus {d B : A} (h : IsDualSeedPair d B)
    (c s : R) (h_cs : c * c + s * s = 1) :
    movingPolePlus c s d B - polePlus d B =
      -(s • (s • phasePolarization d B + c • transitionVelocity d B)) := by
  have h_c2 : c * c - 1 = -(s * s) := by linear_combination h_cs
  rw [movingPolePlus_eq h c s]
  unfold phasePolarization
  calc (c * c) • polePlus d B + (s * s) • poleMinus d B -
       (c * s) • transitionVelocity d B - polePlus d B
    _ = (c * c - 1) • polePlus d B + (s * s) • poleMinus d B -
        (c * s) • transitionVelocity d B := by rw [sub_smul, one_smul]; abel
    _ = -(s • (s • (polePlus d B - poleMinus d B) + c • transitionVelocity d B)) := by
        rw [h_c2, neg_smul, smul_add, smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, mul_comm s c]
        abel

/-- **Clifford Square of the Chordal Direction `U(c, s) = s • Γ + c • Q₁`**:
    Because `Γ² = Δ`, `Q₁² = Δ`, and `{Γ, Q₁} = 0`, `(s • Γ + c • Q₁)² = (c² + s²) • Δ`. -/
lemma chordalDirection_sq {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    (s • phasePolarization d B + c • transitionVelocity d B) *
    (s • phasePolarization d B + c • transitionVelocity d B) =
      (c * c + s * s) • carrierSupport d B := by
  calc (s • phasePolarization d B + c • transitionVelocity d B) *
       (s • phasePolarization d B + c • transitionVelocity d B)
    _ = (s * s) • (phasePolarization d B * phasePolarization d B) +
        (c * c) • (transitionVelocity d B * transitionVelocity d B) +
        (s * c) • jordanProd (phasePolarization d B) (transitionVelocity d B) := by
        unfold jordanProd
        simp only [add_mul, mul_add, smul_mul_smul, smul_add, mul_comm c s]
        abel
    _ = (c * c + s * s) • carrierSupport d B := by
        rw [phasePolarization_sq h, transitionVelocity_sq h,
            polarization_anticommutes_velocity h, smul_zero, add_zero,
            ← add_smul, add_comm (s * s) (c * c)]

lemma movingPolePlus_mul_carrierSupport {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    movingPolePlus c s d B * carrierSupport d B = movingPolePlus c s d B := by
  have hPp_Delta : polePlus d B * carrierSupport d B = polePlus d B := by
    unfold carrierSupport; rw [mul_add, polePlus_idem h, polePlus_mul_poleMinus h, add_zero]
  have hPm_Delta : poleMinus d B * carrierSupport d B = poleMinus d B := by
    unfold carrierSupport; rw [mul_add, poleMinus_mul_polePlus h, poleMinus_idem h, zero_add]
  have hQ1_Delta : transitionVelocity d B * carrierSupport d B = transitionVelocity d B := by
    unfold carrierSupport
    rw [mul_add, velocity_mul_polePlus h, velocity_mul_poleMinus h]
    unfold transitionVelocity; abel
  rw [movingPolePlus_eq h c s, sub_mul, add_mul,
      smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
      hPp_Delta, hPm_Delta, hQ1_Delta]

/-- **Exact Idempotence & Mutual Orthogonality of the Moving Projectors (`movingPolePlus_idem_and_orth`)**:
    Whenever `c * c + s * s = 1`:
    1. `P₊(c, s) * P₊(c, s) = P₊(c, s)` (Idempotent at every instant of the cycle).
    2. `P₊(c, s) + P₋(c, s) = carrierSupport d B` (Conserves the total carrier `Δ`).
    3. `P₊(c, s) * P₋(c, s) = 0` (The two moving poles remain mutually orthogonal). -/
theorem movingPolePlus_idem_and_orth {d B : A} (h : IsDualSeedPair d B)
    {c s : R} (h_cs : c * c + s * s = 1) :
    movingPolePlus c s d B * movingPolePlus c s d B = movingPolePlus c s d B ∧
    movingPolePlus c s d B + movingPoleMinus c s d B = carrierSupport d B ∧
    movingPolePlus c s d B * movingPoleMinus c s d B = 0 := by
  have h_idem := movingPolePlus_idem h c s h_cs
  have h_sum := movingPoles_sum_eq_carrierSupport h c s h_cs
  refine ⟨h_idem, h_sum, ?_⟩
  have h_minus : movingPoleMinus c s d B = carrierSupport d B - movingPolePlus c s d B :=
    eq_sub_of_add_eq' h_sum
  rw [h_minus, mul_sub, movingPolePlus_mul_carrierSupport h c s, h_idem, sub_self]

/-- The moving positive pole is supported on the left by the active carrier. -/
lemma carrierSupport_mul_movingPolePlus {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    carrierSupport d B * movingPolePlus c s d B = movingPolePlus c s d B := by
  have hp : carrierSupport d B * polePlus d B = polePlus d B := by
    simp [carrierSupport, add_mul, polePlus_idem h, poleMinus_mul_polePlus h]
  have hm : carrierSupport d B * poleMinus d B = poleMinus d B := by
    simp [carrierSupport, add_mul, polePlus_mul_poleMinus h, poleMinus_idem h]
  have hq : carrierSupport d B * transitionVelocity d B = transitionVelocity d B := by
    rw [carrierSupport, add_mul, polePlus_mul_velocity h, poleMinus_mul_velocity h]
    rfl
  rw [movingPolePlus_eq h c s, mul_sub, mul_add, mul_smul_comm, mul_smul_comm,
    mul_smul_comm, hp, hm, hq]

/-- Complementary moving idempotents in the active carrier, with both zero products.
Orthogonality here is multiplicative; it does not assert self-adjointness. -/
theorem movingPoles_complementary_idempotents {d B : A} (h : IsDualSeedPair d B)
    {c s : R} (hcs : c * c + s * s = 1) :
    IsIdempotentElem (movingPolePlus c s d B) ∧
    IsIdempotentElem (movingPoleMinus c s d B) ∧
    movingPolePlus c s d B + movingPoleMinus c s d B = carrierSupport d B ∧
    movingPolePlus c s d B * movingPoleMinus c s d B = 0 ∧
    movingPoleMinus c s d B * movingPolePlus c s d B = 0 := by
  obtain ⟨hp, hsum, horth⟩ := movingPolePlus_idem_and_orth h hcs
  have hm := eq_sub_of_add_eq' hsum
  have hl := carrierSupport_mul_movingPolePlus h c s
  have hr := movingPolePlus_mul_carrierSupport h c s
  refine ⟨hp, ?_, hsum, horth, ?_⟩
  · change movingPoleMinus c s d B * movingPoleMinus c s d B = movingPoleMinus c s d B
    rw [hm, sub_mul, mul_sub, mul_sub, carrierSupport_idem h, hl, hr, hp]
    abel
  · rw [hm, sub_mul, hl, hp, sub_self]

/-- Algebraic squared displacement and compression on the active carrier.
No norm, order, self-adjointness, Fubini–Study metric, or probability is assumed. -/
theorem movingPolePlus_chordal_square_and_compression {d B : A} (h : IsDualSeedPair d B)
    {c s : R} (h_cs : c * c + s * s = 1) :
    (movingPolePlus c s d B - polePlus d B) *
      (movingPolePlus c s d B - polePlus d B) = (s * s) • carrierSupport d B ∧
    polePlus d B * movingPolePlus c s d B * polePlus d B = (c * c) • polePlus d B := by
  refine ⟨?_, ?_⟩
  · rw [movingPolePlus_sub_polePlus h c s h_cs, neg_mul_neg,
        smul_mul_smul, chordalDirection_sq h c s, h_cs, one_smul]
  · have h_v_P : polePlus d B * transitionVelocity d B * polePlus d B = 0 := by
      rw [polePlus_mul_velocity h]
      unfold polePlus
      rw [← mul_assoc, h.d_sq, zero_mul]
    rw [movingPolePlus_eq h c s, mul_sub, mul_add, sub_mul, add_mul,
        mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
        mul_smul_comm, smul_mul_assoc,
        polePlus_idem h, polePlus_idem h, polePlus_mul_poleMinus h, zero_mul,
        h_v_P]
    simp only [smul_zero, add_zero, sub_zero]

/-!
## 5. Node 3: Refutation Boundary (No Turning Without Nilpotent Seeds)
-/

/-- **Refutation Boundary (`no_turning_iff_seeds_vanish`)**:
    The pole `P₊` is stationary under the wheel generator `J` (`[J, P₊] = 0`)
    if and only if both off-diagonal nilpotent seeds `d` and `B` vanish (`d = 0 ∧ B = 0`). -/
theorem no_turning_iff_seeds_vanish {d B : A} (h : IsDualSeedPair d B) :
    lieBracket (wheelGenerator d B) (polePlus d B) = 0 ↔ (d = 0 ∧ B = 0) := by
  rw [lieBracket_wheel_polePlus h, neg_eq_zero]
  unfold transitionVelocity
  constructor
  · intro h_sum
    have hd_zero : d = 0 := by
      calc d = d * B * d := h.dBd.symm
        _ = (d * B) * (d + B) - d * (B * B) := by noncomm_ring
        _ = 0 := by rw [h_sum, h.B_sq, mul_zero, mul_zero, sub_zero]
    have hB_zero : B = 0 := by
      calc B = (d + B) - d := by abel
        _ = 0 := by rw [h_sum, hd_zero, sub_self]
    exact ⟨hd_zero, hB_zero⟩
  · rintro ⟨rfl, rfl⟩
    exact add_zero 0

end UniversalRotorAlternation

/-!
## 6. Concrete Noncommutative Matrix Witness in `Matrix (Fin 2) (Fin 2) ℤ`
-/

section ConcreteMatrixWitness

abbrev Mat2Z := Matrix (Fin 2) (Fin 2) ℤ

/-- Off-diagonal nilpotent seed `d₂ = E₀₁` in `Matrix (Fin 2) (Fin 2) ℤ`. -/
def seedD : Mat2Z := !![0, 1; 0, 0]

/-- Dual off-diagonal nilpotent seed `B₂ = E₁₀` in `Matrix (Fin 2) (Fin 2) ℤ`. -/
def seedB : Mat2Z := !![0, 0; 1, 0]

lemma mat2Z_isDualSeedPair : IsDualSeedPair seedD seedB where
  d_sq := by decide
  B_sq := by decide
  dBd := by decide
  BdB := by decide

/-- Concrete non-vacuity witness in `Matrix (Fin 2) (Fin 2) ℤ` verifying:
    - Non-commutativity `seedD * seedB ≠ seedB * seedD`
    - Non-vanishing turning velocity `[J, P₊] = -Q₁ ≠ 0`
    - Harmonic oscillator restoring acceleration `[J, [J, Γ]] = -(4 • Γ)`
    - Quarter-turn pole trade `P₊(0, 1) = P₋` and `P₋(0, 1) = P₊`
    - Pythagorean `(c, s) = (3, 4)` seed-growth matrix identity
      `P₊(3, 4) = 9 • P₊ + 16 • P₋ - 12 • Q₁ = !![9, -12; -12, 16]`. -/
theorem mat2Z_rotor_alternation_witness :
    seedD * seedB ≠ seedB * seedD ∧
    lieBracket (wheelGenerator seedD seedB) (polePlus seedD seedB) ≠ 0 ∧
    lieBracket (wheelGenerator seedD seedB)
      (lieBracket (wheelGenerator seedD seedB) (phasePolarization seedD seedB)) =
      -(4 • phasePolarization seedD seedB) ∧
    movingPolePlus (0 : ℤ) (1 : ℤ) seedD seedB = poleMinus seedD seedB ∧
    movingPoleMinus (0 : ℤ) (1 : ℤ) seedD seedB = polePlus seedD seedB ∧
    movingPolePlus (3 : ℤ) (4 : ℤ) seedD seedB = !![9, -12; -12, 16] := by
  decide

end ConcreteMatrixWitness

/-!
## 7. Diamond Causal Poset (`DeBruijnRotorArchetype`) & Meta Epistemic Compiler Certification
-/

section MetaEpistemicCompilerCertification

open InfoGeometry.MetaCompiler
open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.ProofCarryingSchedule
open InfoGeometry.Causal.CertifiedDependencyCompiler

/-- The 4-node diamond causal poset of Stream 5. -/
inductive DeBruijnRotorArchetype where
  | deBruijnOneHillTwoPoles
  | infinitesimalAlternationOscillator
  | algebraicCircularRotor
  | movingIdempotentAndNonCommutingWitness
  deriving DecidableEq, Repr, Inhabited

namespace DeBruijnRotorArchetype

private def equivFin : DeBruijnRotorArchetype ≃ Fin 4 where
  toFun
    | .deBruijnOneHillTwoPoles => 0
    | .infinitesimalAlternationOscillator => 1
    | .algebraicCircularRotor => 2
    | .movingIdempotentAndNonCommutingWitness => 3
  invFun
    | 0 => .deBruijnOneHillTwoPoles
    | 1 => .infinitesimalAlternationOscillator
    | 2 => .algebraicCircularRotor
    | _ => .movingIdempotentAndNonCommutingWitness
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance instFintype : Fintype DeBruijnRotorArchetype :=
  Fintype.ofEquiv (Fin 4) equivFin.symm

/-- Diamond prerequisite map:
    - `deBruijnOneHillTwoPoles` is the root (Node 0)
    - `infinitesimalAlternationOscillator` (Node 1) and `algebraicCircularRotor` (Node 2)
      are incomparable parallel branches above Node 0
    - `movingIdempotentAndNonCommutingWitness` (Node 3) joins Node 1 and Node 2. -/
def prerequisites : DeBruijnRotorArchetype → Finset DeBruijnRotorArchetype
  | .deBruijnOneHillTwoPoles => {.deBruijnOneHillTwoPoles}
  | .infinitesimalAlternationOscillator =>
      {.deBruijnOneHillTwoPoles, .infinitesimalAlternationOscillator}
  | .algebraicCircularRotor =>
      {.deBruijnOneHillTwoPoles, .algebraicCircularRotor}
  | .movingIdempotentAndNonCommutingWitness =>
      {.deBruijnOneHillTwoPoles, .infinitesimalAlternationOscillator,
       .algebraicCircularRotor, .movingIdempotentAndNonCommutingWitness}

instance instPartialOrder : PartialOrder DeBruijnRotorArchetype where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro a b
    cases a <;> cases b <;> decide

instance instDecidableLE : DecidableLE DeBruijnRotorArchetype := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

instance instDecidableLT : DecidableLT DeBruijnRotorArchetype := fun a b =>
  decidable_of_iff (a ≤ b ∧ ¬ b ≤ a) lt_iff_le_not_ge.symm

/-- Node 1 (`infinitesimalAlternationOscillator`) and Node 2 (`algebraicCircularRotor`)
    are causally incomparable parallel branches in the diamond poset. -/
theorem oscillator_and_rotor_branches_incomparable :
    ¬ (infinitesimalAlternationOscillator ≤ algebraicCircularRotor) ∧
    ¬ (algebraicCircularRotor ≤ infinitesimalAlternationOscillator) := by
  decide

def canonicalPending : List DeBruijnRotorArchetype :=
  [.movingIdempotentAndNonCommutingWitness, .algebraicCircularRotor,
   .infinitesimalAlternationOscillator, .deBruijnOneHillTwoPoles]

def canonicalSchedule : List DeBruijnRotorArchetype :=
  [.deBruijnOneHillTwoPoles, .algebraicCircularRotor,
   .infinitesimalAlternationOscillator, .movingIdempotentAndNonCommutingWitness]

theorem canonicalPending_nodup : canonicalPending.Nodup := by decide

theorem canonicalPending_univ : canonicalPending.toFinset = Finset.univ := by decide

theorem compile_canonicalPending :
    compile (∅ : Finset DeBruijnRotorArchetype) canonicalPending =
      some canonicalSchedule := by
  decide

end DeBruijnRotorArchetype

/-- Node 0 proved `TypedArchetype`: Off-diagonal seed localization & carrier invariance `[J, Δ] = 0`. -/
def arch0DeBruijnOneHillTwoPoles : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.DeBruijnRotorAlternationCycle.arch0DeBruijnOneHillTwoPoles
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    (polePlus seedD seedB * seedD * poleMinus seedD seedB = seedD ∧
     poleMinus seedD seedB * seedB * polePlus seedD seedB = seedB) ∧
    lieBracket (wheelGenerator seedD seedB) (carrierSupport seedD seedB) = 0
  evidence := fun _ =>
    ⟨seed_off_diagonal_localization mat2Z_isDualSeedPair,
     wheelGenerator_commutes_carrierSupport mat2Z_isDualSeedPair⟩

/-- Node 1 proved `TypedArchetype`: Harmonic Alternation Oscillator `[J, [J, Γ]] = -(4 • Γ)`. -/
def arch1InfinitesimalAlternationOscillator : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.DeBruijnRotorAlternationCycle.arch1InfinitesimalAlternationOscillator
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    lieBracket (wheelGenerator seedD seedB) (polePlus seedD seedB) =
      -transitionVelocity seedD seedB ∧
    lieBracket (wheelGenerator seedD seedB)
      (lieBracket (wheelGenerator seedD seedB) (phasePolarization seedD seedB)) =
      -(4 • phasePolarization seedD seedB)
  evidence := fun _ =>
    ⟨lieBracket_wheel_polePlus mat2Z_isDualSeedPair,
     harmonic_alternation_oscillator_law mat2Z_isDualSeedPair⟩

/-- Node 2 proved `TypedArchetype`: Algebraic Circular Rotor & Opposite-Seed Growth Formula. -/
def arch2AlgebraicCircularRotor : TypedArchetype (ℤ × ℤ) .proved where
  name := `InfoGeometry.Canonical.DeBruijnRotorAlternationCycle.arch2AlgebraicCircularRotor
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun p =>
    movingPolePlus p.1 p.2 seedD seedB =
      (p.1 * p.1) • polePlus seedD seedB + (p.2 * p.2) • poleMinus seedD seedB -
      (p.1 * p.2) • transitionVelocity seedD seedB ∧
    movingPolePlus (0 : ℤ) (1 : ℤ) seedD seedB = poleMinus seedD seedB
  evidence := fun p =>
    movingPolePlus_explicit_formula mat2Z_isDualSeedPair p.1 p.2

/-- Node 3 proved `TypedArchetype`: Refutation boundary (`[J, P₊] = 0 ↔ d = 0 ∧ B = 0`)
    and noncommutative matrix rotor witness. -/
def arch3MovingIdempotentAndNonCommutingWitness : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.DeBruijnRotorAlternationCycle.arch3MovingIdempotentAndNonCommutingWitness
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    (lieBracket (wheelGenerator seedD seedB) (polePlus seedD seedB) = 0 ↔
      (seedD = 0 ∧ seedB = 0)) ∧
    lieBracket (wheelGenerator seedD seedB) (polePlus seedD seedB) ≠ 0 ∧
    movingPolePlus (3 : ℤ) (4 : ℤ) seedD seedB = !![9, -12; -12, 16]
  evidence := fun _ =>
    ⟨no_turning_iff_seeds_vanish mat2Z_isDualSeedPair,
     mat2Z_rotor_alternation_witness.2.1,
     mat2Z_rotor_alternation_witness.2.2.2.2.2⟩

#register_archetype arch0DeBruijnOneHillTwoPoles
#register_archetype arch1InfinitesimalAlternationOscillator
#register_archetype arch2AlgebraicCircularRotor
#register_archetype arch3MovingIdempotentAndNonCommutingWitness

#audit_archetype arch0DeBruijnOneHillTwoPoles
#audit_archetype arch1InfinitesimalAlternationOscillator
#audit_archetype arch2AlgebraicCircularRotor
#audit_archetype arch3MovingIdempotentAndNonCommutingWitness

/-- Target statement map on the `DeBruijnRotorArchetype` poset. -/
def deBruijnRotorStatement : DeBruijnRotorArchetype → Prop
  | .deBruijnOneHillTwoPoles => arch0DeBruijnOneHillTwoPoles.claim ()
  | .infinitesimalAlternationOscillator => arch1InfinitesimalAlternationOscillator.claim ()
  | .algebraicCircularRotor => ∀ p : ℤ × ℤ, arch2AlgebraicCircularRotor.claim p
  | .movingIdempotentAndNonCommutingWitness => arch3MovingIdempotentAndNonCommutingWitness.claim ()

lemma deBruijnRotorRules : ProofRules deBruijnRotorStatement := by
  intro target _
  cases target with
  | deBruijnOneHillTwoPoles => exact arch0DeBruijnOneHillTwoPoles.discharge ()
  | infinitesimalAlternationOscillator => exact arch1InfinitesimalAlternationOscillator.discharge ()
  | algebraicCircularRotor => exact fun p => arch2AlgebraicCircularRotor.discharge p
  | movingIdempotentAndNonCommutingWitness =>
      exact arch3MovingIdempotentAndNonCommutingWitness.discharge ()

/-- Certified execution of the Meta Epistemic Compiler on the `DeBruijnRotorArchetype` diamond poset. -/
theorem debruijn_rotor_executable_certified_compilation :
    ∃ schedule : List DeBruijnRotorArchetype,
      compile ∅ DeBruijnRotorArchetype.canonicalPending = some schedule ∧
      ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧
      schedule.length = Fintype.card DeBruijnRotorArchetype ∧
      schedule.toFinset = Finset.univ ∧
      ∀ target, deBruijnRotorStatement target :=
  executable_certified_compilation
    deBruijnRotorStatement
    deBruijnRotorRules
    DeBruijnRotorArchetype.canonicalPending
    DeBruijnRotorArchetype.canonicalPending_nodup
    DeBruijnRotorArchetype.canonicalPending_univ

end MetaEpistemicCompilerCertification

end InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
