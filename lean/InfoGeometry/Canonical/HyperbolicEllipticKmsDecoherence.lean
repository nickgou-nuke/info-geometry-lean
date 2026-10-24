/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Formalization Team
-/
import Mathlib
import InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
import InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Meta.EpistemicCompilerChain
import InfoGeometry.Meta.MetaEpistemicCompiler

/-!
# Stream 6: Hyperbolic–Elliptic Geodesic Duality & KMS Diagonal Decoherence

This module formalizes the noncommutative algebraic duality between:
1. **Elliptic Moving Projectors (`ellipticPolePlus c s d B`)** along $c^2 + s^2 = 1$,
   whose chordal displacement $P_+^{\mathrm{ell}}(c, s) - P_+$ has positive-sign square
   $+s^2 \bullet \Delta$,
2. **Hyperbolic Moving Idempotents (`hyperbolicPolePlus u v d B`)** along $u^2 - v^2 = 1$,
   whose chordal displacement $P_+^{\mathrm{hyp}}(u, v) - P_+$ has opposite-sign square
   $-v^2 \bullet \Delta$ while remaining strictly idempotent ($P^2 = P$) and carrier-conserving
   ($P_+^{\mathrm{hyp}}(u, v) + P_-^{\mathrm{hyp}}(u, v) = \Delta$), and
3. **Diagonal Peirce Decoherence (`diagonalDecoherence`)**: projecting the elliptic moving
   projector $P_+^{\mathrm{ell}}(c, s)$ onto the diagonal Peirce subalgebra
   $P_+ X P_+ + P_- X P_-$ annihilates the off-diagonal transition velocity $-c s Q_1$
   and recovers Stream 3's `kmsModularWeight s c d B = s^2 \bullet P_- + c^2 \bullet P_+`.

All identities hold in an arbitrary noncommutative `[CommRing R] [Ring A] [Algebra R A]`.
-/

namespace InfoGeometry.Canonical.HyperbolicEllipticKmsDecoherence

open Matrix

section UniversalHyperbolicEllipticDuality

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

/-!
## 1. Primitives: Dual Seeds, Elliptic & Hyperbolic Moving Projectors, & KMS Weight
-/

/-- Symmetrized Jordan anticommutator `{X, Y} = X Y + Y X`. -/
def jordanProd (X Y : A) : A := X * Y + Y * X

/-- Antisymmetric Lie commutator `[X, Y] = X Y - Y X`. -/
def lieBracket (X Y : A) : A := X * Y - Y * X

/-- Reflexive square-zero seed pair `(d, B)`: `d^2 = 0`, `B^2 = 0`, `dBd = d`, `BdB = B`. -/
structure IsDualSeedPair (d B : A) : Prop where
  d_sq : d * d = 0
  B_sq : B * B = 0
  dBd : d * B * d = d
  BdB : B * d * B = B

/-- Equivalence with Stream 5's `DeBruijnRotorAlternationCycle.IsDualSeedPair`. -/
lemma isDualSeedPair_iff_stream5 (d B : A) :
    IsDualSeedPair d B ↔ DeBruijnRotorAlternationCycle.IsDualSeedPair d B :=
  ⟨fun h => ⟨h.d_sq, h.B_sq, h.dBd, h.BdB⟩, fun h => ⟨h.d_sq, h.B_sq, h.dBd, h.BdB⟩⟩

def polePlus (d B : A) : A := d * B
def poleMinus (d B : A) : A := B * d
def carrierSupport (d B : A) : A := polePlus d B + poleMinus d B
def phasePolarization (d B : A) : A := polePlus d B - poleMinus d B
def transitionVelocity (d B : A) : A := d + B
def wheelGenerator (d B : A) : A := d - B

/-- Elliptic moving projector `P_+^{ell}(c, s) = c^2 • P_+ + s^2 • P_- - (c * s) • Q₁`. -/
def ellipticPolePlus (c s : R) (d B : A) : A :=
  (c * c) • polePlus d B + (s * s) • poleMinus d B - (c * s) • transitionVelocity d B

/-- Hyperbolic moving idempotent `P_+^{hyp}(u, v) = u^2 • P_+ - v^2 • P_- - (u * v) • J`. -/
def hyperbolicPolePlus (u v : R) (d B : A) : A :=
  (u * u) • polePlus d B - (v * v) • poleMinus d B - (u * v) • wheelGenerator d B

/-- Complementary hyperbolic moving idempotent `P_-^{hyp}(u, v) = -v^2 • P_+ + u^2 • P_- + (u * v) • J`. -/
def hyperbolicPoleMinus (u v : R) (d B : A) : A :=
  -(v * v) • polePlus d B + (u * u) • poleMinus d B + (u * v) • wheelGenerator d B

/-- Hyperbolic chordal direction `V(u, v) = v • Γ - u • J`. -/
def hyperbolicChordalDir (u v : R) (d B : A) : A :=
  v • phasePolarization d B - u • wheelGenerator d B

/-- KMS modular density weight `ρ(s, c) = s^2 • P_- + c^2 • P_+` (definitionally Stream 3's `kmsModularWeight`). -/
def kmsModularWeight (s c : R) (d B : A) : A :=
  (s * s) • poleMinus d B + (c * c) • polePlus d B

/-- Diagonal Peirce decoherence projection `decohere(X) = P_+ X P_+ + P_- X P_-`. -/
def diagonalDecoherence (d B X : A) : A :=
  polePlus d B * X * polePlus d B + poleMinus d B * X * poleMinus d B

/-- Definitional coherence between Stream 6's `kmsModularWeight` and Stream 3's `kmsModularWeight`,
    and between Stream 6's `ellipticPolePlus` and Stream 5's `movingPolePlus_eq`. -/
theorem stream6_stream3_stream5_coherence {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    kmsModularWeight s c d B =
      UnifiedGeometryOperatorSignificance.kmsModularWeight s c d B ∧
    DeBruijnRotorAlternationCycle.movingPolePlus c s d B =
      ellipticPolePlus c s d B :=
  ⟨rfl, DeBruijnRotorAlternationCycle.movingPolePlus_eq
    ((isDualSeedPair_iff_stream5 d B).mp h) c s⟩

/-!
## 2. Node 0 Atomic Lemmas: Peirce & Wheel Absorption Identities
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

lemma phasePolarization_sq {d B : A} (h : IsDualSeedPair d B) :
    phasePolarization d B * phasePolarization d B = carrierSupport d B := by
  unfold phasePolarization carrierSupport
  rw [sub_mul, mul_sub, mul_sub, polePlus_idem h, polePlus_mul_poleMinus h,
      poleMinus_mul_polePlus h, poleMinus_idem h]
  abel

lemma wheelGenerator_sq {d B : A} (h : IsDualSeedPair d B) :
    wheelGenerator d B * wheelGenerator d B = -carrierSupport d B := by
  unfold wheelGenerator carrierSupport polePlus poleMinus
  calc (d - B) * (d - B) = d * d - (d * B + B * d) + B * B := by noncomm_ring
    _ = -(d * B + B * d) := by rw [h.d_sq, h.B_sq]; abel

lemma polePlus_mul_wheel {d B : A} (h : IsDualSeedPair d B) :
    polePlus d B * wheelGenerator d B = d := by
  have hdB_B : (d * B) * B = 0 := by rw [mul_assoc, h.B_sq, mul_zero]
  unfold polePlus wheelGenerator
  rw [mul_sub, h.dBd, hdB_B, sub_zero]

lemma wheel_mul_polePlus {d B : A} (h : IsDualSeedPair d B) :
    wheelGenerator d B * polePlus d B = -B := by
  have hd_dB : d * (d * B) = 0 := by rw [← mul_assoc, h.d_sq, zero_mul]
  have hB_dB : B * (d * B) = B := by rw [← mul_assoc, h.BdB]
  unfold polePlus wheelGenerator
  rw [sub_mul, hd_dB, hB_dB, zero_sub]

lemma poleMinus_mul_wheel {d B : A} (h : IsDualSeedPair d B) :
    poleMinus d B * wheelGenerator d B = -B := by
  have hBd_d : (B * d) * d = 0 := by rw [mul_assoc, h.d_sq, mul_zero]
  unfold poleMinus wheelGenerator
  rw [mul_sub, hBd_d, h.BdB, zero_sub]

lemma wheel_mul_poleMinus {d B : A} (h : IsDualSeedPair d B) :
    wheelGenerator d B * poleMinus d B = d := by
  have hd_Bd : d * (B * d) = d := by rw [← mul_assoc, h.dBd]
  have hB_Bd : B * (B * d) = 0 := by rw [← mul_assoc, h.B_sq, zero_mul]
  unfold poleMinus wheelGenerator
  rw [sub_mul, hd_Bd, hB_Bd, sub_zero]

lemma polarization_anticommutes_wheel {d B : A} (h : IsDualSeedPair d B) :
    jordanProd (phasePolarization d B) (wheelGenerator d B) = 0 := by
  unfold jordanProd phasePolarization
  rw [sub_mul, mul_sub, polePlus_mul_wheel h, poleMinus_mul_wheel h,
      wheel_mul_polePlus h, wheel_mul_poleMinus h]
  abel

/-!
## 3. Node 1 Atomic Lemmas: Hyperbolic Moving Idempotent & Opposite-Sign Chordal Square
-/

lemma hyperbolicPolePlus_sub_polePlus (u v : R) (d B : A) (h_uv : u * u - v * v = 1) :
    hyperbolicPolePlus u v d B - polePlus d B = v • hyperbolicChordalDir u v d B := by
  have h_u2 : u * u - 1 = v * v := by linear_combination h_uv
  unfold hyperbolicPolePlus hyperbolicChordalDir phasePolarization
  calc (u * u) • polePlus d B - (v * v) • poleMinus d B -
       (u * v) • wheelGenerator d B - polePlus d B
    _ = (u * u - 1) • polePlus d B - (v * v) • poleMinus d B -
        (u * v) • wheelGenerator d B := by rw [sub_smul, one_smul]; abel
    _ = v • (v • (polePlus d B - poleMinus d B) - u • wheelGenerator d B) := by
        rw [h_u2, smul_sub, smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, mul_comm v u]

lemma hyperbolicPolePlus_eq_polePlus_add_chordal (u v : R) (d B : A)
    (h_uv : u * u - v * v = 1) :
    hyperbolicPolePlus u v d B = polePlus d B + v • hyperbolicChordalDir u v d B := by
  have h_sub := hyperbolicPolePlus_sub_polePlus u v d B h_uv
  calc hyperbolicPolePlus u v d B
    _ = polePlus d B + (hyperbolicPolePlus u v d B - polePlus d B) := by abel
    _ = polePlus d B + v • hyperbolicChordalDir u v d B := by rw [h_sub]

lemma hyperbolicChordalDir_sq {d B : A} (h : IsDualSeedPair d B) (u v : R) :
    hyperbolicChordalDir u v d B * hyperbolicChordalDir u v d B =
      (v * v - u * u) • carrierSupport d B := by
  unfold hyperbolicChordalDir
  calc (v • phasePolarization d B - u • wheelGenerator d B) *
       (v • phasePolarization d B - u • wheelGenerator d B)
    _ = (v * v) • (phasePolarization d B * phasePolarization d B) +
        (u * u) • (wheelGenerator d B * wheelGenerator d B) -
        (v * u) • jordanProd (phasePolarization d B) (wheelGenerator d B) := by
        unfold jordanProd
        simp only [sub_mul, mul_sub, smul_mul_smul, smul_add, mul_comm u v]
        abel
    _ = (v * v - u * u) • carrierSupport d B := by
        rw [phasePolarization_sq h, wheelGenerator_sq h,
            polarization_anticommutes_wheel h, smul_neg, smul_zero, sub_zero,
            ← sub_eq_add_neg, ← sub_smul]

lemma jordanProd_polePlus_hyperbolicChordalDir {d B : A} (h : IsDualSeedPair d B) (u v : R) :
    jordanProd (polePlus d B) (hyperbolicChordalDir u v d B) =
      v • (2 • polePlus d B) - u • wheelGenerator d B := by
  unfold jordanProd hyperbolicChordalDir phasePolarization
  rw [mul_sub, sub_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
      mul_sub, sub_mul, polePlus_idem h, polePlus_mul_poleMinus h,
      poleMinus_mul_polePlus h, polePlus_mul_wheel h, wheel_mul_polePlus h,
      sub_zero, smul_neg, two_nsmul, smul_add]
  unfold wheelGenerator
  rw [smul_sub]
  abel

/-- **Exact Idempotence of the Hyperbolic Moving Projector (`u^2 - v^2 = 1`)**. -/
theorem hyperbolicPolePlus_idempotent {d B : A} (h : IsDualSeedPair d B)
    {u v : R} (h_uv : u * u - v * v = 1) :
    hyperbolicPolePlus u v d B * hyperbolicPolePlus u v d B =
      hyperbolicPolePlus u v d B := by
  have h_vu : v * v - u * u = -1 := by linear_combination -h_uv
  have h_V_sq : hyperbolicChordalDir u v d B * hyperbolicChordalDir u v d B =
      -carrierSupport d B := by
    rw [hyperbolicChordalDir_sq h u v, h_vu, neg_one_smul]
  rw [hyperbolicPolePlus_eq_polePlus_add_chordal u v d B h_uv]
  calc (polePlus d B + v • hyperbolicChordalDir u v d B) *
       (polePlus d B + v • hyperbolicChordalDir u v d B)
    _ = polePlus d B + v • jordanProd (polePlus d B) (hyperbolicChordalDir u v d B) -
        (v * v) • (polePlus d B + poleMinus d B) := by
        rw [add_mul, mul_add, mul_add, polePlus_idem h,
            mul_smul_comm, smul_mul_assoc, smul_mul_smul, h_V_sq, smul_neg]
        unfold jordanProd carrierSupport; rw [smul_add, smul_add]; abel
    _ = polePlus d B + v • hyperbolicChordalDir u v d B := by
        rw [jordanProd_polePlus_hyperbolicChordalDir h u v]
        unfold hyperbolicChordalDir phasePolarization
        simp only [smul_sub, smul_add, smul_smul, two_nsmul]
        abel

/-- **Hyperbolic Carrier Conservation (`P_+^{hyp}(u, v) + P_-^{hyp}(u, v) = Δ`)**. -/
theorem hyperbolicPoles_sum_eq_carrierSupport (d B : A) {u v : R}
    (h_uv : u * u - v * v = 1) :
    hyperbolicPolePlus u v d B + hyperbolicPoleMinus u v d B =
      carrierSupport d B := by
  unfold hyperbolicPolePlus hyperbolicPoleMinus carrierSupport
  calc ((u * u) • polePlus d B - (v * v) • poleMinus d B - (u * v) • wheelGenerator d B) +
       (-(v * v) • polePlus d B + (u * u) • poleMinus d B + (u * v) • wheelGenerator d B)
    _ = (u * u - v * v) • polePlus d B + (u * u - v * v) • poleMinus d B := by
        rw [neg_smul, sub_smul, sub_smul]; abel
    _ = polePlus d B + poleMinus d B := by rw [h_uv, one_smul, one_smul]

/-- **Hyperbolic Chordal Displacement Square & Sandwich Compression (`(P_+^{hyp}(u, v) - P_+)^2 = -(v * v) • Δ`)**. -/
theorem hyperbolic_timelike_chordal_metric {d B : A} (h : IsDualSeedPair d B)
    {u v : R} (h_uv : u * u - v * v = 1) :
    (hyperbolicPolePlus u v d B - polePlus d B) *
      (hyperbolicPolePlus u v d B - polePlus d B) = -((v * v) • carrierSupport d B) ∧
    polePlus d B * hyperbolicPolePlus u v d B * polePlus d B =
      (u * u) • polePlus d B := by
  have h_vu : v * v - u * u = -1 := by linear_combination -h_uv
  refine ⟨?_, ?_⟩
  · rw [hyperbolicPolePlus_sub_polePlus u v d B h_uv, smul_mul_smul,
        hyperbolicChordalDir_sq h u v, h_vu, neg_one_smul, smul_neg]
  · have h_w_P : polePlus d B * wheelGenerator d B * polePlus d B = 0 := by
      rw [polePlus_mul_wheel h]
      unfold polePlus; rw [← mul_assoc, h.d_sq, zero_mul]
    unfold hyperbolicPolePlus
    rw [mul_sub, mul_sub, sub_mul, sub_mul,
        mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
        mul_smul_comm, smul_mul_assoc,
        polePlus_idem h, polePlus_idem h, polePlus_mul_poleMinus h, zero_mul,
        h_w_P]
    simp only [smul_zero, sub_zero]

/-!
## 4. Node 2 Atomic Lemmas: Diagonal Peirce Decoherence = KMS Modular Weight
-/

lemma polePlus_sandwich_velocity {d B : A} (h : IsDualSeedPair d B) :
    polePlus d B * transitionVelocity d B * polePlus d B = 0 := by
  have hd_dB : d * (d * B) = 0 := by rw [← mul_assoc, h.d_sq, zero_mul]
  unfold transitionVelocity polePlus
  calc (d * B) * (d + B) * (d * B)
    _ = (d * B * d) * (d * B) + d * (B * B) * (d * B) := by noncomm_ring
    _ = 0 := by rw [h.dBd, hd_dB, h.B_sq, mul_zero, zero_mul, add_zero]

lemma poleMinus_sandwich_velocity {d B : A} (h : IsDualSeedPair d B) :
    poleMinus d B * transitionVelocity d B * poleMinus d B = 0 := by
  have hB_Bd : B * (B * d) = 0 := by rw [← mul_assoc, h.B_sq, zero_mul]
  unfold transitionVelocity poleMinus
  calc (B * d) * (d + B) * (B * d)
    _ = B * (d * d) * (B * d) + (B * d * B) * (B * d) := by noncomm_ring
    _ = 0 := by rw [h.d_sq, h.BdB, hB_Bd, mul_zero, zero_mul, add_zero]

lemma polePlus_sandwich_ellipticPolePlus {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    polePlus d B * ellipticPolePlus c s d B * polePlus d B =
      (c * c) • polePlus d B := by
  unfold ellipticPolePlus
  rw [mul_sub, mul_add, sub_mul, add_mul,
      mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
      mul_smul_comm, smul_mul_assoc,
      polePlus_idem h, polePlus_idem h, polePlus_mul_poleMinus h, zero_mul,
      polePlus_sandwich_velocity h]
  simp only [smul_zero, add_zero, sub_zero]

lemma poleMinus_sandwich_ellipticPolePlus {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    poleMinus d B * ellipticPolePlus c s d B * poleMinus d B =
      (s * s) • poleMinus d B := by
  unfold ellipticPolePlus
  rw [mul_sub, mul_add, sub_mul, add_mul,
      mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
      mul_smul_comm, smul_mul_assoc,
      poleMinus_mul_polePlus h, zero_mul, poleMinus_idem h, poleMinus_idem h,
      poleMinus_sandwich_velocity h]
  simp only [smul_zero, zero_add, sub_zero]

/-- **KMS Decoherence Bridge Theorem (`diagonalDecoherence_ellipticPolePlus_eq_kms`)**:
    Projecting the elliptic moving projector `ellipticPolePlus c s d B` onto the diagonal
    Peirce subalgebra `P_+ X P_+ + P_- X P_-` annihilates the off-diagonal velocity `-cs Q₁`
    and yields the exact KMS modular weight `kmsModularWeight s c d B`. -/
theorem diagonalDecoherence_ellipticPolePlus_eq_kms {d B : A}
    (h : IsDualSeedPair d B) (c s : R) :
    diagonalDecoherence d B (ellipticPolePlus c s d B) =
      kmsModularWeight s c d B := by
  unfold diagonalDecoherence kmsModularWeight
  rw [polePlus_sandwich_ellipticPolePlus h c s,
      poleMinus_sandwich_ellipticPolePlus h c s, add_comm]

/-!
## 5. Node 3: Refutation Boundary & Master Elliptic–Hyperbolic–KMS Synthesis
-/

/-- **Refutation Boundary (`no_hyperbolic_boost_iff_seeds_vanish`)**:
    The pole `P_+` commutes with the hyperbolic generator `Q₁ = d + B` (`[Q₁, P_+] = 0`)
    if and only if both off-diagonal nilpotent seeds `d` and `B` vanish (`d = 0 ∧ B = 0`). -/
theorem no_hyperbolic_boost_iff_seeds_vanish {d B : A} (h : IsDualSeedPair d B) :
    lieBracket (transitionVelocity d B) (polePlus d B) = 0 ↔ (d = 0 ∧ B = 0) := by
  have h5 := (isDualSeedPair_iff_stream5 d B).mp h
  have h_comm : lieBracket (transitionVelocity d B) (polePlus d B) = -(d - B) := by
    unfold lieBracket
    change DeBruijnRotorAlternationCycle.transitionVelocity d B *
        DeBruijnRotorAlternationCycle.polePlus d B -
      DeBruijnRotorAlternationCycle.polePlus d B *
        DeBruijnRotorAlternationCycle.transitionVelocity d B = -(d - B)
    rw [DeBruijnRotorAlternationCycle.velocity_mul_polePlus h5,
        DeBruijnRotorAlternationCycle.polePlus_mul_velocity h5]
    abel
  rw [h_comm, neg_eq_zero, sub_eq_zero]
  constructor
  · intro hdB
    have hd : d = 0 := by rw [← h.dBd, hdB, mul_assoc, h.B_sq, mul_zero]
    exact ⟨hd, hdB.symm.trans hd⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- **Master Elliptic–Hyperbolic–KMS Synthesis Theorem**. -/
theorem elliptic_hyperbolic_kms_master_synthesis {d B : A} (h : IsDualSeedPair d B)
    {c s u v : R} (h_cs : c * c + s * s = 1) (h_uv : u * u - v * v = 1) :
    (hyperbolicPolePlus u v d B * hyperbolicPolePlus u v d B = hyperbolicPolePlus u v d B ∧
     hyperbolicPolePlus u v d B + hyperbolicPoleMinus u v d B = carrierSupport d B) ∧
    ((hyperbolicPolePlus u v d B - polePlus d B) *
       (hyperbolicPolePlus u v d B - polePlus d B) = -((v * v) • carrierSupport d B) ∧
     polePlus d B * hyperbolicPolePlus u v d B * polePlus d B = (u * u) • polePlus d B) ∧
    (diagonalDecoherence d B (ellipticPolePlus c s d B) = kmsModularWeight s c d B ∧
     (ellipticPolePlus c s d B - polePlus d B) *
       (ellipticPolePlus c s d B - polePlus d B) = (s * s) • carrierSupport d B) := by
  have h5 := (isDualSeedPair_iff_stream5 d B).mp h
  have h_ell_eq : DeBruijnRotorAlternationCycle.movingPolePlus c s d B =
      ellipticPolePlus c s d B :=
    (stream6_stream3_stream5_coherence h c s).2
  have h_ell_chordal : (ellipticPolePlus c s d B - polePlus d B) *
      (ellipticPolePlus c s d B - polePlus d B) = (s * s) • carrierSupport d B := by
    rw [← h_ell_eq]
    exact (DeBruijnRotorAlternationCycle.movingPolePlus_chordal_square_and_compression h5 h_cs).1
  exact ⟨⟨hyperbolicPolePlus_idempotent h h_uv,
          hyperbolicPoles_sum_eq_carrierSupport d B h_uv⟩,
         hyperbolic_timelike_chordal_metric h h_uv,
         ⟨diagonalDecoherence_ellipticPolePlus_eq_kms h c s, h_ell_chordal⟩⟩

end UniversalHyperbolicEllipticDuality

/-!
## 6. Concrete Non-Vacuity Witness on `Matrix (Fin 2) (Fin 2) ℚ` at `(3/5, 4/5)` & `(5/3, 4/3)`
-/

section ConcreteRationalWitness

abbrev Mat2Q := Matrix (Fin 2) (Fin 2) ℚ

def seedDQ : Mat2Q := !![0, 1; 0, 0]
def seedBQ : Mat2Q := !![0, 0; 1, 0]

lemma mat2Q_isDualSeedPair : IsDualSeedPair seedDQ seedBQ where
  d_sq := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [seedDQ, Matrix.mul_apply, Fin.sum_univ_two]
  B_sq := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [seedBQ, Matrix.mul_apply, Fin.sum_univ_two]
  dBd := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [seedDQ, seedBQ, Matrix.mul_apply, Fin.sum_univ_two]
  BdB := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [seedDQ, seedBQ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Concrete noncommutative rational matrix witness at the Pythagorean unit-circle point
    `(c, s) = (3/5, 4/5)` (`c^2 + s^2 = 1`) and the Pythagorean unit-hyperbola point
    `(u, v) = (5/3, 4/3)` (`u^2 - v^2 = 1`). -/
theorem mat2Q_elliptic_hyperbolic_kms_witness :
    seedDQ * seedBQ ≠ seedBQ * seedDQ ∧
    ((3 / 5 : ℚ) * (3 / 5) + (4 / 5) * (4 / 5) = 1 ∧
     (5 / 3 : ℚ) * (5 / 3) - (4 / 3) * (4 / 3) = 1) ∧
    ellipticPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ *
      ellipticPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ =
      ellipticPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ ∧
    hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ *
      hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ =
      hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ ∧
    (ellipticPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ - polePlus seedDQ seedBQ) *
      (ellipticPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ - polePlus seedDQ seedBQ) =
      (16 / 25 : ℚ) • carrierSupport seedDQ seedBQ ∧
    (hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ - polePlus seedDQ seedBQ) *
      (hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ - polePlus seedDQ seedBQ) =
      -((16 / 9 : ℚ) • carrierSupport seedDQ seedBQ) ∧
    diagonalDecoherence seedDQ seedBQ (ellipticPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ) =
      kmsModularWeight (4 / 5 : ℚ) (3 / 5 : ℚ) seedDQ seedBQ := by
  have hcs : (3 / 5 : ℚ) * (3 / 5) + (4 / 5) * (4 / 5) = 1 := by norm_num
  have huv : (5 / 3 : ℚ) * (5 / 3) - (4 / 3) * (4 / 3) = 1 := by norm_num
  have h_ne : seedDQ * seedBQ ≠ seedBQ * seedDQ := by
    intro h_eq
    have h00 := congr_fun (congr_fun h_eq 0) 0
    norm_num [seedDQ, seedBQ, Matrix.mul_apply, Fin.sum_univ_two] at h00
  have h5 := (isDualSeedPair_iff_stream5 seedDQ seedBQ).mp mat2Q_isDualSeedPair
  have h_ell_idem : ellipticPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ *
      ellipticPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ =
      ellipticPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ := by
    rw [← (stream6_stream3_stream5_coherence mat2Q_isDualSeedPair (3 / 5 : ℚ) (4 / 5 : ℚ)).2]
    exact DeBruijnRotorAlternationCycle.movingPolePlus_idem h5 (3 / 5 : ℚ) (4 / 5 : ℚ) hcs
  have h_master := elliptic_hyperbolic_kms_master_synthesis mat2Q_isDualSeedPair hcs huv
  refine ⟨h_ne, ⟨hcs, huv⟩, h_ell_idem, h_master.1.1, ?_, ?_, h_master.2.2.1⟩
  · simpa only [show (4 / 5 : ℚ) * (4 / 5) = 16 / 25 by norm_num] using h_master.2.2.2
  · simpa only [show (4 / 3 : ℚ) * (4 / 3) = 16 / 9 by norm_num] using h_master.2.1.1

end ConcreteRationalWitness

/-!
## 7. Causal Poset & Meta Epistemic Registration (`HyperbolicEllipticKmsArchetype`)
-/

section CausalPosetAndMetaRegistration

open InfoGeometry.MetaCompiler
open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.ProofCarryingSchedule
open InfoGeometry.Causal.CertifiedDependencyCompiler

inductive HyperbolicEllipticKmsArchetype where
  | dualSeedPeirceAndCliffordBase
  | hyperbolicMovingIdempotentAndSpacetimeMetric
  | normalBundleKmsDecoherenceBridge
  | ellipticHyperbolicKmsSynthesisAndWitness
  deriving DecidableEq, Repr, Inhabited

namespace HyperbolicEllipticKmsArchetype

private def equivFin : HyperbolicEllipticKmsArchetype ≃ Fin 4 where
  toFun
    | .dualSeedPeirceAndCliffordBase => 0
    | .hyperbolicMovingIdempotentAndSpacetimeMetric => 1
    | .normalBundleKmsDecoherenceBridge => 2
    | .ellipticHyperbolicKmsSynthesisAndWitness => 3
  invFun
    | 0 => .dualSeedPeirceAndCliffordBase
    | 1 => .hyperbolicMovingIdempotentAndSpacetimeMetric
    | 2 => .normalBundleKmsDecoherenceBridge
    | _ => .ellipticHyperbolicKmsSynthesisAndWitness
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance instFintype : Fintype HyperbolicEllipticKmsArchetype :=
  Fintype.ofEquiv (Fin 4) equivFin.symm

def prerequisites : HyperbolicEllipticKmsArchetype → Finset HyperbolicEllipticKmsArchetype
  | .dualSeedPeirceAndCliffordBase => {.dualSeedPeirceAndCliffordBase}
  | .hyperbolicMovingIdempotentAndSpacetimeMetric =>
      {.dualSeedPeirceAndCliffordBase, .hyperbolicMovingIdempotentAndSpacetimeMetric}
  | .normalBundleKmsDecoherenceBridge =>
      {.dualSeedPeirceAndCliffordBase, .normalBundleKmsDecoherenceBridge}
  | .ellipticHyperbolicKmsSynthesisAndWitness =>
      {.dualSeedPeirceAndCliffordBase,
       .hyperbolicMovingIdempotentAndSpacetimeMetric,
       .normalBundleKmsDecoherenceBridge,
       .ellipticHyperbolicKmsSynthesisAndWitness}

instance instPartialOrder : PartialOrder HyperbolicEllipticKmsArchetype where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro a b
    cases a <;> cases b <;> decide

instance instDecidableLE : DecidableLE HyperbolicEllipticKmsArchetype := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

instance instDecidableLT : DecidableLT HyperbolicEllipticKmsArchetype := fun a b =>
  decidable_of_iff (a ≤ b ∧ ¬ b ≤ a) lt_iff_le_not_ge.symm

theorem hyperbolic_and_kms_branches_incomparable :
    ¬ (hyperbolicMovingIdempotentAndSpacetimeMetric ≤ normalBundleKmsDecoherenceBridge) ∧
    ¬ (normalBundleKmsDecoherenceBridge ≤ hyperbolicMovingIdempotentAndSpacetimeMetric) := by
  decide

def canonicalPending : List HyperbolicEllipticKmsArchetype := [
  .ellipticHyperbolicKmsSynthesisAndWitness,
  .normalBundleKmsDecoherenceBridge,
  .hyperbolicMovingIdempotentAndSpacetimeMetric,
  .dualSeedPeirceAndCliffordBase
]

def canonicalSchedule : List HyperbolicEllipticKmsArchetype := [
  .dualSeedPeirceAndCliffordBase,
  .normalBundleKmsDecoherenceBridge,
  .hyperbolicMovingIdempotentAndSpacetimeMetric,
  .ellipticHyperbolicKmsSynthesisAndWitness
]

theorem canonicalPending_nodup : canonicalPending.Nodup := by decide

theorem canonicalPending_univ : canonicalPending.toFinset = Finset.univ := by decide

theorem compile_canonicalPending :
    compile (∅ : Finset HyperbolicEllipticKmsArchetype) canonicalPending =
      some canonicalSchedule := by
  decide

end HyperbolicEllipticKmsArchetype

def arch0DualSeedPeirceAndCliffordBase : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.HyperbolicEllipticKmsDecoherence.arch0DualSeedPeirceAndCliffordBase
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    phasePolarization seedDQ seedBQ * phasePolarization seedDQ seedBQ =
      carrierSupport seedDQ seedBQ ∧
    wheelGenerator seedDQ seedBQ * wheelGenerator seedDQ seedBQ =
      -carrierSupport seedDQ seedBQ ∧
    jordanProd (phasePolarization seedDQ seedBQ) (wheelGenerator seedDQ seedBQ) = 0
  evidence := fun _ =>
    ⟨phasePolarization_sq mat2Q_isDualSeedPair,
     wheelGenerator_sq mat2Q_isDualSeedPair,
     polarization_anticommutes_wheel mat2Q_isDualSeedPair⟩

def arch1HyperbolicMovingIdempotentAndSpacetimeMetric : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.HyperbolicEllipticKmsDecoherence.arch1HyperbolicMovingIdempotentAndSpacetimeMetric
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ *
      hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ =
      hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ ∧
    (hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ - polePlus seedDQ seedBQ) *
      (hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ - polePlus seedDQ seedBQ) =
      -((16 / 9 : ℚ) • carrierSupport seedDQ seedBQ)
  evidence := fun _ =>
    ⟨mat2Q_elliptic_hyperbolic_kms_witness.2.2.2.1,
     mat2Q_elliptic_hyperbolic_kms_witness.2.2.2.2.2.1⟩

def arch2NormalBundleKmsDecoherenceBridge : TypedArchetype (ℚ × ℚ) .proved where
  name := `InfoGeometry.Canonical.HyperbolicEllipticKmsDecoherence.arch2NormalBundleKmsDecoherenceBridge
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun p =>
    diagonalDecoherence seedDQ seedBQ (ellipticPolePlus p.1 p.2 seedDQ seedBQ) =
      kmsModularWeight p.2 p.1 seedDQ seedBQ
  evidence := fun p =>
    diagonalDecoherence_ellipticPolePlus_eq_kms mat2Q_isDualSeedPair p.1 p.2

def arch3EllipticHyperbolicKmsSynthesisAndWitness : TypedArchetype Unit .proved where
  name := `InfoGeometry.Canonical.HyperbolicEllipticKmsDecoherence.arch3EllipticHyperbolicKmsSynthesisAndWitness
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    seedDQ * seedBQ ≠ seedBQ * seedDQ ∧
    ((3 / 5 : ℚ) * (3 / 5) + (4 / 5) * (4 / 5) = 1 ∧
     (5 / 3 : ℚ) * (5 / 3) - (4 / 3) * (4 / 3) = 1) ∧
    ellipticPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ *
      ellipticPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ =
      ellipticPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ ∧
    hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ *
      hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ =
      hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ ∧
    (ellipticPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ - polePlus seedDQ seedBQ) *
      (ellipticPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ - polePlus seedDQ seedBQ) =
      (16 / 25 : ℚ) • carrierSupport seedDQ seedBQ ∧
    (hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ - polePlus seedDQ seedBQ) *
      (hyperbolicPolePlus (5 / 3 : ℚ) (4 / 3 : ℚ) seedDQ seedBQ - polePlus seedDQ seedBQ) =
      -((16 / 9 : ℚ) • carrierSupport seedDQ seedBQ) ∧
    diagonalDecoherence seedDQ seedBQ (ellipticPolePlus (3 / 5 : ℚ) (4 / 5 : ℚ) seedDQ seedBQ) =
      kmsModularWeight (4 / 5 : ℚ) (3 / 5 : ℚ) seedDQ seedBQ
  evidence := fun _ => mat2Q_elliptic_hyperbolic_kms_witness

#register_archetype arch0DualSeedPeirceAndCliffordBase
#register_archetype arch1HyperbolicMovingIdempotentAndSpacetimeMetric
#register_archetype arch2NormalBundleKmsDecoherenceBridge
#register_archetype arch3EllipticHyperbolicKmsSynthesisAndWitness

#audit_archetype arch0DualSeedPeirceAndCliffordBase
#audit_archetype arch1HyperbolicMovingIdempotentAndSpacetimeMetric
#audit_archetype arch2NormalBundleKmsDecoherenceBridge
#audit_archetype arch3EllipticHyperbolicKmsSynthesisAndWitness

def hyperbolicEllipticKmsStatement : HyperbolicEllipticKmsArchetype → Prop
  | .dualSeedPeirceAndCliffordBase => arch0DualSeedPeirceAndCliffordBase.claim ()
  | .hyperbolicMovingIdempotentAndSpacetimeMetric =>
      arch1HyperbolicMovingIdempotentAndSpacetimeMetric.claim ()
  | .normalBundleKmsDecoherenceBridge =>
      ∀ p : ℚ × ℚ, arch2NormalBundleKmsDecoherenceBridge.claim p
  | .ellipticHyperbolicKmsSynthesisAndWitness =>
      arch3EllipticHyperbolicKmsSynthesisAndWitness.claim ()

lemma hyperbolicEllipticKmsRules : ProofRules hyperbolicEllipticKmsStatement := by
  intro target _
  cases target with
  | dualSeedPeirceAndCliffordBase => exact arch0DualSeedPeirceAndCliffordBase.discharge ()
  | hyperbolicMovingIdempotentAndSpacetimeMetric =>
      exact arch1HyperbolicMovingIdempotentAndSpacetimeMetric.discharge ()
  | normalBundleKmsDecoherenceBridge =>
      exact fun p => arch2NormalBundleKmsDecoherenceBridge.discharge p
  | ellipticHyperbolicKmsSynthesisAndWitness =>
      exact arch3EllipticHyperbolicKmsSynthesisAndWitness.discharge ()

theorem hyperbolic_elliptic_kms_executable_certified_compilation :
    ∃ schedule : List HyperbolicEllipticKmsArchetype,
      compile ∅ HyperbolicEllipticKmsArchetype.canonicalPending = some schedule ∧
      ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧
      schedule.length = Fintype.card HyperbolicEllipticKmsArchetype ∧
      schedule.toFinset = Finset.univ ∧
      ∀ target, hyperbolicEllipticKmsStatement target :=
  executable_certified_compilation
    hyperbolicEllipticKmsStatement
    hyperbolicEllipticKmsRules
    HyperbolicEllipticKmsArchetype.canonicalPending
    HyperbolicEllipticKmsArchetype.canonicalPending_nodup
    HyperbolicEllipticKmsArchetype.canonicalPending_univ

end CausalPosetAndMetaRegistration

end InfoGeometry.Canonical.HyperbolicEllipticKmsDecoherence
