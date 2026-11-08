/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

open Matrix

namespace InfoGeometry.Canonical.TwoStateWeakSandwichBargmannLoop

variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]

/-!
## 1. Core Definitions: Dual Seeds, Elliptic & Hyperbolic Moving Projectors, & Two-State Sandwiches
-/

/-- Reflexive square-zero seed pair `(d, B)`: `d^2 = 0`, `B^2 = 0`, `dBd = d`, `BdB = B`. -/
structure IsDualSeedPair (d B : A) : Prop where
  d_sq : d * d = 0
  B_sq : B * B = 0
  dBd : d * B * d = d
  BdB : B * d * B = B

/-- Positive simplex pole idempotent `P_+ = d B`. -/
def polePlus (d B : A) : A := d * B

/-- Negative simplex pole idempotent `P_- = B d`. -/
def poleMinus (d B : A) : A := B * d

/-- Odd transition velocity `Q₁ = d + B`. -/
def transitionVelocity (d B : A) : A := d + B

/-- Skew-Majorana wheel generator `J = d - B`. -/
def wheelGenerator (d B : A) : A := d - B

/-- Elliptic moving projector `P_+^{ell}(c, s) = c^2 • P_+ + s^2 • P_- - (c * s) • Q₁`. -/
def ellipticPolePlus (c s : R) (d B : A) : A :=
  (c * c) • polePlus d B + (s * s) • poleMinus d B - (c * s) • transitionVelocity d B

/-- Hyperbolic moving idempotent `P_+^{hyp}(u, v) = u^2 • P_+ - v^2 • P_- - (u * v) • J`. -/
def hyperbolicPolePlus (u v : R) (d B : A) : A :=
  (u * u) • polePlus d B - (v * v) • poleMinus d B - (u * v) • wheelGenerator d B

/-!
## 2. Node 0 Atomic Lemmas: T4/T6-Clean Right & Left Peirce Absorption
-/

lemma polePlus_idem {d B : A} (h : IsDualSeedPair d B) :
    polePlus d B * polePlus d B = polePlus d B := by
  unfold polePlus
  calc (d * B) * (d * B) = (d * B * d) * B := by noncomm_ring
    _ = d * B := by rw [h.dBd]

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

lemma polePlus_mul_B {d B : A} (h : IsDualSeedPair d B) :
    polePlus d B * B = 0 := by
  unfold polePlus
  rw [mul_assoc, h.B_sq, mul_zero]

lemma d_mul_polePlus {d B : A} (h : IsDualSeedPair d B) :
    d * polePlus d B = 0 := by
  unfold polePlus
  rw [← mul_assoc, h.d_sq, zero_mul]

lemma B_mul_polePlus {d B : A} (h : IsDualSeedPair d B) :
    B * polePlus d B = B := by
  unfold polePlus
  rw [← mul_assoc, h.BdB]

lemma d_mul_poleMinus {d B : A} (h : IsDualSeedPair d B) :
    d * poleMinus d B = d := by
  unfold poleMinus
  rw [← mul_assoc, h.dBd]

lemma polePlus_mul_velocity {d B : A} (h : IsDualSeedPair d B) :
    polePlus d B * transitionVelocity d B = d := by
  unfold transitionVelocity
  rw [mul_add, polePlus_mul_B h, add_zero]
  exact h.dBd

lemma velocity_mul_polePlus {d B : A} (h : IsDualSeedPair d B) :
    transitionVelocity d B * polePlus d B = B := by
  unfold transitionVelocity
  rw [add_mul, d_mul_polePlus h, B_mul_polePlus h, zero_add]

lemma polePlus_mul_wheel {d B : A} (h : IsDualSeedPair d B) :
    polePlus d B * wheelGenerator d B = d := by
  unfold wheelGenerator
  rw [mul_sub, polePlus_mul_B h, sub_zero]
  exact h.dBd

/-!
## 3. Node 1 Atomic Lemmas: Division-Free Elliptic Two-State Sandwiches & Syzygy
-/

/-- **Forward Elliptic Overlap Sandwich (`P_+ * P_+^{ell}(c, s) = c^2 • P_+ - (c * s) • d`)**. -/
lemma polePlus_mul_ellipticPolePlus {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    polePlus d B * ellipticPolePlus c s d B =
      (c * c) • polePlus d B - (c * s) • d := by
  unfold ellipticPolePlus
  rw [mul_sub, mul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm,
      polePlus_idem h, polePlus_mul_poleMinus h, polePlus_mul_velocity h,
      smul_zero, add_zero]

/-- **Backward Elliptic Overlap Sandwich (`P_+^{ell}(c, s) * P_+ = c^2 • P_+ - (c * s) • B`)**. -/
lemma ellipticPolePlus_mul_polePlus {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    ellipticPolePlus c s d B * polePlus d B =
      (c * c) • polePlus d B - (c * s) • B := by
  unfold ellipticPolePlus
  rw [sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
      polePlus_idem h, poleMinus_mul_polePlus h, velocity_mul_polePlus h,
      smul_zero, add_zero]

/-- **Forward Two-State Velocity Sandwich (`P_+ * Q₁ * P_+^{ell}(c, s) = s^2 • d - (c * s) • P_+`)**. -/
theorem two_state_velocity_sandwich {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    polePlus d B * transitionVelocity d B * ellipticPolePlus c s d B =
      (s * s) • d - (c * s) • polePlus d B := by
  have hd_vel : d * transitionVelocity d B = polePlus d B := by
    unfold transitionVelocity polePlus; rw [mul_add, h.d_sq, zero_add]
  rw [polePlus_mul_velocity h]
  unfold ellipticPolePlus
  rw [mul_sub, mul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm,
      d_mul_polePlus h, d_mul_poleMinus h, hd_vel, smul_zero, zero_add]

/-- **Backward Two-State Velocity Sandwich (`P_+^{ell}(c, s) * Q₁ * P_+ = s^2 • B - (c * s) • P_+`)**. -/
theorem two_state_velocity_sandwich_rev {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    ellipticPolePlus c s d B * transitionVelocity d B * polePlus d B =
      (s * s) • B - (c * s) • polePlus d B := by
  have hvel_B : transitionVelocity d B * B = polePlus d B := by
    unfold transitionVelocity polePlus; rw [add_mul, h.B_sq, add_zero]
  rw [mul_assoc, velocity_mul_polePlus h]
  unfold ellipticPolePlus poleMinus
  rw [sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
      polePlus_mul_B h, h.BdB, hvel_B, smul_zero, zero_add]

/-- **Division-Free Elliptic Weak-Value Syzygy (`elliptic_weak_value_syzygy`)**:
    For ALL `c, s ∈ R`, the overlap sandwich `P_+ * P_+^{ell}(c, s)` and the velocity sandwich
    `P_+ * Q₁ * P_+^{ell}(c, s)` satisfy the exact division-free linear syzygy:
    `s • (P_+ * P_+^{ell}(c, s)) + c • (P_+ * Q₁ * P_+^{ell}(c, s)) = 0`! -/
theorem elliptic_weak_value_syzygy {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    s • (polePlus d B * ellipticPolePlus c s d B) +
    c • (polePlus d B * transitionVelocity d B * ellipticPolePlus c s d B) = 0 := by
  rw [polePlus_mul_ellipticPolePlus h c s, two_state_velocity_sandwich h c s,
      smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]
  have h_sc : s * (c * c) = c * (c * s) := by ring
  have h_cs : s * (c * s) = c * (s * s) := by ring
  rw [h_sc, h_cs]
  abel

/-!
## 4. Node 2 Atomic Lemmas: Division-Free Hyperbolic Two-State Sandwiches & Syzygy
-/

/-- **Forward Hyperbolic Overlap Sandwich (`P_+ * P_+^{hyp}(u, v) = u^2 • P_+ - (u * v) • d`)**. -/
lemma polePlus_mul_hyperbolicPolePlus {d B : A} (h : IsDualSeedPair d B) (u v : R) :
    polePlus d B * hyperbolicPolePlus u v d B =
      (u * u) • polePlus d B - (u * v) • d := by
  unfold hyperbolicPolePlus
  rw [mul_sub, mul_sub, mul_smul_comm, mul_smul_comm, mul_smul_comm,
      polePlus_idem h, polePlus_mul_poleMinus h, polePlus_mul_wheel h,
      smul_zero, sub_zero]

/-- **Forward Hyperbolic Wheel Sandwich (`P_+ * J * P_+^{hyp}(u, v) = -(v^2 • d) + (u * v) • P_+`)**. -/
theorem hyperbolic_two_state_wheel_sandwich {d B : A} (h : IsDualSeedPair d B) (u v : R) :
    polePlus d B * wheelGenerator d B * hyperbolicPolePlus u v d B =
      -((v * v) • d) + (u * v) • polePlus d B := by
  have hd_wheel : d * wheelGenerator d B = -polePlus d B := by
    unfold wheelGenerator polePlus; rw [mul_sub, h.d_sq, zero_sub]
  rw [polePlus_mul_wheel h]
  unfold hyperbolicPolePlus
  rw [mul_sub, mul_sub, mul_smul_comm, mul_smul_comm, mul_smul_comm,
      d_mul_polePlus h, d_mul_poleMinus h, hd_wheel, smul_zero, zero_sub,
      smul_neg, sub_neg_eq_add]

/-- **Division-Free Hyperbolic Weak-Value Syzygy (`hyperbolic_weak_value_syzygy`)**:
    For ALL `u, v ∈ R`:
    `v • (P_+ * P_+^{hyp}(u, v)) - u • (P_+ * J * P_+^{hyp}(u, v)) = 0`! -/
theorem hyperbolic_weak_value_syzygy {d B : A} (h : IsDualSeedPair d B) (u v : R) :
    v • (polePlus d B * hyperbolicPolePlus u v d B) -
    u • (polePlus d B * wheelGenerator d B * hyperbolicPolePlus u v d B) = 0 := by
  rw [polePlus_mul_hyperbolicPolePlus h u v, hyperbolic_two_state_wheel_sandwich h u v,
      smul_sub, smul_add, smul_neg, smul_smul, smul_smul, smul_smul, smul_smul]
  have h_vu : v * (u * u) = u * (u * v) := by ring
  have h_uv : v * (u * v) = u * (v * v) := by ring
  rw [h_vu, h_uv]
  abel

/-!
## 5. Node 3: Bargmann–Pancharatnam Holonomy Loops, Orthogonal-Pole Anomaly, & `M₂(ℤ)` Witness
-/

lemma bargmann_overlap_loop {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    (polePlus d B * ellipticPolePlus c s d B) *
    (ellipticPolePlus c s d B * polePlus d B) =
      ((c * c) * (c * c + s * s)) • polePlus d B := by
  rw [polePlus_mul_ellipticPolePlus h c s, ellipticPolePlus_mul_polePlus h c s]
  simp only [sub_mul, mul_sub, smul_mul_smul, polePlus_idem h,
    polePlus_mul_B h, d_mul_polePlus h, smul_zero, sub_zero, zero_sub,
    sub_neg_eq_add]
  change ((c * c) * (c * c)) • polePlus d B + ((c * s) * (c * s)) • polePlus d B =
    ((c * c) * (c * c + s * s)) • polePlus d B
  rw [← add_smul]
  have h_alg : (c * c) * (c * c) + (c * s) * (c * s) = (c * c) * (c * c + s * s) := by ring
  rw [h_alg]

lemma bargmann_velocity_loop {d B : A} (h : IsDualSeedPair d B) (c s : R) :
    (polePlus d B * transitionVelocity d B * ellipticPolePlus c s d B) *
    (ellipticPolePlus c s d B * transitionVelocity d B * polePlus d B) =
      ((s * s) * (c * c + s * s)) • polePlus d B := by
  rw [two_state_velocity_sandwich h c s, two_state_velocity_sandwich_rev h c s]
  simp only [sub_mul, mul_sub, smul_mul_smul, polePlus_idem h,
    polePlus_mul_B h, d_mul_polePlus h, smul_zero, sub_zero, zero_sub,
    sub_neg_eq_add]
  change ((s * s) * (s * s)) • polePlus d B + ((c * s) * (c * s)) • polePlus d B =
    ((s * s) * (c * c + s * s)) • polePlus d B
  rw [← add_smul]
  have h_alg : (s * s) * (s * s) + (c * s) * (c * s) = (s * s) * (c * c + s * s) := by ring
  rw [h_alg]

/-- **Bargmann–Pancharatnam Holonomy Loop Partition & Orthogonal-Pole Anomaly Master Theorem**. -/
theorem bargmann_pancharatnam_loop_and_anomaly_master {d B : A}
    (h : IsDualSeedPair d B) {c s : R} (h_cs : c * c + s * s = 1) :
    let W_id := polePlus d B * ellipticPolePlus c s d B
    let W_id_rev := ellipticPolePlus c s d B * polePlus d B
    let W_vel := polePlus d B * transitionVelocity d B * ellipticPolePlus c s d B
    let W_vel_rev := ellipticPolePlus c s d B * transitionVelocity d B * polePlus d B
    (polePlus d B * ellipticPolePlus (0 : R) (1 : R) d B = 0 ∧
     polePlus d B * transitionVelocity d B * ellipticPolePlus (0 : R) (1 : R) d B = d) ∧
    (W_id * W_id_rev = (c * c) • polePlus d B ∧
     W_vel * W_vel_rev = (s * s) • polePlus d B ∧
     W_id * W_id_rev + W_vel * W_vel_rev = polePlus d B) := by
  intro W_id W_id_rev W_vel W_vel_rev
  have h_orth_id : polePlus d B * ellipticPolePlus (0 : R) (1 : R) d B = 0 := by
    rw [polePlus_mul_ellipticPolePlus h (0 : R) (1 : R)]
    simp
  have h_orth_vel : polePlus d B * transitionVelocity d B * ellipticPolePlus (0 : R) (1 : R) d B = d := by
    rw [two_state_velocity_sandwich h (0 : R) (1 : R)]
    simp
  have h_loop_id : W_id * W_id_rev = (c * c) • polePlus d B := by
    unfold W_id W_id_rev; rw [bargmann_overlap_loop h c s, h_cs, mul_one]
  have h_loop_vel : W_vel * W_vel_rev = (s * s) • polePlus d B := by
    unfold W_vel W_vel_rev; rw [bargmann_velocity_loop h c s, h_cs, mul_one]
  have h_sum : W_id * W_id_rev + W_vel * W_vel_rev = polePlus d B := by
    rw [h_loop_id, h_loop_vel, ← add_smul, h_cs, one_smul]
  exact ⟨⟨h_orth_id, h_orth_vel⟩, ⟨h_loop_id, h_loop_vel, h_sum⟩⟩

/-- Concrete noncommutative `2 × 2` integer matrix seeds `matD = E_{01}`, `matB = E_{10}`. -/
def matD : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]
def matB : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

/-- Constructive `IsDualSeedPair` model witness on `M₂(ℤ)`. -/
lemma mat2Z_isDualSeedPair : IsDualSeedPair matD matB where
  d_sq := by decide
  B_sq := by decide
  dBd := by decide
  BdB := by decide

/-- **Concrete Noncommutative `M₂(ℤ)` Orthogonal-Pole Weak-Anomaly Witness**:
    At `(c, s) = (0, 1)`, the overlap `P_+ * P_+(0, 1)` vanishes identically, yet the
    two-state velocity sandwich `P_+ * Q₁ * P_+(0, 1)` is `matD ≠ 0`! -/
theorem mat2Z_two_state_weak_sandwich_witness :
    IsDualSeedPair matD matB ∧
    polePlus matD matB * ellipticPolePlus (0 : ℤ) 1 matD matB = 0 ∧
    polePlus matD matB * transitionVelocity matD matB *
      ellipticPolePlus (0 : ℤ) 1 matD matB = matD ∧
    matD ≠ 0 := by
  have h_cs : (0 : ℤ) * 0 + 1 * 1 = 1 := by ring
  rcases (bargmann_pancharatnam_loop_and_anomaly_master mat2Z_isDualSeedPair h_cs).1 with
    ⟨h_id0, h_vel_d⟩
  have hd_ne : matD ≠ 0 := by decide
  exact ⟨mat2Z_isDualSeedPair, h_id0, h_vel_d, hd_ne⟩

end InfoGeometry.Canonical.TwoStateWeakSandwichBargmannLoop
