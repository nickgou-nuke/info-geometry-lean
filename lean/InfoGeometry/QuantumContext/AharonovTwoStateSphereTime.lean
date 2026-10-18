/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Section 116: $S^3$ Radial Dilatation Time, Aharonov Two-State Vectors, and Negative Weak Dwell Times

This module formalizes:
1. **Concentric $S^3$ Shells in $\mathbb{R}^4$ (`Sphere4D R`)**: Squared radius
   $\|X\|^2 = w^2 + x^2 + y^2 + z^2$, Weyl radial dilatation scaling $\|s \cdot X\|^2 = s^2 \|X\|^2$,
   and the forward-backward thermofield twin shell horizon invariant
   $(r_0 e^\tau)(r_0 e^{-\tau}) = r_0^2$.
2. **Aharonov–Bergmann–Lebowitz Two-State Vector Formalism (`SlitState2D R`)**: Two-slit
   interference space equipped with slit projectors $\hat{P}_1, \hat{P}_2$, single-vector Born
   positivity ($0 \le \langle \psi | \hat{P}_1 | \psi \rangle$), and the two-state weak partition
   of unity $\langle \phi | \hat{P}_1 \psi \rangle + \langle \phi | \hat{P}_2 \psi \rangle = \langle \phi | \psi \rangle$.
3. **Anomalous Negative Weak Dwell Time**: Constructive proof that for pre-selected forward state
   $\psi = (1, 1)$ and post-selected backward state $\phi = (1, -2)$ near a destructive
   interference fringe, the normalized weak value on Slit 1 is strictly negative ($W(\hat{P}_1) = -1 < 0$)
   while $W(\hat{P}_2) = 2$ and total weak probability is conserved ($W(\hat{P}_1) + W(\hat{P}_2) = 1$).
-/

namespace InfoGeometry.QuantumContext.AharonovTime

variable {R : Type*} [CommRing R]

/-! ## Section 1: 4D Euclidean Carrier and Concentric $S^3$ Shells (`Sphere4D R`) -/

/-- Four-dimensional Euclidean coordinate vector $(w, x, y, z)$ foliated by concentric $S^3$ shells. -/
@[ext]
structure Sphere4D (R : Type*) where
  w : R
  x : R
  y : R
  z : R
  deriving DecidableEq, Repr, Inhabited

namespace Sphere4D

variable {R : Type*} [CommRing R]

/-- Origin of the 4D carrier. -/
def zero : Sphere4D R := ⟨0, 0, 0, 0⟩

/-- Canonical unit point on the $S^3$ sphere over $\mathbb{Z}$. -/
def unitW : Sphere4D ℤ := ⟨1, 0, 0, 0⟩

/-- The canonical point `unitW` over $\mathbb{Z}$ is distinct from `zero`. -/
theorem unitW_ne_zero : unitW ≠ (zero : Sphere4D ℤ) := by
  intro h
  have h1 : unitW.w = (zero : Sphere4D ℤ).w := congrArg Sphere4D.w h
  revert h1
  decide

/-- Squared radius of the $S^3$ shell in $R^4$: $r^2 = w^2 + x^2 + y^2 + z^2$. -/
def radiusSq (X : Sphere4D R) : R :=
  X.w ^ 2 + X.x ^ 2 + X.y ^ 2 + X.z ^ 2

/-- Radial Weyl dilatation of the $S^3$ shell by scale factor $s = \exp(\tau)$. -/
def dilate (s : R) (X : Sphere4D R) : Sphere4D R :=
  ⟨s * X.w, s * X.x, s * X.y, s * X.z⟩

/-- **Radial Dilatation Scaling Law**:
    Dilating the 4D coordinates by $s$ scales the $S^3$ squared radius by $s^2$. -/
theorem radiusSq_dilate (s : R) (X : Sphere4D R) :
    radiusSq (dilate s X) = s ^ 2 * radiusSq X := by
  dsimp [radiusSq, dilate]
  ring

/-- **Radial Shell Perturbation Expansion**:
    For a shell perturbation $r = r_0 + \delta r$, the squared radius expands around $r_0^2$
    with linear radial term $2 r_0 \delta r$ and quadratic remainder $\delta r^2$. -/
theorem shell_deviation_expansion (r₀ δr : R) :
    (r₀ + δr) ^ 2 - r₀ ^ 2 = 2 * r₀ * δr + δr ^ 2 := by
  ring

/-- **Forward–Backward Twin Shell Horizon Invariance**:
    When the forward shell expands by `exp_pos` and the backward twin shell contracts by
    `exp_neg` with `exp_pos * exp_neg = 1`, the product of their radii is locked to $r_0^2$. -/
theorem twin_shell_horizon_lock (r₀ exp_pos exp_neg : R)
    (h_inv : exp_pos * exp_neg = 1) :
    (r₀ * exp_pos) * (r₀ * exp_neg) = r₀ ^ 2 := by
  calc (r₀ * exp_pos) * (r₀ * exp_neg)
    _ = r₀ ^ 2 * (exp_pos * exp_neg) := by ring
    _ = r₀ ^ 2 * 1 := by rw [h_inv]
    _ = r₀ ^ 2 := by ring

end Sphere4D

/-! ## Section 2: Double-Slit Two-State Vector Formalism (`SlitState2D R`) -/

/-- Two-component state vector in the double-slit interference space ($\text{Slit 1} \oplus \text{Slit 2}$). -/
@[ext]
structure SlitState2D (R : Type*) where
  s₁ : R
  s₂ : R
  deriving DecidableEq, Repr, Inhabited

namespace SlitState2D

variable {R : Type*} [CommRing R]

/-- Zero double-slit state. -/
def zero : SlitState2D R := ⟨0, 0⟩

/-- Componentwise addition of double-slit states. -/
def add (ϕ ψ : SlitState2D R) : SlitState2D R :=
  ⟨ϕ.s₁ + ψ.s₁, ϕ.s₂ + ψ.s₂⟩

/-- Bilinear pairing $\langle \phi | \psi \rangle = \phi_1 \psi_1 + \phi_2 \psi_2$ between a
    backward post-selected state $\langle \phi|$ and a forward pre-selected state $|\psi\rangle$. -/
def bracket (ϕ ψ : SlitState2D R) : R :=
  ϕ.s₁ * ψ.s₁ + ϕ.s₂ * ψ.s₂

/-- Slit 1 projection operator $\hat{P}_1(\psi_1, \psi_2) = (\psi_1, 0)$. -/
def projSlit1 (ψ : SlitState2D R) : SlitState2D R :=
  ⟨ψ.s₁, 0⟩

/-- Slit 2 projection operator $\hat{P}_2(\psi_1, \psi_2) = (0, \psi_2)$. -/
def projSlit2 (ψ : SlitState2D R) : SlitState2D R :=
  ⟨0, ψ.s₂⟩

/-- Idempotency of the Slit 1 projector: $\hat{P}_1(\hat{P}_1(\psi)) = \hat{P}_1(\psi)$. -/
@[simp]
theorem projSlit1_idempotent (ψ : SlitState2D R) :
    projSlit1 (projSlit1 ψ) = projSlit1 ψ := by
  rfl

/-- Idempotency of the Slit 2 projector: $\hat{P}_2(\hat{P}_2(\psi)) = \hat{P}_2(\psi)$. -/
@[simp]
theorem projSlit2_idempotent (ψ : SlitState2D R) :
    projSlit2 (projSlit2 ψ) = projSlit2 ψ := by
  rfl

/-- Mutual orthogonality of Slit 1 and Slit 2 projectors: $\hat{P}_1(\hat{P}_2(\psi)) = 0$. -/
@[simp]
theorem projSlit1_projSlit2_zero (ψ : SlitState2D R) :
    projSlit1 (projSlit2 ψ) = zero := by
  rfl

/-- Completeness of Slit 1 and Slit 2 projectors: $\hat{P}_1(\psi) + \hat{P}_2(\psi) = \psi$. -/
theorem projSlit_partition_of_unity (ψ : SlitState2D R) :
    add (projSlit1 ψ) (projSlit2 ψ) = ψ := by
  ext <;> dsimp [add, projSlit1, projSlit2] <;> ring

/-- **Standard Single-Vector Born Positivity (Slit 1)**:
    In standard single-vector quantum mechanics ($\phi = \psi$), the expectation value of
    $\hat{P}_1$ equals $\psi_1^2 \ge 0$ and is never negative. -/
theorem standard_qm_slit1_nonneg [LinearOrder R] [IsStrictOrderedRing R] (ψ : SlitState2D R) :
    0 ≤ bracket ψ (projSlit1 ψ) := by
  dsimp [bracket, projSlit1]
  have h_eq : ψ.s₁ * ψ.s₁ + ψ.s₂ * 0 = ψ.s₁ ^ 2 := by ring
  rw [h_eq]
  exact sq_nonneg ψ.s₁

/-- **Standard Single-Vector Born Positivity (Slit 2)**:
    In standard single-vector quantum mechanics ($\phi = \psi$), the expectation value of
    $\hat{P}_2$ equals $\psi_2^2 \ge 0$. -/
theorem standard_qm_slit2_nonneg [LinearOrder R] [IsStrictOrderedRing R] (ψ : SlitState2D R) :
    0 ≤ bracket ψ (projSlit2 ψ) := by
  dsimp [bracket, projSlit2]
  have h_eq : ψ.s₁ * 0 + ψ.s₂ * ψ.s₂ = ψ.s₂ ^ 2 := by ring
  rw [h_eq]
  exact sq_nonneg ψ.s₂

/-- **Aharonov Two-State Weak Partition of Unity**:
    For any pre-selected state $|\psi\rangle$ and post-selected state $\langle \phi|$, the sum
    of the two-state transition amplitudes across Slit 1 and Slit 2 equals the total overlap
    $\langle \phi | \psi \rangle$. -/
theorem two_state_weak_partition (ϕ ψ : SlitState2D R) :
    bracket ϕ (projSlit1 ψ) + bracket ϕ (projSlit2 ψ) = bracket ϕ ψ := by
  dsimp [bracket, projSlit1, projSlit2]
  ring

/-! ## Section 3: Anomalous Negative Weak Dwell Time in Destructive Interference -/

/-- Pre-selected forward state $|\psi_{\mathrm{fwd}}\rangle = (1, 1)$ illuminating both slits symmetrically. -/
def forwardPreSelected : SlitState2D ℤ := ⟨1, 1⟩

/-- Post-selected backward state $\langle \phi_{\mathrm{bwd}}| = (1, -2)$ near a destructive fringe. -/
def backwardPostSelected : SlitState2D ℤ := ⟨1, -2⟩

/-- The pre-selected forward state `forwardPreSelected` is distinct from `zero`. -/
theorem forwardPreSelected_ne_zero : forwardPreSelected ≠ (zero : SlitState2D ℤ) := by
  intro h
  have h1 : forwardPreSelected.s₁ = (zero : SlitState2D ℤ).s₁ := congrArg SlitState2D.s₁ h
  revert h1
  decide

/-- Normalized weak value $W(\hat{P}_1) = -\langle \phi | \hat{P}_1 | \psi \rangle$ for unit-negative
    overlap $\langle \phi | \psi \rangle = -1$. -/
def normalizedWeakValue1 (ϕ ψ : SlitState2D R) : R :=
  - bracket ϕ (projSlit1 ψ)

/-- Normalized weak value $W(\hat{P}_2) = -\langle \phi | \hat{P}_2 | \psi \rangle$ for unit-negative
    overlap $\langle \phi | \psi \rangle = -1$. -/
def normalizedWeakValue2 (ϕ ψ : SlitState2D R) : R :=
  - bracket ϕ (projSlit2 ψ)

/-- **Anomalous Negative Weak Dwell Time in the Double-Slit Experiment**:
    For pre-selected $\psi = (1, 1)$ and post-selected $\phi = (1, -2)$:
    1. The two-state overlap is $\langle \phi | \psi \rangle = -1$.
    2. The normalized weak value (dwell time) in Slit 1 is strictly negative ($W(\hat{P}_1) = -1 < 0$).
    3. The normalized weak value in Slit 2 exceeds unity ($W(\hat{P}_2) = 2$).
    4. Total normalized weak probability is conserved ($W(\hat{P}_1) + W(\hat{P}_2) = 1$). -/
theorem double_slit_registers_negative_weak_time :
    bracket backwardPostSelected forwardPreSelected = -1 ∧
    normalizedWeakValue1 backwardPostSelected forwardPreSelected = -1 ∧
    normalizedWeakValue1 backwardPostSelected forwardPreSelected < 0 ∧
    normalizedWeakValue2 backwardPostSelected forwardPreSelected = 2 ∧
    normalizedWeakValue1 backwardPostSelected forwardPreSelected +
      normalizedWeakValue2 backwardPostSelected forwardPreSelected = 1 := by
  dsimp [forwardPreSelected, backwardPostSelected, bracket,
    normalizedWeakValue1, normalizedWeakValue2, projSlit1, projSlit2]
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

end SlitState2D

/-- **Section 116 Master Synthesis**:
    Combines $S^3$ radial dilatation scaling, twin-shell horizon locking, single-vector Born
    positivity, two-state weak partition of unity, and anomalous negative weak dwell time. -/
theorem aharonov_sphere_time_master_synthesis [LinearOrder R] [IsStrictOrderedRing R] :
    (∀ (s : R) (X : Sphere4D R),
      Sphere4D.radiusSq (Sphere4D.dilate s X) = s ^ 2 * Sphere4D.radiusSq X) ∧
    (∀ (r₀ ep en : R), ep * en = 1 → (r₀ * ep) * (r₀ * en) = r₀ ^ 2) ∧
    (∀ ψ : SlitState2D R, 0 ≤ SlitState2D.bracket ψ (SlitState2D.projSlit1 ψ)) ∧
    (∀ ϕ ψ : SlitState2D R,
      SlitState2D.bracket ϕ (SlitState2D.projSlit1 ψ) +
        SlitState2D.bracket ϕ (SlitState2D.projSlit2 ψ) = SlitState2D.bracket ϕ ψ) ∧
    SlitState2D.normalizedWeakValue1
      SlitState2D.backwardPostSelected SlitState2D.forwardPreSelected < 0 := by
  refine ⟨Sphere4D.radiusSq_dilate, Sphere4D.twin_shell_horizon_lock,
    SlitState2D.standard_qm_slit1_nonneg, SlitState2D.two_state_weak_partition,
    SlitState2D.double_slit_registers_negative_weak_time.2.2.1⟩

end InfoGeometry.QuantumContext.AharonovTime
