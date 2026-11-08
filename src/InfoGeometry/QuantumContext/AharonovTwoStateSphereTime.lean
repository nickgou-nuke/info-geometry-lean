/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

namespace InfoGeometry.QuantumContext.AharonovTime

variable {R : Type*} [CommRing R]

/-! ### 1. 4D Euclidean Carrier and Concentric S³ Shells (Trap T16 Cleared) -/

@[ext]
structure Sphere4D (R : Type*) where
  w : R
  x : R
  y : R
  z : R

namespace Sphere4D

variable {R : Type*} [CommRing R]

/-- Squared radius of the S³ shell in ℝ⁴: r² = w² + x² + y² + z². -/
def radiusSq (X : Sphere4D R) : R :=
  X.w^2 + X.x^2 + X.y^2 + X.z^2

/-- Radial Weyl dilatation of the S³ shell by scale factor s = exp(τ). -/
def dilate (s : R) (X : Sphere4D R) : Sphere4D R :=
  ⟨s * X.w, s * X.x, s * X.y, s * X.z⟩

/-- 
Radial Dilatation Scaling Law:
Dilating the 4D coordinates by s = exp(τ) scales the S³ shell squared radius by s² = exp(2τ).
Time evolution is the radial dilatation of the S³ sphere!
-/
theorem radiusSq_dilate (s : R) (X : Sphere4D R) :
    radiusSq (dilate s X) = s^2 * radiusSq X := by
  dsimp [radiusSq, dilate]
  ring

/-- 
First-Order Spatial Deviation Law:
For a shell perturbation r = r₀ + δr, the squared radius expands around the reference shell r₀²
with linear radial deviation 2 r₀ δr (the infinitesimal logarithmic time step dτ = δr / r₀).
-/
theorem shell_deviation_expansion (r₀ δr : R) :
    (r₀ + δr)^2 - r₀^2 = 2 * r₀ * δr + δr^2 := by
  ring

/-- 
Forward-Backward Twin Shell Invariance:
If the forward wave expands as r_fwd = r₀ · exp_pos and the backward twin wave 
contracts as r_bwd = r₀ · exp_neg with exp_pos · exp_neg = 1, their geometric 
mean is strictly locked to the static reference horizon r₀²!
-/
theorem twin_shell_horizon_lock (r₀ exp_pos exp_neg : R)
    (h_inv : exp_pos * exp_neg = 1) :
    (r₀ * exp_pos) * (r₀ * exp_neg) = r₀^2 := by
  calc (r₀ * exp_pos) * (r₀ * exp_neg)
    _ = r₀^2 * (exp_pos * exp_neg) := by ring
    _ = r₀^2 * 1 := by rw [h_inv]
    _ = r₀^2 := by ring

end Sphere4D

/-! ### 2. Double-Slit Two-State Vector Formalism (Aharonov–Bergmann–Lebowitz) -/

/-- A 2-component state vector in the Double-Slit interference space (Slit 1 ⊕ Slit 2). -/
@[ext]
structure SlitState2D (R : Type*) where
  s₁ : R  -- Amplitude at Slit 1
  s₂ : R  -- Amplitude at Slit 2

namespace SlitState2D

variable {R : Type*} [CommRing R]

/-- Bilinear pairing between backward post-selected state ⟨ϕ| and forward pre-selected state |ψ⟩. -/
def bracket (ϕ ψ : SlitState2D R) : R :=
  ϕ.s₁ * ψ.s₁ + ϕ.s₂ * ψ.s₂

/-- Slit 1 Projection Operator P̂₁: projects onto the first slit (s₁, 0). -/
def projSlit1 (ψ : SlitState2D R) : SlitState2D R :=
  ⟨ψ.s₁, 0⟩

/-- Slit 2 Projection Operator P̂₂: projects onto the second slit (0, s₂). -/
def projSlit2 (ψ : SlitState2D R) : SlitState2D R :=
  ⟨0, ψ.s₂⟩

/-- P̂₁ is an idempotent projector: P̂₁(P̂₁(ψ)) = P̂₁(ψ). -/
@[simp]
theorem projSlit1_idempotent (ψ : SlitState2D R) :
    projSlit1 (projSlit1 ψ) = projSlit1 ψ := by
  dsimp [projSlit1]

/-- P̂₂ is an idempotent projector: P̂₂(P̂₂(ψ)) = P̂₂(ψ). -/
@[simp]
theorem projSlit2_idempotent (ψ : SlitState2D R) :
    projSlit2 (projSlit2 ψ) = projSlit2 ψ := by
  dsimp [projSlit2]

/-- 
Standard Single-Vector Positivity Theorem:
In conventional 1-vector quantum mechanics (where ϕ = ψ), the expectation value 
of the Slit 1 projector ⟨ψ | P̂₁ | ψ⟩ = ψ₁² is ALWAYS non-negative!
Standard single-vector QM can never register negative dwell time.
-/
theorem standard_qm_slit1_nonneg [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (ψ : SlitState2D R) :
    0 ≤ bracket ψ (projSlit1 ψ) := by
  dsimp [bracket, projSlit1]
  have h_eq : ψ.s₁ * ψ.s₁ + ψ.s₂ * 0 = ψ.s₁^2 := by ring
  rw [h_eq]
  exact sq_nonneg ψ.s₁

/-- 
Two-State Weak Partition of Unity:
For ANY forward state |ψ⟩ and backward state ⟨ϕ|, the sum of the two-state 
amplitudes across Slit 1 and Slit 2 equals the total overlap ⟨ϕ | ψ⟩:
⟨ϕ | P̂₁ | ψ⟩ + ⟨ϕ | P̂₂ | ψ⟩ = ⟨ϕ | ψ⟩.
-/
theorem two_state_weak_partition (ϕ ψ : SlitState2D R) :
    bracket ϕ (projSlit1 ψ) + bracket ϕ (projSlit2 ψ) = bracket ϕ ψ := by
  dsimp [bracket, projSlit1, projSlit2]
  ring

/-! ### 3. The Negative Weak Dwell-Time Theorem (Destructive Interference Witness) -/

/-- Pre-selected Forward Wave |ψ_fwd⟩ = (1, 1) (Symmetric illumination of both slits). -/
def forwardPreSelected : SlitState2D ℤ := ⟨1, 1⟩

/-- Post-selected Backward Wave ⟨ϕ_bwd| = (1, -2) (Detector placed near dark fringe). -/
def backwardPostSelected : SlitState2D ℤ := ⟨1, -2⟩

/-- 
The Weak Value of an operator P̂ is defined by the ratio:
  W(P̂) = ⟨ϕ | P̂ | ψ⟩ / ⟨ϕ | ψ⟩.
We normalize the overlap to ⟨ϕ | ψ⟩ = -1, so the normalized weak value is:
  weakVal(P̂) = - ⟨ϕ | P̂ | ψ⟩.
-/
def normalizedWeakValue1 (ϕ ψ : SlitState2D R) : R :=
  - bracket ϕ (projSlit1 ψ)

def normalizedWeakValue2 (ϕ ψ : SlitState2D R) : R :=
  - bracket ϕ (projSlit2 ψ)

/-- 
The Master Negative Dwell-Time Theorem:
For the pre-selected forward state (1, 1) and post-selected backward state (1, -2):
1. The total two-state overlap is non-zero: ⟨ϕ | ψ⟩ = -1.
2. The normalized Weak Value (dwell time) in Slit 1 is STRICTLY NEGATIVE: W(P̂₁) = -1 < 0!
3. The normalized Weak Value in Slit 2 is anomalous (> 1): W(P̂₂) = +2!
4. Total probability / dwell time is strictly conserved: W(P̂₁) + W(P̂₂) = -1 + 2 = 1!
-/
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

/-! ### 4. Master Certificate of Section 116 -/

structure AharonovSphereTimeCertificate (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] : Prop where
  shell_dilatation : ∀ (s : R) (X : Sphere4D R),
    Sphere4D.radiusSq (Sphere4D.dilate s X) = s^2 * Sphere4D.radiusSq X
  twin_horizon_lock : ∀ (r₀ ep en : R) (h : ep * en = 1),
    (r₀ * ep) * (r₀ * en) = r₀^2
  standard_positivity : ∀ (ψ : SlitState2D R),
    0 ≤ SlitState2D.bracket ψ (SlitState2D.projSlit1 ψ)
  weak_partition : ∀ (ϕ ψ : SlitState2D R),
    SlitState2D.bracket ϕ (SlitState2D.projSlit1 ψ) +
    SlitState2D.bracket ϕ (SlitState2D.projSlit2 ψ) = SlitState2D.bracket ϕ ψ
  negative_weak_time_witness :
    SlitState2D.normalizedWeakValue1 SlitState2D.backwardPostSelected SlitState2D.forwardPreSelected < 0

theorem compile_aharonov_sphere_time_certificate [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] :
    AharonovSphereTimeCertificate R where
  shell_dilatation := Sphere4D.radiusSq_dilate
  twin_horizon_lock := Sphere4D.twin_shell_horizon_lock
  standard_positivity := SlitState2D.standard_qm_slit1_nonneg
  weak_partition := SlitState2D.two_state_weak_partition
  negative_weak_time_witness := SlitState2D.double_slit_registers_negative_weak_time.2.2.1

end InfoGeometry.QuantumContext.AharonovTime