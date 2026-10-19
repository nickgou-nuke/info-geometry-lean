/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.External.Auto.SarsModularWeakValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Section 116: $S^3$ Radial Dilatation Time and a Finite Two-Slit Weak-Value Model

This module formalizes:
1. **Concentric $S^3$ Shells in $\mathbb{R}^4$ (`Sphere4D R`)**: Squared radius
   $\|X\|^2 = w^2 + x^2 + y^2 + z^2$, Weyl radial dilatation scaling $\|s \cdot X\|^2 = s^2 \|X\|^2$,
   and the forward-backward thermofield twin shell horizon invariant
   $(r_0 e^\tau)(r_0 e^{-\tau}) = r_0^2$.
2. **Aharonov–Bergmann–Lebowitz Two-State Vector Formalism (`SlitState2D R`)**: Two-slit
   interference space equipped with slit projectors $\hat{P}_1, \hat{P}_2$, single-vector Born
   positivity ($0 \le \langle \psi | \hat{P}_1 | \psi \rangle$), and the two-state transition-amplitude partition
   of unity $\langle \phi | \hat{P}_1 \psi \rangle + \langle \phi | \hat{P}_2 \psi \rangle = \langle \phi | \psi \rangle$.
3. **Finite two-slit weak values**: a field-valued option quotient is defined when the
   bilinear post/pre overlap is nonzero. The selected rational pair has weak values $-1$ and $2$.
   Their rational subcarrier is explicitly compared with the existing finite complex weak-value
   owner; no physical dwell-time or measurement-process theorem is claimed.
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

/-- Specialization to the actual real exponential pair `exp(τ), exp(-τ)`. -/
theorem twin_shell_horizon_lock_real_exp (r₀ τ : ℝ) :
    (r₀ * Real.exp τ) * (r₀ * Real.exp (-τ)) = r₀ ^ 2 := by
  calc
    _ = r₀ ^ 2 * (Real.exp τ * Real.exp (-τ)) := by ring
    _ = r₀ ^ 2 * Real.exp (τ + -τ) := by rw [← Real.exp_add]
    _ = r₀ ^ 2 := by simp

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

/-- **Aharonov Two-State Transition-Amplitude Partition**:
    For any pre-selected state $|\psi\rangle$ and post-selected state $\langle \phi|$, the sum
    of the two-state transition amplitudes across Slit 1 and Slit 2 equals the total overlap
    $\langle \phi | \psi \rangle$. -/
theorem two_state_transition_amplitude_partition (ϕ ψ : SlitState2D R) :
    bracket ϕ (projSlit1 ψ) + bracket ϕ (projSlit2 ψ) = bracket ϕ ψ := by
  dsimp [bracket, projSlit1, projSlit2]
  ring

/-! ## Section 3: Negative Transition Amplitudes and Guarded Weak Values -/

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

/-- Transition numerator through slit 1. -/
def transitionAmplitude1 (ϕ ψ : SlitState2D R) : R :=
  bracket ϕ (projSlit1 ψ)

/-- Transition numerator through slit 2. -/
def transitionAmplitude2 (ϕ ψ : SlitState2D R) : R :=
  bracket ϕ (projSlit2 ψ)

/-- **Selected two-slit transition-numerator example**:
    For pre-selected $\psi = (1, 1)$ and post-selected $\phi = (1, -2)$:
    1. The two-state overlap is $\langle \phi | \psi \rangle = -1$.
    2. The unnormalized transition numerators are `1` and `-2`.
    Their sum is the overlap, by the general partition theorem. -/
theorem double_slit_transition_numerators :
    bracket backwardPostSelected forwardPreSelected = -1 ∧
    transitionAmplitude1 backwardPostSelected forwardPreSelected = 1 ∧
    transitionAmplitude2 backwardPostSelected forwardPreSelected = -2 ∧
    transitionAmplitude1 backwardPostSelected forwardPreSelected +
      transitionAmplitude2 backwardPostSelected forwardPreSelected = -1 := by
  dsimp [forwardPreSelected, backwardPostSelected, bracket,
    transitionAmplitude1, transitionAmplitude2, projSlit1, projSlit2]
  refine ⟨by decide, by decide, by decide, by decide⟩

end SlitState2D

/-! ### Field-valued weak values for the finite bilinear carrier

The `bracket` above is bilinear and has no conjugation. The option quotient
makes the normalization domain explicit by returning `none` when the overlap
vanishes. The rational subcarrier is explicitly embedded into the repository's
finite complex weak-value owner below; no physical dwell-time interpretation is
claimed.
-/

namespace SlitWeakValue

variable {R : Type*} [Field R]

/-- The two coordinate projectors are the only observables admitted by this
    finite weak-value API. -/
inductive SlitProjector
  | slit1
  | slit2
  deriving DecidableEq, Repr

/-- Action of one of the two slit projectors. -/
def SlitProjector.act (P : SlitProjector) (ψ : SlitState2D R) : SlitState2D R :=
  match P with
  | .slit1 => SlitState2D.projSlit1 ψ
  | .slit2 => SlitState2D.projSlit2 ψ

/-- Weak value of an observable action on a two-slit state. Zero overlap is
    represented by `none`; division is used only on the nonzero branch. The
    observable is restricted to the two coordinate slit projectors. -/
noncomputable def weakValue? (ϕ ψ : SlitState2D R)
    (P : SlitProjector) : Option R :=
  by
    classical
    exact if h : SlitState2D.bracket ϕ ψ = 0 then none
      else some (SlitState2D.bracket ϕ (P.act ψ) / SlitState2D.bracket ϕ ψ)

/-- On a regular pair, the option-valued weak value is the transition
    numerator divided by the overlap. -/
theorem weakValue?_eq_quotient_of_overlap_ne_zero
    (ϕ ψ : SlitState2D R) (P : SlitProjector)
    (h : SlitState2D.bracket ϕ ψ ≠ 0) :
    weakValue? ϕ ψ P =
      some (SlitState2D.bracket ϕ (P.act ψ) / SlitState2D.bracket ϕ ψ) := by
  simp [weakValue?, h]

/-- A vanishing post/pre overlap makes the weak value undefined. -/
theorem weakValue?_eq_none_of_overlap_eq_zero
    (ϕ ψ : SlitState2D R) (P : SlitProjector)
    (h : SlitState2D.bracket ϕ ψ = 0) :
    weakValue? ϕ ψ P = none := by
  simp [weakValue?, h]

/-- The two projector weak values sum to one whenever both are defined. -/
theorem slit_projector_weak_values_partition
    (ϕ ψ : SlitState2D R) (h : SlitState2D.bracket ϕ ψ ≠ 0) :
    ∃ w₁ w₂ : R,
      weakValue? ϕ ψ .slit1 = some w₁ ∧
      weakValue? ϕ ψ .slit2 = some w₂ ∧
      w₁ + w₂ = 1 := by
  refine ⟨SlitState2D.bracket ϕ (SlitState2D.projSlit1 ψ) /
      SlitState2D.bracket ϕ ψ,
    SlitState2D.bracket ϕ (SlitState2D.projSlit2 ψ) /
      SlitState2D.bracket ϕ ψ, ?_, ?_, ?_⟩
  · simpa [SlitProjector.act] using
      weakValue?_eq_quotient_of_overlap_ne_zero ϕ ψ .slit1 h
  · simpa [SlitProjector.act] using
      weakValue?_eq_quotient_of_overlap_ne_zero ϕ ψ .slit2 h
  · rw [← add_div, SlitState2D.two_state_transition_amplitude_partition, div_self h]

/-- Rational specialization of the selected pre-state. -/
def rationalForwardPreSelected : SlitState2D ℚ := ⟨1, 1⟩

/-- Rational specialization of the selected post-state. -/
def rationalBackwardPostSelected : SlitState2D ℚ := ⟨1, -2⟩

theorem rational_selected_overlap :
    SlitState2D.bracket rationalBackwardPostSelected rationalForwardPreSelected = -1 := by
  norm_num [rationalBackwardPostSelected, rationalForwardPreSelected,
    SlitState2D.bracket]

theorem rational_selected_projector_weak_values :
    weakValue? rationalBackwardPostSelected rationalForwardPreSelected
        .slit1 = some (-1) ∧
    weakValue? rationalBackwardPostSelected rationalForwardPreSelected
        .slit2 = some 2 := by
  have h : SlitState2D.bracket rationalBackwardPostSelected
      rationalForwardPreSelected ≠ 0 := by
    rw [rational_selected_overlap]
    norm_num
  constructor
  · rw [weakValue?_eq_quotient_of_overlap_ne_zero _ _ .slit1 h]
    norm_num [rationalBackwardPostSelected, rationalForwardPreSelected,
      SlitState2D.bracket, SlitProjector.act, SlitState2D.projSlit1]
  · rw [weakValue?_eq_quotient_of_overlap_ne_zero _ _ .slit2 h]
    norm_num [rationalBackwardPostSelected, rationalForwardPreSelected,
      SlitState2D.bracket, SlitProjector.act, SlitState2D.projSlit2]

theorem orthogonal_pair_weak_value_is_none :
    weakValue? (⟨1, 0⟩ : SlitState2D ℚ) (⟨0, 1⟩ : SlitState2D ℚ)
      .slit1 = none := by
  apply weakValue?_eq_none_of_overlap_eq_zero
  norm_num [SlitState2D.bracket]

/-- A rational two-slit vector viewed as a complex two-level state. -/
def rationalStateToComplex (ψ : SlitState2D ℚ) :
    SarsModularWeakValue.State2 :=
  fun i => if i = 0 then (ψ.s₁ : ℂ) else (ψ.s₂ : ℂ)

/-- The two coordinate projectors as actual complex `2 × 2` matrices. -/
def complexSlitProjector : SlitProjector → SarsModularWeakValue.M2C
  | .slit1 => fun i j => if i = 0 then (if j = 0 then 1 else 0) else 0
  | .slit2 => fun i j => if i = 1 then (if j = 1 then 1 else 0) else 0

/-- On real rational coordinates, the repository's complex inner product is
the cast of the finite bilinear pairing. -/
theorem complexPairing_eq_cast (ϕ ψ : SlitState2D ℚ) :
    SarsModularWeakValue.cinner (rationalStateToComplex ϕ)
      (rationalStateToComplex ψ) =
      ((SlitState2D.bracket ϕ ψ : ℚ) : ℂ) := by
  simp [SarsModularWeakValue.cinner, rationalStateToComplex,
    SlitState2D.bracket]

/-- The complex coordinate-matrix projector action agrees with the rational
coordinate projector after embedding states. -/
theorem complexProjector_action (P : SlitProjector) (ψ : SlitState2D ℚ) :
    SarsModularWeakValue.matVec (complexSlitProjector P)
      (rationalStateToComplex ψ) =
      rationalStateToComplex (P.act ψ) := by
  cases P <;> funext i <;> fin_cases i <;>
    simp [complexSlitProjector, SarsModularWeakValue.matVec,
      rationalStateToComplex, SlitProjector.act,
      SlitState2D.projSlit1, SlitState2D.projSlit2]

/-- The complex weak-value numerator is the complex cast of the rational
transition amplitude. -/
theorem complexWeakNumerator_eq_cast
    (ϕ ψ : SlitState2D ℚ) (P : SlitProjector) :
    SarsModularWeakValue.weakNumerator (complexSlitProjector P)
      (rationalStateToComplex ψ) (rationalStateToComplex ϕ) =
      ((SlitState2D.bracket ϕ (P.act ψ) : ℚ) : ℂ) := by
  simpa [SarsModularWeakValue.weakNumerator, complexProjector_action] using
    complexPairing_eq_cast ϕ (P.act ψ)

/-- The complex weak-value denominator is the complex cast of the rational
overlap. -/
theorem complexWeakDenominator_eq_cast (ϕ ψ : SlitState2D ℚ) :
    SarsModularWeakValue.weakDenominator
      (rationalStateToComplex ψ) (rationalStateToComplex ϕ) =
      ((SlitState2D.bracket ϕ ψ : ℚ) : ℂ) := by
  simpa [SarsModularWeakValue.weakDenominator] using complexPairing_eq_cast ϕ ψ

/-- The guarded rational weak-value function agrees, after the canonical cast
`ℚ → ℂ`, with the existing sesquilinear complex weak-value owner. -/
theorem rational_weakValue_complex_compatibility
    (ϕ ψ : SlitState2D ℚ) (P : SlitProjector) :
    Option.map (fun q : ℚ => (q : ℂ)) (weakValue? ϕ ψ P) =
      SarsModularWeakValue.weakValue? (complexSlitProjector P)
        (rationalStateToComplex ψ) (rationalStateToComplex ϕ) := by
  by_cases h : SlitState2D.bracket ϕ ψ = 0
  · have hc : SarsModularWeakValue.weakDenominator
        (rationalStateToComplex ψ) (rationalStateToComplex ϕ) = 0 := by
      rw [complexWeakDenominator_eq_cast]
      simp [h]
    simp [weakValue?, SarsModularWeakValue.weakValue?, h, hc]
  · have hc : SarsModularWeakValue.weakDenominator
        (rationalStateToComplex ψ) (rationalStateToComplex ϕ) ≠ 0 := by
      rw [complexWeakDenominator_eq_cast]
      exact_mod_cast h
    rw [weakValue?_eq_quotient_of_overlap_ne_zero ϕ ψ P h]
    rw [SarsModularWeakValue.weak_value_some_of_nonorthogonal
      (complexSlitProjector P) (rationalStateToComplex ψ)
      (rationalStateToComplex ϕ) hc]
    simp only [Option.map_some]
    congr 1
    simp [complexWeakNumerator_eq_cast, complexWeakDenominator_eq_cast]

end SlitWeakValue

end InfoGeometry.QuantumContext.AharonovTime
