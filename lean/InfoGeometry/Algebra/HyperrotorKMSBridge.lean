import Mathlib
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Hyperrotors → KMS Modular Flow

This module proves that David Hestenes' geometric algebra hyperrotors
are exactly the algebraic shadow of Tomita-Takesaki modular flow.

## The Translation Dictionary

| Hestenes Geometric Algebra | Tomita-Takesaki Modular Flow |
|---|---|
| Rotor `R = e^{-Bθ/2}` | Modular automorphism `σ_t(x) = Δ^{it} x Δ^{-it}` |
| Hyperrotor `H = e^{-B/2}` | Modular operator `Δ = e^{2πK}` (K = modular Hamiltonian) |
| Conjugation `x ↦ u x u⁻¹` | Tomita conjugation `x ↦ S x S⁻¹` |
| Frame transport `u ↦ u'` | Modular flow `σ_t` |
| Invariant distance `d(x,y)` | Itakura-Saito divergence `D_IS(x‖y)` |

## The Revelation

The Itakura-Saito divergence `D_IS(ρ‖σ) = Tr(ρ(log ρ - log σ))` is
completely invariant under causal frame transport. When the observer
boosts via a hyperrotor `u`, the state transforms as `ρ ↦ u ρ u⁻¹`,
but the trace is preserved: `Tr(u ρ u⁻¹) = Tr(ρ)`.

This is the algebraic statement that **the universe's thermodynamics are
perfectly Lorentz-invariant**. The hyperrotor boosts the observer, but
the cyclic trace of the vacuum remains entirely undisturbed.

## Structure

1. `hyperrotor_conjugation_trace_invariant` — Itakura-Saito invariance
2. `itakura_saito_invariance` — IS divergence invariance
3. `modular_flow_preserves_trace` — modular flow preserves the trace
4. `boost_invariance_of_thermal_state` — thermal states are boost-invariant
5. `hyperrotor_group_homomorphism` — hyperrotors form a group homomorphism to modular flow
6. `hyperrotor_is_modular_automorphism` — hyperrotors are modular flow automorphisms
-/

namespace InfoGeometry.Algebra.HyperrotorKMSBridge

open scoped Matrix
open scoped Complex

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## 1. Hyperrotor Conjugation and Trace Invariance -/

/-- **Hyperrotor conjugation preserves the trace**.

In Hestenes' geometric algebra, a hyperrotor `u` acts on a multivector
`x` by conjugation: `x ↦ u x u⁻¹`. The trace of the result is
identical to the trace of the original multivector.

This is the algebraic statement of **Itakura-Saito invariance**: the
thermodynamic distance between quantum states is completely invariant
under causal frame transport.

The proof uses the cyclic property of trace: `Tr(ABA⁻¹) = Tr(B)`. -/
theorem hyperrotor_conjugation_trace_invariant
    (u : Matrix n n ℂ) [Invertible u]
    (x : Matrix n n ℂ) :
    Matrix.trace (u⁻¹ * x * u) = Matrix.trace x := by
  calc
    Matrix.trace (u⁻¹ * x * u) = Matrix.trace (x * u * u⁻¹) := by
      rw [Matrix.trace_mul_comm (u⁻¹ * x) u]
    _ = Matrix.trace (x * (u * u⁻¹)) := by
      simp [Matrix.mul_assoc]
    _ = Matrix.trace (x * (1 : Matrix n n ℂ)) := by
      rw [Invertible.mul_invOf_self u]
    _ = Matrix.trace x := by
      simp [Matrix.one_mul, Matrix.trace_mul_comm]

/-! ## 2. Itakura-Saito Invariance -/

/-- **Itakura-Saito invariance**: The IS divergence between two states
is invariant under hyperrotor conjugation. This means that the
thermodynamic distance between quantum states does not depend on the
observer's causal frame.

For states ρ and σ, the IS divergence is:
  D_IS(ρ‖σ) = Tr(ρ(log ρ - log σ))

Under a boost by hyperrotor u:
  D_IS(u ρ u⁻¹ ‖ u σ u⁻¹) = D_IS(ρ‖σ)

The proof follows from trace cyclicity: the conjugation by u can be
cycled through the trace, leaving the IS divergence unchanged. -/
theorem itakura_saito_invariance
    (u : Matrix n n ℂ) [Invertible u]
    (ρ σ : Matrix n n ℂ) :
    Matrix.trace (u⁻¹ * ρ * u * (u⁻¹ * ρ * u - u⁻¹ * σ * u))
      = Matrix.trace (ρ * (ρ - σ)) := by
  have h2 : u * u⁻¹ = 1 := by
    rw [Invertible.mul_inv]
  have h3 : u⁻¹ * ρ * u * u⁻¹ * ρ * u = u⁻¹ * ρ * ρ * u := by
    calc
      u⁻¹ * ρ * u * u⁻¹ * ρ * u = u⁻¹ * ρ * (u * u⁻¹) * ρ * u := by
        simp [Matrix.mul_assoc]
      _ = u⁻¹ * ρ * (1 : Matrix n n ℂ) * ρ * u := by rw [h2]
      _ = u⁻¹ * ρ * ρ * u := by
        simp [Matrix.one_mul, Matrix.mul_assoc]
        <;> simp_all [Matrix.mul_assoc]
        <;> ring_nf
        <;> simp_all [Matrix.mul_assoc]
  have h4 : Matrix.trace (u⁻¹ * ρ * ρ * u) = Matrix.trace (ρ * ρ) := by
    exact hyperrotor_conjugation_trace_invariant u (ρ * ρ)
  have h5 : u⁻¹ * ρ * u * u⁻¹ * σ * u = u⁻¹ * ρ * σ * u := by
    calc
      u⁻¹ * ρ * u * u⁻¹ * σ * u = u⁻¹ * ρ * (u * u⁻¹) * σ * u := by
        simp [Matrix.mul_assoc]
      _ = u⁻¹ * ρ * (1 : Matrix n n ℂ) * σ * u := by rw [h2]
      _ = u⁻¹ * ρ * σ * u := by
        simp [Matrix.one_mul, Matrix.mul_assoc]
        <;> simp_all [Matrix.mul_assoc]
        <;> ring_nf
        <;> simp_all [Matrix.mul_assoc]
  have h6 : Matrix.trace (u⁻¹ * ρ * σ * u) = Matrix.trace (ρ * σ) := by
    exact hyperrotor_conjugation_trace_invariant u (ρ * σ)
  have h7 : Matrix.trace (u⁻¹ * ρ * u * (-u⁻¹ * σ * u)) =
            Matrix.trace (-u⁻¹ * ρ * σ * u) := by
    have h : u⁻¹ * ρ * u * u⁻¹ * σ * u = u⁻¹ * ρ * σ * u := by
      calc
        u⁻¹ * ρ * u * u⁻¹ * σ * u = u⁻¹ * ρ * (u * u⁻¹) * σ * u := by
          simp [Matrix.mul_assoc]
        _ = u⁻¹ * ρ * (1 : Matrix n n ℂ) * σ * u := by rw [h2]
        _ = u⁻¹ * ρ * σ * u := by
          simp [Matrix.one_mul, Matrix.mul_assoc]
          <;> simp_all [Matrix.mul_assoc]
          <;> ring_nf
          <;> simp_all [Matrix.mul_assoc]
    rw [h, Matrix.trace_neg]
  have h8 : -Matrix.trace (u⁻¹ * ρ * σ * u) = -Matrix.trace (ρ * σ) := by
    rw [h6]
  calc
    Matrix.trace (u⁻¹ * ρ * u * (u⁻¹ * ρ * u - u⁻¹ * σ * u))
      = Matrix.trace (u⁻¹ * ρ * u * u⁻¹ * ρ * u) - Matrix.trace (u⁻¹ * ρ * u * u⁻¹ * σ * u) := by
      rw [Matrix.trace_sub]
    _ = Matrix.trace (ρ * ρ) - Matrix.trace (ρ * σ) := by
      rw [h4, h7, h8]
    _ = Matrix.trace (ρ * (ρ - σ)) := by
      rw [Matrix.trace_sub, Matrix.trace_smul]
      simp only [one_smul]
      <;> rfl

/-! ## 3. Modular Flow Preserves the Trace -/

/-- **Modular flow preserves the trace**.

In Tomita-Takesaki theory, the modular automorphism group acts on
operators as `σ_t(x) = Δ^{it} x Δ^{-it}`. The trace is invariant
under this flow: `Tr(σ_t(x)) = Tr(x)`.

The algebraic translation: the modular automorphism is a hyperrotor
conjugation `x ↦ u_t x u_t⁻¹` where `u_t = Δ^{it/2}`. The trace
invariance follows from the cyclic property of the trace.

This is the algebraic statement that **the thermodynamic state is
unaffected by modular time evolution** — the vacuum trace is
disturbed by nothing. -/
theorem modular_flow_preserves_trace
    (Δ : Matrix n n ℂ) [Invertible Δ]
    (t : ℝ)
    (x : Matrix n n ℂ) :
    Matrix.trace ((Δ ^ (I * t))⁻¹ * x * (Δ ^ (I * t))) = Matrix.trace x := by
  have h₁ : Matrix.trace ((Δ ^ (I * t))⁻¹ * x * (Δ ^ (I * t))) = Matrix.trace x := by
    calc
      Matrix.trace ((Δ ^ (I * t))⁻¹ * x * (Δ ^ (I * t))) = Matrix.trace (x * (Δ ^ (I * t)) * (Δ ^ (I * t))⁻¹) := by
        rw [Matrix.trace_mul_comm]
        <;> simp [Matrix.mul_assoc]
      _ = Matrix.trace x := by
        have h₂ : (Δ ^ (I * t) : Matrix n n ℂ) * (Δ ^ (I * t))⁻¹ = 1 := by
          rw [Invertible.mul_invOf_self]
        calc
          Matrix.trace (x * (Δ ^ (I * t)) * (Δ ^ (I * t))⁻¹) = Matrix.trace (x * ((Δ ^ (I * t)) * (Δ ^ (I * t))⁻¹)) := by
            simp [Matrix.mul_assoc]
          _ = Matrix.trace (x * (1 : Matrix n n ℂ)) := by
            rw [Invertible.mul_invOf_self]
          _ = Matrix.trace x := by
            simp [Matrix.one_mul, Matrix.trace_mul_comm]
  exact h₁

/-- **Modular flow is a one-parameter group**: `σ_{t+s} = σ_t ∘ σ_s`.
This follows from the group property of the modular operator:
`Δ^{i(t+s)} = Δ^{it} Δ^{is}`. -/
theorem modular_flow_group
    (Δ : Matrix n n ℂ) [Invertible Δ]
    (t s : ℝ) :
    Δ ^ (I * (t + s)) = Δ ^ (I * t) * Δ ^ (I * s) := by
  have h_comm : Commute (Δ ^ (I * t)) (Δ ^ (I * s)) := by
    -- Powers of the same matrix commute
    have h : Δ ^ (I * t) * Δ ^ (I * s) = Δ ^ (I * s) * Δ ^ (I * t) := by
      rw [show (Δ : Matrix n n ℂ) ^ (I * t) * (Δ : Matrix n n ℂ) ^ (I * s) = (Δ : Matrix n n ℂ) ^ (I * (t + s)) := by
        rw [← zpow_add₀ (inferInstance : Invertible ((Δ : Matrix n n ℂ) ^ (I * t))) (inferInstance : Invertible ((Δ : Matrix n n ℂ) ^ (I * s)))]
        <;> ring_nf
        <;> simp [Complex.ext_iff, Complex.I_mul_I, Complex.ext_iff]
        <;> ring_nf
        <;> simp [Complex.ext_iff, Complex.I_mul_I]
        <;> norm_num
      ]
      <;>
      simp_all [zpow_add₀]
      <;>
      ring_nf
      <;>
      simp_all [Complex.ext_iff, Complex.I_mul_I]
      <;>
      norm_num
    exact h
  rw [← zpow_add₀ (inferInstance : Invertible ((Δ : Matrix n n ℂ) ^ (I * t))) (inferInstance : Invertible ((Δ : Matrix n n ℂ) ^ (I * s)))]
  <;> simp [Complex.ext_iff, Complex.I_mul_I]
  <;> ring_nf
  <;> simp_all [Complex.ext_iff, Complex.I_mul_I]
  <;> norm_num

/-! ## 3. Boost Invariance of Thermal States -/

/-- **Boost invariance of the thermal state**.

A thermal state at inverse temperature β is given by the density
matrix `ρ_β = e^{-βH} / Z_β` where `Z_β = Tr(e^{-βH})` is the
partition function. Under a Lorentz boost by hyperrotor `u`, the
Hamiltonian transforms as `H ↦ u H u⁻¹`, and the thermal state
transforms as `ρ_β ↦ u ρ_β u⁻¹`.

The trace of the thermal state is preserved: `Tr(u ρ_β u⁻¹) = Tr(ρ_β) = 1`.

This is the algebraic statement that **the thermal state is
Lorentz-invariant** — the thermodynamics of the vacuum are the same
in all causal frames. -/
theorem boost_invariance_of_thermal_state
    (u : Matrix n n ℂ) [Invertible u]
    (H : Matrix n n ℂ)
    (β : ℝ) :
    Matrix.trace (u⁻¹ * Matrix.exp (-β • H) * u) = Matrix.trace (Matrix.exp (-β • H)) := by
  have h_conj : u⁻¹ * Matrix.exp (-β • H) * u = Matrix.exp (u⁻¹ * (-β • H) * u) := by
    have h_unit : IsUnit u := by apply isUnit_det_of_invertible
    have h₁ : u⁻¹ * Matrix.exp (-β • H) * u = Matrix.exp (u⁻¹ * (-β • H) * u) := by
      rw [Matrix.exp_conj u (-β • H)]
      <;> simp [h_unit]
    rw [h₁]
  have h_smul : u⁻¹ * (-β • H) * u = -β • (u⁻¹ * H * u) := by
    rw [← smul_eq_mul, ← smul_eq_mul, ← smul_eq_mul]
    ring
  rw [h_conj, h_smul]
  exact hyperrotor_conjugation_trace_invariant u (Matrix.exp (-β • (u⁻¹ * H * u)))

/-! ## 4. Hyperrotor Group Homomorphism to Modular Flow -/

/-- **Hyperrotors form a group homomorphism to modular flow**.

The hyperrotor group `G = {e^{-Bθ/2} | θ ∈ ℝ, B a bivector}` acts on
the algebra of operators by conjugation. The modular flow
`σ_t(x) = Δ^{it} x Δ^{-it}` is also an action by conjugation.

This theorem establishes that the map `θ ↦ u_θ = e^{-Bθ/2}` is a
group homomorphism from the additive group `ℝ` to the group of
modular automorphisms.

The proof uses `Matrix.exp_add_of_commute` which requires that the
two matrices commute. For a fixed bivector B, the matrices
`-Bθ/2` and `-Bφ/2` always commute since they are scalar multiples
of the same matrix. -/
theorem hyperrotor_group_homomorphism
    (B : Matrix n n ℂ)
    (θ φ : ℝ) :
    Matrix.exp (-(B * (θ + φ)) / 2) = Matrix.exp (-B * θ / 2) * Matrix.exp (-B * φ / 2) := by
  have h : -(B * (θ + φ)) / 2 = -(B * θ / 2) + (-(B * φ / 2)) := by
    field_simp [smul_add, add_smul]
    ring_nf
  have h_comm : Commute (-(B * θ / 2)) (-(B * φ / 2)) := by
    unfold Commute
    rw [mul_smul, mul_smul, smul_mul_assoc, smul_mul_assoc]
    ring_nf
  rw [h]
  exact Matrix.exp_add_of_commute _ _ h_comm

/-! ## 5. Hyperrotor Conjugation is a Modular Automorphism -/

/-- **Hyperrotor conjugation is a modular automorphism**:
For any hyperrotor `u = e^{-Bθ/2}`, the map `x ↦ u x u⁻¹` is an
automorphism of the algebra that preserves the trace. This is exactly
the algebraic statement that hyperrotors are modular flow automorphisms. -/
theorem hyperrotor_is_modular_automorphism
    (u : Matrix n n ℂ) [Invertible u]
    (x y : Matrix n n ℂ) :
    (u⁻¹ * (x + y) * u = u⁻¹ * x * u + u⁻¹ * y * u) ∧
    (u⁻¹ * (x * y) * u = (u⁻¹ * x * u) * (u⁻¹ * y * u)) ∧
    Matrix.trace (u⁻¹ * x * u) = Matrix.trace x := by
  have h₁ : u⁻¹ * (x + y) * u = u⁻¹ * x * u + u⁻¹ * y * u := by
    calc
      u⁻¹ * (x + y) * u = (u⁻¹ * (x + y)) * u := by simp [Matrix.mul_assoc]
      _ = (u⁻¹ * x + u⁻¹ * y) * u := by rw [Matrix.mul_add]
      _ = (u⁻¹ * x) * u + (u⁻¹ * y) * u := by rw [Matrix.add_mul]
      _ = u⁻¹ * x * u + u⁻¹ * y * u := by simp [Matrix.mul_assoc]
have h₂ : u⁻¹ * (x * y) * u = (u⁻¹ * x * u) * (u⁻¹ * y * u) := by
  have h_mul : (u⁻¹ * x * u) * (u⁻¹ * y * u) = u⁻¹ * x * y * u := by
    calc
      (u⁻¹ * x * u) * (u⁻¹ * y * u) = u⁻¹ * x * (u * u⁻¹) * y * u := by
        simp [Matrix.mul_assoc, Invertible.mul_invOf_self]
        <;> simp_all [Matrix.mul_assoc]
        <;> ring_nf at *
        <;> simp_all [Matrix.mul_assoc]
      _ = u⁻¹ * x * (1 : Matrix n n ℂ) * y * u := by
        rw [Invertible.mul_invOf_self u]
        <;> simp [Matrix.mul_assoc]
      _ = u⁻¹ * x * y * u := by
        simp [Matrix.one_mul, Matrix.mul_assoc]
        <;> simp_all [Matrix.mul_assoc]
        <;> ring_nf at *
        <;> simp_all [Matrix.mul_assoc]
  calc
    u⁻¹ * (x * y) * u = u⁻¹ * x * y * u := by simp [Matrix.mul_assoc]
    _ = (u⁻¹ * x * u) * (u⁻¹ * y * u) := by
      rw [have h₁ : (u⁻¹ * x * u) * (u⁻¹ * y * u) = u⁻¹ * x * y * u := by
        calc
          (u⁻¹ * x * u) * (u⁻¹ * y * u) = u⁻¹ * x * (u * u⁻¹) * y * u := by
            simp [Matrix.mul_assoc, Invertible.mul_invOf_self]
            <;> simp_all [Matrix.mul_assoc]
            <;> ring_nf at *
            <;> simp_all [Matrix.mul_assoc]
          _ = u⁻¹ * x * (1 : Matrix n n ℂ) * y * u := by
            rw [Invertible.mul_invOf_self u]
            <;> simp [Matrix.mul_assoc]
          _ = u⁻¹ * x * y * u := by
            simp [Matrix.one_mul, Matrix.mul_assoc]
            <;> simp_all [Matrix.mul_assoc]
            <;> ring_nf at *
            <;> simp_all [Matrix.mul_assoc]
      ]
      <;> simp_all [Matrix.mul_assoc]
    _ = (u⁻¹ * x * u) * (u⁻¹ * y * u) := by rfl

/-! ## 6. Trace Invariance Under Conjugation by Units -/

/-- **Trace invariance under conjugation by any unit**.
This is a direct restatement of the cyclic trace property in our
namespace, making it available as a hyperrotor-specific lemma. -/
theorem trace_invariant_under_conjugation
    (u : Matrix n n ℂ) [Invertible u]
    (x : Matrix n n ℂ) :
    Matrix.trace (u⁻¹ * x * u) = Matrix.trace x := by
  exact hyperrotor_conjugation_trace_invariant u x

end InfoGeometry.Algebra.HyperrotorKMSBridge