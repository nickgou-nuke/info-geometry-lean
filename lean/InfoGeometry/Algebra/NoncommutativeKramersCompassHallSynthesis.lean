/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Noncommutative Kramers Time-Reversal, Compass Plaquette Algebra & Hall Selection Rule

Pure noncommutative matrix/operator-algebraic formalization over an arbitrary
associative ring `[Ring B]` (and `[StarRing B]` where adjoints appear), without
commutativity, centrality, or scalar-diagonal assumptions.

Reuses `mat2`, `ext_fin2`, `gamma1Op`, `sigmaOp`, `omegaOp`, `fiberEmbed`, and
`vecOp` from `NoncommutativeCliffordPrimitives` and
`NoncommutativeCovariantDiracZornSynthesis`.

## Causal Poset of Archetypes
* `KC₁` — Symplectic Time-Reversal Involution `sympTimeRev` on `M₂(B)` via `omegaOp`
  (`omegaOp² = -1`), anti-multiplicativity, and `vecOp` / `fiberEmbed` parity.
* `KC₂` — Kramers–Zeeman Parity Dichotomy: `Θ`-even self-adjoint operators commute
  with `omegaOp`; `Θ`-odd self-adjoint operators anticommute with `omegaOp`;
  commutator parity law.
* `KC₃` — Noncommutative Compass Bond Algebra & Hexagonal Plaquette Gauge Conjugation,
  plus the `M₂(B)` Clifford/compass realization via `(gamma1Op, sigmaOp, omegaOp)`.
* `KC₄` — Antisymmetric Hall Commutator `⁅Jₓ, Jᵧ⁆` & Time-Reversal Selection Rule:
  star-skewness for self-adjoint currents and `2 • ω ⁅Jₓ, Jᵧ⁆ = 0` for any
  `Θ`-invariant additive functional `ω` when `Jₓ, Jᵧ` are `Θ`-odd.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.NoncommutativeCovariantDiracZornSynthesis

namespace InfoGeometry.Algebra.NoncommutativeKramersCompassHallSynthesis

/-! ## KC₁: Symplectic Time-Reversal Involution on `M₂(B)` -/

section ArchetypeKC1_SymplecticTimeReversal

variable {B : Type*} [Ring B]

lemma omegaOp_sq :
    (omegaOp : Matrix (Fin 2) (Fin 2) B) * omegaOp = -1 := by
  apply ext_fin2 <;> simp [omegaOp]

lemma gamma1Op_sq :
    (gamma1Op : Matrix (Fin 2) (Fin 2) B) * gamma1Op = 1 := by
  apply ext_fin2 <;> simp [gamma1Op]

lemma sigmaOp_sq :
    (sigmaOp : Matrix (Fin 2) (Fin 2) B) * sigmaOp = 1 := by
  apply ext_fin2 <;> simp [sigmaOp]

lemma gamma1_sigma_anticomm :
    (gamma1Op : Matrix (Fin 2) (Fin 2) B) * sigmaOp +
      sigmaOp * gamma1Op = 0 := by
  apply ext_fin2 <;> simp [gamma1Op, sigmaOp]

lemma gamma1_omega_anticomm :
    (gamma1Op : Matrix (Fin 2) (Fin 2) B) * omegaOp +
      omegaOp * gamma1Op = 0 := by
  apply ext_fin2 <;> simp [gamma1Op, omegaOp]

lemma sigma_omega_anticomm :
    (sigmaOp : Matrix (Fin 2) (Fin 2) B) * omegaOp +
      omegaOp * sigmaOp = 0 := by
  apply ext_fin2 <;> simp [sigmaOp, omegaOp]

variable [StarRing B]

lemma omegaOp_ct :
    (omegaOp : Matrix (Fin 2) (Fin 2) B)ᴴ = -omegaOp := by
  apply ext_fin2 <;> simp [omegaOp]

/-- Symplectic time-reversal operator `Θ(X) = -Ω Xᴴ Ω` on `M₂(B)`. -/
def sympTimeRev (X : Matrix (Fin 2) (Fin 2) B) : Matrix (Fin 2) (Fin 2) B :=
  -omegaOp * Xᴴ * omegaOp

lemma sympTimeRev_add (X Y : Matrix (Fin 2) (Fin 2) B) :
    sympTimeRev (X + Y) = sympTimeRev X + sympTimeRev Y := by
  simp only [sympTimeRev, conjTranspose_add, mul_add, add_mul]

lemma sympTimeRev_neg (X : Matrix (Fin 2) (Fin 2) B) :
    sympTimeRev (-X) = -sympTimeRev X := by
  simp only [sympTimeRev, conjTranspose_neg, mul_neg, neg_mul]

lemma sympTimeRev_sub (X Y : Matrix (Fin 2) (Fin 2) B) :
    sympTimeRev (X - Y) = sympTimeRev X - sympTimeRev Y := by
  simp only [sub_eq_add_neg, sympTimeRev_add, sympTimeRev_neg]

/-- `sympTimeRev` is an anti-homomorphism of `M₂(B)`: `Θ(XY) = Θ(Y) Θ(X)`. -/
theorem sympTimeRev_mul (X Y : Matrix (Fin 2) (Fin 2) B) :
    sympTimeRev (X * Y) = sympTimeRev Y * sympTimeRev X := by
  dsimp [sympTimeRev]
  rw [conjTranspose_mul]
  calc
    -omegaOp * (Yᴴ * Xᴴ) * omegaOp
      = -omegaOp * Yᴴ * (-(omegaOp * omegaOp)) * Xᴴ * omegaOp := by
        rw [omegaOp_sq, neg_neg, mul_one]
        noncomm_ring
    _ = (-omegaOp * Yᴴ * omegaOp) * (-omegaOp * Xᴴ * omegaOp) := by
        noncomm_ring

/-- `sympTimeRev` is an involution on `M₂(B)`: `Θ(Θ(X)) = X`. -/
theorem sympTimeRev_involutive (X : Matrix (Fin 2) (Fin 2) B) :
    sympTimeRev (sympTimeRev X) = X := by
  dsimp [sympTimeRev]
  simp only [conjTranspose_mul, conjTranspose_neg, conjTranspose_conjTranspose,
    omegaOp_ct, neg_neg]
  calc
    -omegaOp * (-omegaOp * (X * omegaOp)) * omegaOp
      = (omegaOp * omegaOp) * X * (omegaOp * omegaOp) := by noncomm_ring
    _ = (-1 : Matrix (Fin 2) (Fin 2) B) * X * (-1) := by rw [omegaOp_sq]
    _ = X := by noncomm_ring

/-- Scalar diagonal embeddings `fiberEmbed s` transform by `s ↦ star s` under `sympTimeRev`. -/
theorem sympTimeRev_fiberEmbed (s : B) :
    sympTimeRev (fiberEmbed s) = fiberEmbed (star s) := by
  apply ext_fin2 <;> simp [sympTimeRev, fiberEmbed, omegaOp]

/-- Trace-free Zorn 3-vectors `vecOp v₁ v₂ v₃` pick up a minus sign under `sympTimeRev`. -/
theorem sympTimeRev_vecOp (v₁ v₂ v₃ : B) :
    sympTimeRev (vecOp v₁ v₂ v₃) = -(vecOp (star v₁) (star v₂) (star v₃)) := by
  apply ext_fin2 <;>
    simp [sympTimeRev, vecOp, fiberEmbed, gamma1Op, sigmaOp, omegaOp]

end ArchetypeKC1_SymplecticTimeReversal

/-! ## KC₂: Kramers–Zeeman Parity Dichotomy & Commutator Parity Law -/

section ArchetypeKC2_KramersZeemanDichotomy

variable {B : Type*} [Ring B] [StarRing B]

/-- Any `Θ`-even self-adjoint operator (`sympTimeRev H = H` and `Hᴴ = H`) commutes with `omegaOp`. -/
theorem kramers_even_selfAdjoint_commutes_omega
    {H : Matrix (Fin 2) (Fin 2) B}
    (h_even : sympTimeRev H = H) (h_sa : Hᴴ = H) :
    H * omegaOp = omegaOp * H := by
  have h1 : -omegaOp * H * omegaOp = H := by
    simpa [sympTimeRev, h_sa] using h_even
  calc
    H * omegaOp = (-omegaOp * H * omegaOp) * omegaOp := by rw [h1]
    _ = -omegaOp * H * (omegaOp * omegaOp) := by noncomm_ring
    _ = -omegaOp * H * (-1) := by rw [omegaOp_sq]
    _ = omegaOp * H := by noncomm_ring

/-- Any `Θ`-odd self-adjoint operator (`sympTimeRev M = -M` and `Mᴴ = M`) anticommutes with `omegaOp`. -/
theorem zeeman_odd_selfAdjoint_anticommutes_omega
    {M : Matrix (Fin 2) (Fin 2) B}
    (h_odd : sympTimeRev M = -M) (h_sa : Mᴴ = M) :
    M * omegaOp + omegaOp * M = 0 := by
  have h1 : -omegaOp * M * omegaOp = -M := by
    simpa [sympTimeRev, h_sa] using h_odd
  have h2 : M * omegaOp = -(omegaOp * M) := by
    calc
      M * omegaOp = -((-M) * omegaOp) := by noncomm_ring
      _ = -((-omegaOp * M * omegaOp) * omegaOp) := by rw [h1]
      _ = -(-omegaOp * M * (omegaOp * omegaOp)) := by noncomm_ring
      _ = -(-omegaOp * M * (-1)) := by rw [omegaOp_sq]
      _ = -(omegaOp * M) := by noncomm_ring
  rw [h2]
  abel

/-- Commutator parity under `sympTimeRev`:
`Θ([H, M]) = -[Θ(H), Θ(M)]`, so two `Θ`-odd operators have a `Θ`-odd commutator,
while a `Θ`-even and a `Θ`-odd operator have a `Θ`-even commutator. -/
theorem sympTimeRev_commutator (X Y : Matrix (Fin 2) (Fin 2) B) :
    sympTimeRev ⁅X, Y⁆ = -⁅sympTimeRev X, sympTimeRev Y⁆ := by
  simp only [Ring.lie_def, sympTimeRev_sub, sympTimeRev_mul]
  abel

theorem sympTimeRev_commutator_odd_odd
    {X Y : Matrix (Fin 2) (Fin 2) B}
    (hX : sympTimeRev X = -X) (hY : sympTimeRev Y = -Y) :
    sympTimeRev ⁅X, Y⁆ = -⁅X, Y⁆ := by
  rw [sympTimeRev_commutator, hX, hY]
  simp only [Ring.lie_def, neg_mul_neg]

theorem sympTimeRev_commutator_even_odd
    {H M : Matrix (Fin 2) (Fin 2) B}
    (hH : sympTimeRev H = H) (hM : sympTimeRev M = -M) :
    sympTimeRev ⁅H, M⁆ = ⁅H, M⁆ := by
  rw [sympTimeRev_commutator, hH, hM]
  simp only [Ring.lie_def, mul_neg, neg_mul]
  abel

end ArchetypeKC2_KramersZeemanDichotomy

/-! ## KC₃: Noncommutative Compass Bond Algebra & Hexagonal Plaquette Gauge Conjugation -/

section ArchetypeKC3_CompassPlaquetteAlgebra

/-- Six-bond hexagonal plaquette loop operator in any associative ring. -/
def hexPlaquette {R : Type*} [Mul R] (b₁ b₂ b₃ b₄ b₅ b₆ : R) : R :=
  b₁ * b₂ * b₃ * b₄ * b₅ * b₆

/-- Under local `ℤ₂` bond-gauge involutions `gᵢ² = 1`, transforming each bond
`bᵢ ↦ gᵢ * bᵢ * gᵢ₊₁` conjugates the hexagonal plaquette operator by `g₁`. -/
theorem hexPlaquette_gauge_conjugation {R : Type*} [Ring R]
    (b₁ b₂ b₃ b₄ b₅ b₆ g₁ g₂ g₃ g₄ g₅ g₆ : R)
    (hg₂ : g₂ * g₂ = 1) (hg₃ : g₃ * g₃ = 1) (hg₄ : g₄ * g₄ = 1)
    (hg₅ : g₅ * g₅ = 1) (hg₆ : g₆ * g₆ = 1) :
    hexPlaquette (g₁ * b₁ * g₂) (g₂ * b₂ * g₃) (g₃ * b₃ * g₄)
      (g₄ * b₄ * g₅) (g₅ * b₅ * g₆) (g₆ * b₆ * g₁) =
      g₁ * hexPlaquette b₁ b₂ b₃ b₄ b₅ b₆ * g₁ := by
  dsimp [hexPlaquette]
  calc
    (g₁ * b₁ * g₂) * (g₂ * b₂ * g₃) * (g₃ * b₃ * g₄) *
        (g₄ * b₄ * g₅) * (g₅ * b₅ * g₆) * (g₆ * b₆ * g₁)
      = g₁ * b₁ * (g₂ * g₂) * b₂ * (g₃ * g₃) * b₃ *
          (g₄ * g₄) * b₄ * (g₅ * g₅) * b₅ * (g₆ * g₆) * b₆ * g₁ := by
        noncomm_ring
    _ = g₁ * b₁ * 1 * b₂ * 1 * b₃ * 1 * b₄ * 1 * b₅ * 1 * b₆ * g₁ := by
        rw [hg₂, hg₃, hg₄, hg₅, hg₆]
    _ = g₁ * (b₁ * b₂ * b₃ * b₄ * b₅ * b₆) * g₁ := by
        noncomm_ring

/-- In `M₂(B)`, the compass triple `(gamma1Op, sigmaOp, omegaOp)` realizes a
noncommutative Clifford triple whose 6-bond alternating plaquette equals `1`. -/
theorem zorn_compass_triple_plaquette {B : Type*} [Ring B] :
    (gamma1Op : Matrix (Fin 2) (Fin 2) B) * sigmaOp = -omegaOp ∧
    hexPlaquette (gamma1Op : Matrix (Fin 2) (Fin 2) B) sigmaOp omegaOp
      gamma1Op sigmaOp omegaOp = 1 := by
  refine ⟨?_, ?_⟩
  · apply ext_fin2 <;> simp [gamma1Op, sigmaOp, omegaOp]
  · apply ext_fin2 <;> simp [hexPlaquette, gamma1Op, sigmaOp, omegaOp]

end ArchetypeKC3_CompassPlaquetteAlgebra

/-! ## KC₄: Antisymmetric Hall Commutator & Time-Reversal Selection Rule -/

section ArchetypeKC4_HallSelectionRule

variable {B : Type*} [Ring B] [StarRing B]

/-- The Hall commutator `[Jₓ, Jᵧ]` is antisymmetric and, for self-adjoint
currents `Jₓᴴ = Jₓ`, `Jᵧᴴ = Jᵧ`, is skew-adjoint: `([Jₓ, Jᵧ])ᴴ = -[Jₓ, Jᵧ]`. -/
theorem hall_commutator_antisymm_and_skew
    (Jₓ Jᵧ : Matrix (Fin 2) (Fin 2) B)
    (hx : Jₓᴴ = Jₓ) (hy : Jᵧᴴ = Jᵧ) :
    ⁅Jₓ, Jᵧ⁆ = -⁅Jᵧ, Jₓ⁆ ∧ (⁅Jₓ, Jᵧ⁆)ᴴ = -⁅Jₓ, Jᵧ⁆ := by
  refine ⟨?_, ?_⟩
  · simp only [Ring.lie_def]
    abel
  · simp only [Ring.lie_def, conjTranspose_sub, conjTranspose_mul, hx, hy]
    abel

/-- **Time-Reversal / Kramers Selection Rule for the Hall Commutator**:
If two currents `Jₓ, Jᵧ` are `Θ`-odd (`sympTimeRev J = -J`), then for any
`Θ`-invariant additive functional `ω : M₂(B) →+ B` (`∀ X, ω (sympTimeRev X) = ω X`),
the Hall commutator expectation satisfies `2 • ω ⁅Jₓ, Jᵧ⁆ = 0`. -/
theorem hall_commutator_vanishes_under_trs
    (ω : Matrix (Fin 2) (Fin 2) B →+ B)
    (hω : ∀ X, ω (sympTimeRev X) = ω X)
    (Jₓ Jᵧ : Matrix (Fin 2) (Fin 2) B)
    (hx : sympTimeRev Jₓ = -Jₓ) (hy : sympTimeRev Jᵧ = -Jᵧ) :
    (2 : ℕ) • ω ⁅Jₓ, Jᵧ⁆ = 0 := by
  have hodd : sympTimeRev ⁅Jₓ, Jᵧ⁆ = -⁅Jₓ, Jᵧ⁆ :=
    sympTimeRev_commutator_odd_odd hx hy
  have h_eq : ω ⁅Jₓ, Jᵧ⁆ = -ω ⁅Jₓ, Jᵧ⁆ := by
    calc
      ω ⁅Jₓ, Jᵧ⁆ = ω (sympTimeRev ⁅Jₓ, Jᵧ⁆) := (hω _).symm
      _ = ω (-⁅Jₓ, Jᵧ⁆) := by rw [hodd]
      _ = -ω ⁅Jₓ, Jᵧ⁆ := map_neg ω _
  rw [two_smul]
  calc
    ω ⁅Jₓ, Jᵧ⁆ + ω ⁅Jₓ, Jᵧ⁆ = ω ⁅Jₓ, Jᵧ⁆ + (-ω ⁅Jₓ, Jᵧ⁆) := by
      conv_rhs => rw [← h_eq]
    _ = 0 := add_neg_cancel _

end ArchetypeKC4_HallSelectionRule

/-- Explicit non-commutativity witness for `Matrix (Fin 2) (Fin 2) B` over any nontrivial ring. -/
theorem mat2_basis_noncommuting {B : Type*} [Ring B] [Nontrivial B] :
    ∃ A C : Matrix (Fin 2) (Fin 2) B, A * C ≠ C * A := by
  refine ⟨!![1, 0; 0, 0], !![0, 1; 0, 0], ?_⟩
  intro h
  have h01 := congrArg (fun M => M 0 1) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01

end InfoGeometry.Algebra.NoncommutativeKramersCompassHallSynthesis
