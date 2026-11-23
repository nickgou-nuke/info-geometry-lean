/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.SouriauMetriplecticAttentionCasimirPoset

/-!
# The metriplectic dissipator as an orthogonal Peirce projection

Carrier: an arbitrary noncommutative ring `B` with an idempotent `P`, and (for the
geometric part) a star structure with self-adjoint `P` and a cyclic functional
`τ : B →+ R` defining the sesquilinear pairing `⟨X, Y⟩ = τ (X⋆ Y)`.
The dissipator is `Δ_diss P X = [P, [P, X]]` from
`SouriauMetriplecticParabolicWeitzenbockPoset`.

## Equilibria (Peirce, purely algebraic)
* `comm_eq_zero_iff_offdiag_zero` – `[P, W] = 0 ↔ Q₊(W) = 0 ∧ Q₋(W) = 0`.
* `commutant_eq_block_diagonal` – the commutant of `P` is block diagonal,
  `W = P W P + (1 - P) W (1 - P)`.
* `Delta_diss_eq_zero_iff` – `ker Δ_diss = commutant of P`.

## Orthogonal projection (star ring, cyclic `τ`)
* `ad_symm` – for self-adjoint `P`, `ad_P` is symmetric for `⟨·,·⟩`.
* `Delta_diss_symm` – `Δ_diss` is symmetric; the quadratic-form identity is used
  directly in the positivity proof.
* `Delta_diss_positive_faithful` – positivity, vanishing exactly on the commutant.
* `Delta_diss_orthogonal_projection` – `Δ_diss` is idempotent, symmetric, and its range is
  `⟨·,·⟩`-orthogonal to its complement: `⟨Δ X, Y - Δ Y⟩ = 0`.

## Lyapunov equilibria
* `lyapunov_rate_zero_iff_block_diagonal` – along the Brockett–Souriau flow with energy
  `H = P`, the Lyapunov rate `τ (dW · P)` vanishes exactly when `W` is Peirce block diagonal.
-/

namespace SouriauMetriplecticAttentionCasimirPoset.Dissipator

open InfoGeometry.Canonical.SouriauMetriplecticParabolicWeitzenbockPoset
  (Q_pos Q_neg X_11 X_00 P_perp Delta_diss peirce_fourfold_partition
    metriplectic_lindblad_modular_synthesis proj_perp_zero perp_proj_zero)

variable {B : Type*} [Ring B] {R : Type*} [CommRing R]

/-! ### Peirce corner absorption -/

/-- Left multiplication by the idempotent fixes its positive off-diagonal Peirce corner. -/
lemma P_mul_Q_pos {P : B} (hP : P * P = P) (X : B) : P * Q_pos P X = Q_pos P X := by
  simp only [Q_pos, ← mul_assoc, hP]

/-- Right multiplication by the idempotent annihilates its positive off-diagonal corner. -/
lemma Q_pos_mul_P {P : B} (hP : P * P = P) (X : B) : Q_pos P X * P = 0 := by
  simp only [Q_pos, mul_assoc, perp_proj_zero hP, mul_zero]

/-- Left multiplication by the idempotent annihilates its negative off-diagonal corner. -/
lemma P_mul_Q_neg {P : B} (hP : P * P = P) (X : B) : P * Q_neg P X = 0 := by
  simp only [Q_neg, ← mul_assoc, proj_perp_zero hP, zero_mul]

/-- Right multiplication by the idempotent fixes its negative off-diagonal Peirce corner. -/
lemma Q_neg_mul_P {P : B} (hP : P * P = P) (X : B) : Q_neg P X * P = Q_neg P X := by
  simp only [Q_neg, mul_assoc, hP]

/-- Antisymmetry of the commutator. -/
lemma comm_swap (X Y : B) : comm X Y = - comm Y X := by
  rw [comm, comm, neg_sub]

/-! ### Equilibria: commutant = Peirce block diagonal -/

/-- `[P, W] = 0` iff both off-diagonal Peirce corners of `W` vanish. -/
theorem comm_eq_zero_iff_offdiag_zero {P : B} (hP : P * P = P) (W : B) :
    comm P W = 0 ↔ Q_pos P W = 0 ∧ Q_neg P W = 0 := by
  have hJ : comm P W = Q_pos P W - Q_neg P W :=
    (metriplectic_lindblad_modular_synthesis hP W W).1
  constructor
  · intro h
    rw [hJ] at h
    have h1 : P * (Q_pos P W - Q_neg P W) = 0 := by rw [h, mul_zero]
    have h2 : (Q_pos P W - Q_neg P W) * P = 0 := by rw [h, zero_mul]
    rw [mul_sub, P_mul_Q_pos hP, P_mul_Q_neg hP, sub_zero] at h1
    rw [sub_mul, Q_pos_mul_P hP, Q_neg_mul_P hP, zero_sub, neg_eq_zero] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [hJ, h1, h2, sub_zero]

/-- The commutant of an idempotent is block diagonal: `W = P W P + (1-P) W (1-P)`. -/
theorem commutant_eq_block_diagonal {P : B} (hP : P * P = P) (W : B) (h : comm P W = 0) :
    W = X_11 P W + X_00 P W := by
  obtain ⟨h1, h2⟩ := (comm_eq_zero_iff_offdiag_zero hP W).mp h
  have hW := peirce_fourfold_partition P W
  rw [h1, h2, add_zero, add_zero] at hW
  exact hW

/-- The kernel of the dissipator is exactly the commutant of `P`. -/
theorem Delta_diss_eq_zero_iff {P : B} (hP : P * P = P) (X : B) :
    Delta_diss P X = 0 ↔ comm P X = 0 := by
  have hΔ : Delta_diss P X = Q_pos P X + Q_neg P X :=
    (metriplectic_lindblad_modular_synthesis hP X X).2.1
  rw [comm_eq_zero_iff_offdiag_zero hP X]
  constructor
  · intro h
    rw [hΔ] at h
    have h1 : P * (Q_pos P X + Q_neg P X) = 0 := by rw [h, mul_zero]
    have h2 : (Q_pos P X + Q_neg P X) * P = 0 := by rw [h, zero_mul]
    rw [mul_add, P_mul_Q_pos hP, P_mul_Q_neg hP, add_zero] at h1
    rw [add_mul, Q_pos_mul_P hP, Q_neg_mul_P hP, zero_add] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [hΔ, h1, h2, add_zero]

/-! ### Orthogonal projection for the trace pairing `⟨X, Y⟩ = τ (X⋆ Y)` -/

section Star

variable [StarRing B]

/-- For self-adjoint `P`, the inner derivation `ad_P` is symmetric for `⟨X, Y⟩ = τ (X⋆ Y)`. -/
lemma ad_symm (τ : B →+ R) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    {P : B} (hPs : star P = P) (X Y : B) :
    τ (star X * comm P Y) = τ (star (comm P X) * Y) := by
  simp only [comm, star_sub, star_mul, hPs, mul_sub, sub_mul, map_sub, mul_assoc]
  rw [h_cyc P (star X * Y), mul_assoc]

/-- The dissipator `Δ_diss = ad_P²` is symmetric for the trace pairing. -/
theorem Delta_diss_symm (τ : B →+ R) (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    {P : B} (hPs : star P = P) (X Y : B) :
    τ (star X * Delta_diss P Y) = τ (star (Delta_diss P X) * Y) := by
  show τ (star X * comm P (comm P Y)) = τ (star (comm P (comm P X)) * Y)
  rw [ad_symm τ h_cyc hPs X, ad_symm τ h_cyc hPs (comm P X)]

/-- Positivity of the dissipator, vanishing exactly on the commutant of `P`. -/
theorem Delta_diss_positive_faithful [PartialOrder R] (τ : B →+ R)
    (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (hpos : ∀ Y : B, 0 ≤ τ (star Y * Y))
    (hfaith : ∀ Y : B, τ (star Y * Y) = 0 → Y = 0)
    {P : B} (hPs : star P = P) (X : B) :
    0 ≤ τ (star X * Delta_diss P X) ∧
      (τ (star X * Delta_diss P X) = 0 ↔ comm P X = 0) := by
  have hform : τ (star X * Delta_diss P X) = τ (star (comm P X) * comm P X) :=
    ad_symm τ h_cyc hPs X (comm P X)
  rw [hform]
  exact ⟨hpos _, hfaith _, fun h => by rw [h, mul_zero, map_zero]⟩

/-- **The dissipator is an orthogonal projection**: for a self-adjoint idempotent `P`,
`Δ_diss` is idempotent, symmetric for `⟨X, Y⟩ = τ (X⋆ Y)`, and its range is orthogonal to
the range of `1 - Δ_diss`. Its range is the off-diagonal Peirce space `Q₊ ⊕ Q₋` and its
kernel the commutant of `P` (`Delta_diss_eq_zero_iff`). -/
theorem Delta_diss_orthogonal_projection (τ : B →+ R)
    (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    {P : B} (hP : P * P = P) (hPs : star P = P) (X Y : B) :
    Delta_diss P (Delta_diss P X) = Delta_diss P X ∧
    τ (star X * Delta_diss P Y) = τ (star (Delta_diss P X) * Y) ∧
    τ (star (Delta_diss P X) * (Y - Delta_diss P Y)) = 0 := by
  have hidem : Delta_diss P (Delta_diss P X) = Delta_diss P X :=
    (metriplectic_lindblad_modular_synthesis hP X X).2.2.2.2.2.1
  refine ⟨hidem, Delta_diss_symm τ h_cyc hPs X Y, ?_⟩
  rw [mul_sub, map_sub, Delta_diss_symm τ h_cyc hPs (Delta_diss P X) Y, hidem, sub_self]

/-- **Lyapunov equilibria are block diagonal**: along the Brockett–Souriau flow with energy
`H = P` (a self-adjoint idempotent commuting with `Ω`), and self-adjoint `W`, the Lyapunov
rate `τ (dW · P)` vanishes exactly when both off-diagonal Peirce corners of `W` vanish. -/
theorem lyapunov_rate_zero_iff_block_diagonal [PartialOrder R] (τ : B →+ R)
    (h_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (hpos : ∀ Y : B, 0 ≤ τ (star Y * Y))
    (hfaith : ∀ Y : B, τ (star Y * Y) = 0 → Y = 0)
    (Ω P W : B) (hP : P * P = P) (hΩP : comm Ω P = 0) (hPs : star P = P)
    (hW : star W = W) :
    τ (brockettSouriauWeightFlow Ω P W * P) = 0 ↔ Q_pos P W = 0 ∧ Q_neg P W = 0 := by
  rw [(brockett_souriau_lyapunov τ h_cyc hpos hfaith Ω P W hΩP hPs hW).2.2, comm_swap,
    neg_eq_zero, comm_eq_zero_iff_offdiag_zero hP]

end Star

end SouriauMetriplecticAttentionCasimirPoset.Dissipator
