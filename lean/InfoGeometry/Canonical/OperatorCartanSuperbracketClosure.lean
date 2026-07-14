import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.NoncommRing

/-!
# InfoGeometry.Canonical.OperatorCartanSuperbracketClosure

Operator-level Cartan/superbracket closure.

This file proves finite operator equalities in the associative endomorphism ring
`V →ₗ[𝕜] V`, with grading implemented by an involutive operator `Γ`.

No analytic continuation.
No structure packet.
No wrapper.
-/

namespace OperatorCartanSuperbracketClosure

variable {𝕜 V : Type*}
variable [CommRing 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/-- Conjugation by an involutive grading operator is itself involutive. -/
theorem operator_grading_conjugation_involutive
    (Γ T : V →ₗ[𝕜] V)
    (hΓ : Γ * Γ = 1) :
    Γ * (Γ * T * Γ) * Γ = T := by
  calc
    Γ * (Γ * T * Γ) * Γ
        = (Γ * Γ) * T * (Γ * Γ) := by
            noncomm_ring
    _ = 1 * T * 1 := by
            rw [hΓ]
    _ = T := by
            simp

/-- Evenness by conjugation is equivalent to commuting with the grading operator. -/
theorem operator_even_conj_iff_commutes
    (Γ T : V →ₗ[𝕜] V)
    (hΓ : Γ * Γ = 1) :
    Γ * T * Γ = T ↔ Γ * T = T * Γ := by
  constructor
  · intro h
    calc
      Γ * T
          = Γ * T * 1 := by
              simp
      _ = Γ * T * (Γ * Γ) := by
              rw [hΓ]
      _ = (Γ * T * Γ) * Γ := by
              noncomm_ring
      _ = T * Γ := by
              rw [h]
  · intro h
    calc
      Γ * T * Γ
          = (T * Γ) * Γ := by
              rw [h]
      _ = T * (Γ * Γ) := by
              noncomm_ring
      _ = T := by
              simp [hΓ]

/-- Oddness by conjugation is equivalent to anticommuting with the grading operator. -/
theorem operator_odd_conj_iff_anticommutes
    (Γ T : V →ₗ[𝕜] V)
    (hΓ : Γ * Γ = 1) :
    Γ * T * Γ = -T ↔ Γ * T = -T * Γ := by
  constructor
  · intro h
    calc
      Γ * T
          = Γ * T * 1 := by
              simp
      _ = Γ * T * (Γ * Γ) := by
              rw [hΓ]
      _ = (Γ * T * Γ) * Γ := by
              noncomm_ring
      _ = (-T) * Γ := by
              rw [h]
      _ = -T * Γ := by
              rfl
  · intro h
    calc
      Γ * T * Γ
          = (-T * Γ) * Γ := by
              rw [h]
      _ = -T * (Γ * Γ) := by
              noncomm_ring
      _ = -T := by
              simp [hΓ]

/-- Even-even commutator closure. -/
theorem operator_even_even_commutator_even
    (Γ X Y : V →ₗ[𝕜] V)
    (hX : Γ * X = X * Γ)
    (hY : Γ * Y = Y * Γ) :
    Γ * (X * Y - Y * X) = (X * Y - Y * X) * Γ := by
  calc
    Γ * (X * Y - Y * X)
        = Γ * X * Y - Γ * Y * X := by
            noncomm_ring
    _ = (X * Γ) * Y - (Y * Γ) * X := by
            rw [hX, hY]
    _ = X * (Γ * Y) - Y * (Γ * X) := by
            noncomm_ring
    _ = X * (Y * Γ) - Y * (X * Γ) := by
            rw [hY, hX]
    _ = (X * Y - Y * X) * Γ := by
            noncomm_ring

/-- Even-odd commutator closure. -/
theorem operator_even_odd_commutator_odd
    (Γ X Y : V →ₗ[𝕜] V)
    (hX : Γ * X = X * Γ)
    (hY : Γ * Y = -Y * Γ) :
    Γ * (X * Y - Y * X) = -(X * Y - Y * X) * Γ := by
  calc
    Γ * (X * Y - Y * X)
        = Γ * X * Y - Γ * Y * X := by
            noncomm_ring
    _ = (X * Γ) * Y - (-Y * Γ) * X := by
            rw [hX, hY]
    _ = X * (Γ * Y) - (-Y) * (Γ * X) := by
            noncomm_ring
    _ = X * (-Y * Γ) - (-Y) * (X * Γ) := by
            rw [hY, hX]
    _ = -(X * Y - Y * X) * Γ := by
            noncomm_ring

/-- Odd-even commutator closure. -/
theorem operator_odd_even_commutator_odd
    (Γ X Y : V →ₗ[𝕜] V)
    (hX : Γ * X = -X * Γ)
    (hY : Γ * Y = Y * Γ) :
    Γ * (X * Y - Y * X) = -(X * Y - Y * X) * Γ := by
  calc
    Γ * (X * Y - Y * X)
        = Γ * X * Y - Γ * Y * X := by
            noncomm_ring
    _ = (-X * Γ) * Y - (Y * Γ) * X := by
            rw [hX, hY]
    _ = (-X) * (Γ * Y) - Y * (Γ * X) := by
            noncomm_ring
    _ = (-X) * (Y * Γ) - Y * (-X * Γ) := by
            rw [hY, hX]
    _ = -(X * Y - Y * X) * Γ := by
            noncomm_ring

/-- Odd-odd commutator closure. -/
theorem operator_odd_odd_commutator_even
    (Γ X Y : V →ₗ[𝕜] V)
    (hX : Γ * X = -X * Γ)
    (hY : Γ * Y = -Y * Γ) :
    Γ * (X * Y - Y * X) = (X * Y - Y * X) * Γ := by
  calc
    Γ * (X * Y - Y * X)
        = Γ * X * Y - Γ * Y * X := by
            noncomm_ring
    _ = (-X * Γ) * Y - (-Y * Γ) * X := by
            rw [hX, hY]
    _ = (-X) * (Γ * Y) - (-Y) * (Γ * X) := by
            noncomm_ring
    _ = (-X) * (-Y * Γ) - (-Y) * (-X * Γ) := by
            rw [hY, hX]
    _ = (X * Y - Y * X) * Γ := by
            noncomm_ring

/-- Even-even anticommutator closure. -/
theorem operator_even_even_anticommutator_even
    (Γ X Y : V →ₗ[𝕜] V)
    (hX : Γ * X = X * Γ)
    (hY : Γ * Y = Y * Γ) :
    Γ * (X * Y + Y * X) = (X * Y + Y * X) * Γ := by
  calc
    Γ * (X * Y + Y * X)
        = Γ * X * Y + Γ * Y * X := by
            noncomm_ring
    _ = (X * Γ) * Y + (Y * Γ) * X := by
            rw [hX, hY]
    _ = X * (Γ * Y) + Y * (Γ * X) := by
            noncomm_ring
    _ = X * (Y * Γ) + Y * (X * Γ) := by
            rw [hY, hX]
    _ = (X * Y + Y * X) * Γ := by
            noncomm_ring

/-- Even-odd anticommutator closure. -/
theorem operator_even_odd_anticommutator_odd
    (Γ X Y : V →ₗ[𝕜] V)
    (hX : Γ * X = X * Γ)
    (hY : Γ * Y = -Y * Γ) :
    Γ * (X * Y + Y * X) = -(X * Y + Y * X) * Γ := by
  calc
    Γ * (X * Y + Y * X)
        = Γ * X * Y + Γ * Y * X := by
            noncomm_ring
    _ = (X * Γ) * Y + (-Y * Γ) * X := by
            rw [hX, hY]
    _ = X * (Γ * Y) + (-Y) * (Γ * X) := by
            noncomm_ring
    _ = X * (-Y * Γ) + (-Y) * (X * Γ) := by
            rw [hY, hX]
    _ = -(X * Y + Y * X) * Γ := by
            noncomm_ring

/-- Odd-even anticommutator closure. -/
theorem operator_odd_even_anticommutator_odd
    (Γ X Y : V →ₗ[𝕜] V)
    (hX : Γ * X = -X * Γ)
    (hY : Γ * Y = Y * Γ) :
    Γ * (X * Y + Y * X) = -(X * Y + Y * X) * Γ := by
  calc
    Γ * (X * Y + Y * X)
        = Γ * X * Y + Γ * Y * X := by
            noncomm_ring
    _ = (-X * Γ) * Y + (Y * Γ) * X := by
            rw [hX, hY]
    _ = (-X) * (Γ * Y) + Y * (Γ * X) := by
            noncomm_ring
    _ = (-X) * (Y * Γ) + Y * (-X * Γ) := by
            rw [hY, hX]
    _ = -(X * Y + Y * X) * Γ := by
            noncomm_ring

/-- Odd-odd anticommutator closure. -/
theorem operator_odd_odd_anticommutator_even
    (Γ X Y : V →ₗ[𝕜] V)
    (hX : Γ * X = -X * Γ)
    (hY : Γ * Y = -Y * Γ) :
    Γ * (X * Y + Y * X) = (X * Y + Y * X) * Γ := by
  calc
    Γ * (X * Y + Y * X)
        = Γ * X * Y + Γ * Y * X := by
            noncomm_ring
    _ = (-X * Γ) * Y + (-Y * Γ) * X := by
            rw [hX, hY]
    _ = (-X) * (Γ * Y) + (-Y) * (Γ * X) := by
            noncomm_ring
    _ = (-X) * (-Y * Γ) + (-Y) * (-X * Γ) := by
            rw [hY, hX]
    _ = (X * Y + Y * X) * Γ := by
            noncomm_ring

/-- Even square is even. -/
theorem operator_even_square_even
    (Γ Q : V →ₗ[𝕜] V)
    (hQ : Γ * Q = Q * Γ) :
    Γ * (Q * Q) = (Q * Q) * Γ := by
  calc
    Γ * (Q * Q) = Γ * Q * Q := by noncomm_ring
    _ = (Q * Γ) * Q := by rw [hQ]
    _ = Q * (Γ * Q) := by noncomm_ring
    _ = Q * (Q * Γ) := by rw [hQ]
    _ = (Q * Q) * Γ := by noncomm_ring

/-- Odd square is even. -/
theorem operator_odd_square_even
    (Γ Q : V →ₗ[𝕜] V)
    (hQ : Γ * Q = -Q * Γ) :
    Γ * (Q * Q) = (Q * Q) * Γ := by
  calc
    Γ * (Q * Q)
        = Γ * Q * Q := by
            noncomm_ring
    _ = (-Q * Γ) * Q := by
            rw [hQ]
    _ = (-Q) * (Γ * Q) := by
            noncomm_ring
    _ = (-Q) * (-Q * Γ) := by
            rw [hQ]
    _ = (Q * Q) * Γ := by
            noncomm_ring

/-- Nilpotent odd lane remains zero under grading conjugation. -/
theorem operator_odd_square_zero_stable
    (Γ Q : V →ₗ[𝕜] V)
    (hQ : Γ * Q = -Q * Γ)
    (hzero : Q * Q = 0) :
    Γ * (Q * Q) * Γ = 0 := by
  have hEven : Γ * (Q * Q) = (Q * Q) * Γ :=
    operator_odd_square_even Γ Q hQ
  calc
    Γ * (Q * Q) * Γ = ((Q * Q) * Γ) * Γ := by rw [hEven]
    _ = (0 * Γ) * Γ := by rw [hzero]
    _ = 0 := by simp

/-- Operator Cartan/superbracket closure in conjugation form. -/
theorem operator_cartan_superbracket_conjugation_profile
    (Γ e₁ e₂ o₁ o₂ : V →ₗ[𝕜] V)
    (hΓ : Γ * Γ = 1)
    (he₁ : Γ * e₁ * Γ = e₁)
    (he₂ : Γ * e₂ * Γ = e₂)
    (ho₁ : Γ * o₁ * Γ = -o₁)
    (ho₂ : Γ * o₂ * Γ = -o₂) :
    Γ * (e₁ * e₂ - e₂ * e₁) * Γ = e₁ * e₂ - e₂ * e₁ ∧
    Γ * (e₁ * o₁ - o₁ * e₁) * Γ = -(e₁ * o₁ - o₁ * e₁) ∧
    Γ * (o₁ * e₁ - e₁ * o₁) * Γ = -(o₁ * e₁ - e₁ * o₁) ∧
    Γ * (o₁ * o₂ - o₂ * o₁) * Γ = o₁ * o₂ - o₂ * o₁ ∧
    Γ * (o₁ * o₂ + o₂ * o₁) * Γ = o₁ * o₂ + o₂ * o₁ ∧
    Γ * (o₁ * o₁) * Γ = o₁ * o₁ := by
  have he₁c : Γ * e₁ = e₁ * Γ :=
    (operator_even_conj_iff_commutes Γ e₁ hΓ).1 he₁
  have he₂c : Γ * e₂ = e₂ * Γ :=
    (operator_even_conj_iff_commutes Γ e₂ hΓ).1 he₂
  have ho₁c : Γ * o₁ = -o₁ * Γ :=
    (operator_odd_conj_iff_anticommutes Γ o₁ hΓ).1 ho₁
  have ho₂c : Γ * o₂ = -o₂ * Γ :=
    (operator_odd_conj_iff_anticommutes Γ o₂ hΓ).1 ho₂
  exact
    ⟨
      (operator_even_conj_iff_commutes Γ (e₁ * e₂ - e₂ * e₁) hΓ).2
        (operator_even_even_commutator_even Γ e₁ e₂ he₁c he₂c),
      (operator_odd_conj_iff_anticommutes Γ (e₁ * o₁ - o₁ * e₁) hΓ).2
        (operator_even_odd_commutator_odd Γ e₁ o₁ he₁c ho₁c),
      (operator_odd_conj_iff_anticommutes Γ (o₁ * e₁ - e₁ * o₁) hΓ).2
        (operator_odd_even_commutator_odd Γ o₁ e₁ ho₁c he₁c),
      (operator_even_conj_iff_commutes Γ (o₁ * o₂ - o₂ * o₁) hΓ).2
        (operator_odd_odd_commutator_even Γ o₁ o₂ ho₁c ho₂c),
      (operator_even_conj_iff_commutes Γ (o₁ * o₂ + o₂ * o₁) hΓ).2
        (operator_odd_odd_anticommutator_even Γ o₁ o₂ ho₁c ho₂c),
      (operator_even_conj_iff_commutes Γ (o₁ * o₁) hΓ).2
        (operator_odd_square_even Γ o₁ ho₁c)
    ⟩

end OperatorCartanSuperbracketClosure
