import Mathlib.Tactic

/-!
# The glide and modular conjugation `J`

Tomita--Takesaki modular conjugation obeys the algebraic inversion law

`J Δ J = Δ⁻¹`, with `J²=1`.

This is the same group-theoretic skeleton as the Klein/glide relation

`g a g⁻¹ = a⁻¹`.

So the non-orientable glide is the spatial incarnation of modular conjugation:
it reverses modular time / scale and identifies an excitation with its inverse.
-/

namespace GlideModularJ

variable {G : Type*} [Group G]

/-- `J` is an involutive modular conjugation. -/
def IsModularJ (J : G) : Prop := J * J = 1

/-- `J` inverts the modular operator `Δ`. -/
def ModularJInverts (J Δ : G) : Prop := J * Δ * J⁻¹ = Δ⁻¹

/-- Klein/glide relation: the glide sends a charge/operator to its inverse. -/
def GlideInverts (g a : G) : Prop := g * a * g⁻¹ = a⁻¹

/-- If `J²=1`, then using `J⁻¹` or `J` in the conjugation is equivalent. -/
theorem inv_eq_self_of_modularJ {J : G} (hJ : IsModularJ J) : J⁻¹ = J := by
  unfold IsModularJ at hJ
  calc
    J⁻¹ = J⁻¹ * (J * J) := by rw [hJ]; simp
    _ = J := by group

/-- With `J²=1`, the Tomita form `J Δ J = Δ⁻¹` follows. -/
theorem modularJ_tomita_form {J Δ : G} (hJ : IsModularJ J) (hInv : ModularJInverts J Δ) :
    J * Δ * J = Δ⁻¹ := by
  unfold ModularJInverts at hInv
  have hJinv : J⁻¹ = J := inv_eq_self_of_modularJ hJ
  calc
    J * Δ * J = J * Δ * J⁻¹ := by rw [hJinv]
    _ = Δ⁻¹ := hInv

/-- Conversely, the Tomita form implies the conjugation/inversion form when `J²=1`. -/
theorem modularJ_inverts_of_tomita_form {J Δ : G} (hJ : IsModularJ J)
    (h : J * Δ * J = Δ⁻¹) : ModularJInverts J Δ := by
  unfold ModularJInverts
  have hJinv : J⁻¹ = J := inv_eq_self_of_modularJ hJ
  calc
    J * Δ * J⁻¹ = J * Δ * J := by rw [hJinv]
    _ = Δ⁻¹ := h

/-- The Klein word `J Δ J Δ` equals the identity. -/
theorem modularJ_klein_word {J Δ : G} (hJ : IsModularJ J) (hInv : ModularJInverts J Δ) :
    J * Δ * J * Δ = 1 := by
  rw [modularJ_tomita_form hJ hInv]
  group

/-- `J` reverses integer modular time: `J Δⁿ J = Δ⁻ⁿ`. -/
theorem modularJ_reverses_zpow {J Δ : G} (hJ : IsModularJ J) (hInv : ModularJInverts J Δ)
    (n : ℤ) : J * Δ^n * J = Δ^(-n) := by
  have hconj : J * Δ^n * J⁻¹ = (Δ⁻¹)^n := by
    calc
      J * Δ^n * J⁻¹ = (MulAut.conj J) (Δ^n) := by rw [MulAut.conj_apply]
      _ = ((MulAut.conj J) Δ)^n := by rw [map_zpow]
      _ = (J * Δ * J⁻¹)^n := by rw [MulAut.conj_apply]
      _ = (Δ⁻¹)^n := by rw [hInv]
  rw [inv_eq_self_of_modularJ hJ] at hconj
  rw [hconj]
  exact inv_zpow' Δ n

end GlideModularJ
