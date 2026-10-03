import Mathlib.Algebra.Algebra.Basic

/-!
# Commutants and involutive conjugation

This file proves an elementary commutant closure fact and the double-conjugation
identity for an involution in an endomorphism ring. These algebraic results do
not construct a von Neumann algebra, prove the Tomita–Takesaki theorem, or
derive an involution from Klein-bottle or Möbius topology.
-/

namespace InfoGeometry.GrandUnification.MoebiusTomitaPacket

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### The commutant of a submodule of endomorphisms -/

variable (ℳ : Submodule R (Module.End R M))

def Commutant (ℳ : Submodule R (Module.End R M)) : Submodule R (Module.End R M) where
  carrier := { Y | ∀ X ∈ ℳ, X * Y = Y * X }
  add_mem' {Y1 Y2} hY1 hY2 X hX := by
    calc X * (Y1 + Y2) = X * Y1 + X * Y2 := mul_add X Y1 Y2
         _ = Y1 * X + Y2 * X := by rw [hY1 X hX, hY2 X hX]
         _ = (Y1 + Y2) * X := (add_mul Y1 Y2 X).symm
  zero_mem' X _ := by
    rw [mul_zero, zero_mul]
  smul_mem' c Y hY X hX := by
    calc X * (c • Y) = c • (X * Y) := mul_smul_comm c X Y
         _ = c • (Y * X) := by rw [hY X hX]
         _ = (c • Y) * X := (smul_mul_assoc c Y X).symm

/-! ### Double conjugation by an involution -/

/-- Conjugation by an involution is itself involutive in the endomorphism ring. -/
theorem conjugation_by_involution_involutive
    (J X : Module.End R M) (hJ : J * J = 1) :
    J * (J * X * J) * J = X := by
  calc
    J * (J * X * J) * J = (J * J) * X * (J * J) := by noncomm_ring
    _ = (1 : Module.End R M) * X * 1 := by rw [hJ]
    _ = X := by simp

/-! ### 4. A scalar-submodule commutant lemma -/

theorem scalar_submodule_mem_commutant
    (h_trivial : ∀ X ∈ ℳ, ∃ c : R, X = c • (1 : Module.End R M)) :
    ∀ Y : Module.End R M, Y ∈ Commutant ℳ := by
  intro Y X hX
  rcases h_trivial X hX with ⟨c, rfl⟩
  calc (c • 1) * Y = c • (1 * Y) := by rw [smul_mul_assoc]
       _ = c • Y := by rw [one_mul]
       _ = c • (Y * 1) := by rw [mul_one]
       _ = Y * (c • 1) := (mul_smul_comm c Y 1).symm

end InfoGeometry.GrandUnification.MoebiusTomitaPacket
