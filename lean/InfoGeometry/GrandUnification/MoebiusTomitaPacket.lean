import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Conditional commutant and modular-reflection identities

This file defines a commutant for a supplied submodule of endomorphisms and
packages explicit algebraic hypotheses for a supplied involution. It does not
construct a von Neumann algebra, prove the Tomita–Takesaki theorem, or derive
the involution from Klein-bottle or Möbius topology. The mathematical thread
retained here is the relation between an algebra, its commutant, and a chosen
conjugation-like map, with each required identity stated as a premise.
-/

namespace InfoGeometry.GrandUnification.MoebiusTomitaPacket

open LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### 1. A bilinear form and its isometric involution -/

/-- An involutive linear isometry of a supplied bilinear form. This predicate
does not assert nondegeneracy, indefiniteness, or completeness of the form. -/
structure KreinSymmetry
    (Q : LinearMap.BilinForm R M) (J : Module.End R M) : Prop where
  involutive : J * J = 1
  preserves_form : ∀ x y : M, Q (J x) (J y) = Q x y

/-! ### 2. The Commutant (The Dual Reality) -/

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

/-! ### 3. Conditional algebraic reflection laws -/

structure InvolutiveCommutantReflection
    (J : Module.End R M) (A : Submodule R (Module.End R M)) : Prop where
  involutive : J * J = 1
  maps_into_commutant : ∀ X ∈ A, (J * X * J) ∈ Commutant A
  surjective_onto_commutant : ∀ Y ∈ Commutant A, ∃ X ∈ A, Y = J * X * J

/-! ### 4. A scalar-submodule commutant lemma -/

theorem commutant_maximal_of_algebra_trivial
    (h_trivial : ∀ X ∈ ℳ, ∃ c : R, X = c • (1 : Module.End R M)) :
    ∀ Y : Module.End R M, Y ∈ Commutant ℳ := by
  intro Y X hX
  rcases h_trivial X hX with ⟨c, rfl⟩
  calc (c • 1) * Y = c • (1 * Y) := by rw [smul_mul_assoc]
       _ = c • Y := by rw [one_mul]
       _ = c • (Y * 1) := by rw [mul_one]
       _ = Y * (c • 1) := (mul_smul_comm c Y 1).symm

/--
This structure packages a supplied endomorphism, submodule, and the displayed
reflection/nontriviality hypotheses. It does not prove that such data exist or
that they arise from a geometric parity twist.
-/
structure CommutantReflectionData where
  algebra : Submodule R (Module.End R M)
  kreinForm : LinearMap.BilinForm R M
  involution : Module.End R M
  krein_symmetry : KreinSymmetry kreinForm involution
  reflection : InvolutiveCommutantReflection involution algebra
  nontrivial_algebra : ∃ X ∈ algebra, ∀ c : R, X ≠ c • (1 : Module.End R M)
  operator : Module.End R M
  operator_anticommutes_with_involution :
    involution * operator = - (operator * involution)

end InfoGeometry.GrandUnification.MoebiusTomitaPacket
