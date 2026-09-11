import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

abbrev VirasoroBasis := ℤ ⊕ Unit

variable (R : Type*) [CommRing R] [Invertible (12 : R)]

abbrev VirasoroModule := VirasoroBasis →₀ R

noncomputable def virasoroBracketBasis (x y : VirasoroBasis) : VirasoroModule R :=
  match x, y with
  | Sum.inl m, Sum.inl n =>
    let term1 := (m - n : R) • Finsupp.single (Sum.inl (m + n)) (1 : R)
    let term2 := if m + n = 0 then
                   (((m^3 - m : ℤ) : R) * ⅟(12 : R)) • Finsupp.single (Sum.inr ()) (1 : R)
                 else 0
    term1 + term2
  | _, _ => 0

noncomputable def virasoroBracketBilin : VirasoroModule R →ₗ[R] VirasoroModule R →ₗ[R] VirasoroModule R :=
  Finsupp.linearCombination R (fun x => Finsupp.linearCombination R (fun y => virasoroBracketBasis R x y))

noncomputable instance : Bracket (VirasoroModule R) (VirasoroModule R) where
  bracket x y := virasoroBracketBilin R x y

lemma virasoroBracketBasis_self (x : VirasoroBasis) : virasoroBracketBasis R x x = 0 := by
  cases x with
  | inl m =>
    dsimp [virasoroBracketBasis]
    have hsub : ((m : R) - (m : R)) = 0 := sub_self _
    rw [hsub, zero_smul]
    split
    · next hsum =>
      have hm : m = 0 := by omega
      subst hm
      simp
    · simp
  | inr _ =>
    rfl

lemma virasoro_bracket_add_left (x y z : VirasoroModule R) :
    ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := by
  change virasoroBracketBilin R (x + y) z =
    virasoroBracketBilin R x z + virasoroBracketBilin R y z
  simp

lemma virasoro_bracket_add_right (x y z : VirasoroModule R) :
    ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆ := by
  change virasoroBracketBilin R x (y + z) =
    virasoroBracketBilin R x y + virasoroBracketBilin R x z
  simp

lemma virasoro_bracket_smul_left (t : R) (x y : VirasoroModule R) :
    ⁅t • x, y⁆ = t • ⁅x, y⁆ := by
  change virasoroBracketBilin R (t • x) y = t • virasoroBracketBilin R x y
  simp

lemma virasoro_bracket_smul_right (t : R) (x y : VirasoroModule R) :
    ⁅x, t • y⁆ = t • ⁅x, y⁆ := by
  change virasoroBracketBilin R x (t • y) = t • virasoroBracketBilin R x y
  simp

structure VirasoroLieLaws where
  lie_self : ∀ x : VirasoroModule R, ⁅x, x⁆ = 0
  leibniz_lie :
    ∀ x y z : VirasoroModule R, ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆
