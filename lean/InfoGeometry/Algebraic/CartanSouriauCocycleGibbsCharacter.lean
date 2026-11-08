import InfoGeometry.Algebraic.CartanSouriauAffineCocycle
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

/-!
# Gibbs multipliers from affine Souriau cocycles

The additive cocycle is read through a pairing with the thermodynamic
parameter.  Exponentiation turns the additive defect into a multiplicative
twisted character.  The pairing and its transported parameter action are
kept explicit; no arithmetic symmetry group is assumed.
-/

namespace InfoGeometry.Algebraic.CartanSouriauCocycleGibbsCharacter

open InfoGeometry.Algebraic.CartanSouriauAffineCocycle

variable {G M B : Type*} [Group G] [AddCommGroup M] [AddCommGroup B]

structure GibbsDatum (G M B : Type*) [Group G] [AddCommGroup M] [AddCommGroup B] where
  affine : InfoGeometry.Algebraic.CartanSouriauAffineCocycle.Datum
    (G := G) (M := M)
  pairing : M → B → ℝ
  pairing_add_left : ∀ x y β,
    pairing (x + y) β = pairing x β + pairing y β
  parameterAction : G → B → B
  pairing_transport : ∀ g x β,
    pairing (affine.dualAction g x) β =
      pairing x (parameterAction g β)

noncomputable def gibbsMultiplier (D : GibbsDatum G M B) (g : G) (β : B) : ℝ :=
  Real.exp (-(D.pairing (D.affine.theta g) β))

theorem pairing_zero_left (D : GibbsDatum G M B) (β : B) :
    D.pairing (0 : M) β = 0 := by
  have hzero : D.pairing (0 : M) β =
      D.pairing (0 : M) β + D.pairing (0 : M) β := by
    simpa using D.pairing_add_left (0 : M) 0 β
  linarith

theorem gibbsMultiplier_one (D : GibbsDatum G M B) (β : B) :
    gibbsMultiplier D 1 β = 1 := by
  unfold gibbsMultiplier
  rw [D.affine.theta_one]
  rw [pairing_zero_left D β]
  simp

theorem gibbsMultiplier_mul (D : GibbsDatum G M B) (g h : G) (β : B) :
    gibbsMultiplier D (g * h) β =
      gibbsMultiplier D g β *
        gibbsMultiplier D h (D.parameterAction g β) := by
  unfold gibbsMultiplier
  rw [D.affine.theta_mul, D.pairing_add_left,
    D.pairing_transport]
  rw [neg_add, Real.exp_add]

theorem gibbsMultiplier_pos (D : GibbsDatum G M B) (g : G) (β : B) :
    0 < gibbsMultiplier D g β := by
  unfold gibbsMultiplier
  exact Real.exp_pos _

theorem gibbsMultiplier_ne_zero (D : GibbsDatum G M B) (g : G) (β : B) :
    gibbsMultiplier D g β ≠ 0 := by
  exact ne_of_gt (gibbsMultiplier_pos D g β)

theorem gibbsMultiplier_inv_transported (D : GibbsDatum G M B)
    (g : G) (β : B) :
    gibbsMultiplier D g⁻¹ (D.parameterAction g β) =
      (gibbsMultiplier D g β)⁻¹ := by
  have hmul := gibbsMultiplier_mul D g g⁻¹ β
  rw [mul_inv_cancel, gibbsMultiplier_one] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

theorem parameterAction_one (D : GibbsDatum G M B) (β : B)
    (h_sep : ∀ x y : B, (∀ μ : M, D.pairing μ x = D.pairing μ y) → x = y) :
    D.parameterAction 1 β = β := by
  apply h_sep
  intro μ
  rw [← D.pairing_transport, D.affine.dualAction_one, AddMonoidHom.id_apply]

theorem parameterAction_mul (D : GibbsDatum G M B) (g h : G) (β : B)
    (h_sep : ∀ x y : B, (∀ μ : M, D.pairing μ x = D.pairing μ y) → x = y) :
    D.parameterAction (g * h) β = D.parameterAction h (D.parameterAction g β) := by
  apply h_sep
  intro μ
  rw [← D.pairing_transport, D.affine.dualAction_mul, AddMonoidHom.comp_apply,
    D.pairing_transport, D.pairing_transport]

end InfoGeometry.Algebraic.CartanSouriauCocycleGibbsCharacter
