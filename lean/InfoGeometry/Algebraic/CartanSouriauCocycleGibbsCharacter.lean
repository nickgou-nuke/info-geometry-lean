import InfoGeometry.Algebraic.CartanSouriauAffineCocycle
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

theorem gibbsMultiplier_one (D : GibbsDatum G M B) (β : B) :
    gibbsMultiplier D 1 β = 1 := by
  unfold gibbsMultiplier
  rw [D.affine.theta_one]
  have hzero : D.pairing (0 : M) β =
      D.pairing (0 : M) β + D.pairing (0 : M) β := by
    simpa using D.pairing_add_left (0 : M) 0 β
  have hpzero : D.pairing (0 : M) β = 0 := by
    linarith
  rw [hpzero]
  simp

theorem gibbsMultiplier_mul (D : GibbsDatum G M B) (g h : G) (β : B) :
    gibbsMultiplier D (g * h) β =
      gibbsMultiplier D g β *
        gibbsMultiplier D h (D.parameterAction g β) := by
  unfold gibbsMultiplier
  rw [D.affine.theta_mul, D.pairing_add_left,
    D.pairing_transport]
  rw [neg_add, Real.exp_add]

theorem gibbsMultiplier_ne_zero (D : GibbsDatum G M B) (g : G) (β : B) :
    gibbsMultiplier D g β ≠ 0 := by
  unfold gibbsMultiplier
  exact Real.exp_ne_zero _

end InfoGeometry.Algebraic.CartanSouriauCocycleGibbsCharacter
