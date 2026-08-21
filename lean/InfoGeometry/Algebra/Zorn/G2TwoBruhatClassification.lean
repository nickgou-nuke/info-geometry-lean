import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import Mathlib.Tactic

namespace InfoGeometry.Algebra.Zorn.G2BruhatClassification

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms

/-- Coxeter length of a Weyl group normal form element w(k, refl) in W(G₂). -/
def coxeterLength (p : ZMod 6 × Bool) : ℕ :=
  match p.1.val, p.2 with
  | 0, false => 0
  | 1, false => 2
  | 2, false => 4
  | 3, false => 6
  | 4, false => 4
  | 5, false => 2
  | 0, true  => 1
  | 1, true  => 3
  | 2, true  => 5
  | 3, true  => 5
  | 4, true  => 3
  | 5, true  => 1
  | _, _     => 0

/-- Lemma 1: The cardinality of the Borel parameter space (Fin 6 → Bool) is exactly 64. -/
theorem borel_param_card_eq_sixty_four :
    Fintype.card (Fin 6 → Bool) = 64 := by
  exact pcWord_parameter_card

/-- Lemma 2: The 12-element Weyl normal form parametrization is strictly injective. -/
theorem weyl_param_injective :
    Function.Injective (fun (p : ZMod 6 × Bool) => weylNF p.1 p.2) := by
  exact weylNF_injective

/-- Lemma 3: The cardinality of the 12-element Weyl group carrier is exactly 12. -/
theorem weyl_param_card_eq_twelve :
    Fintype.card (ZMod 6 × Bool) = 12 := by
  exact weylG2_card_eq_twelve

/-- Lemma 4: Evaluation of 2^(coxeterLength w) summed over the 12 Weyl elements equals 189. -/
theorem weyl_two_power_sum_eq_one_eighty_nine :
    (∑ p : ZMod 6 × Bool, 2 ^ (coxeterLength p)) = 189 := by
  decide

/-- Lemma 5: The capstone Bruhat cardinality product formula:
    64 * ∑ w, 2^(coxeterLength w) = 64 * 189 = 12096. -/
theorem bruhat_cardinality_product :
    64 * (∑ p : ZMod 6 × Bool, 2 ^ (coxeterLength p)) = 12096 := by
  rw [weyl_two_power_sum_eq_one_eighty_nine]

end InfoGeometry.Algebra.Zorn.G2BruhatClassification
