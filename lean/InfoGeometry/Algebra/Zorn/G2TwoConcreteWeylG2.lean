import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylGroup
import InfoGeometry.Algebra.Zorn.G2CyclotomicWeylBridge
import Mathlib.Tactic

namespace InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl
open InfoGeometry.Algebra.Zorn.G2Unipotent

/-- The Coxeter element c of order 6 in SplitOctF2Aut. -/
noncomputable def c : SplitOctF2Aut := swapCartanAut * cycle012Aut

/-- The simple reflection s of order 2 in SplitOctF2Aut. -/
noncomputable def s : SplitOctF2Aut := swap01Aut

/-- The second simple reflection t of order 2 in SplitOctF2Aut. -/
noncomputable def t : SplitOctF2Aut := s * c

theorem s_sq : s * s = 1 := by
  exact swap01Aut_sq

theorem c_pow_six : c ^ 6 = 1 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> rfl

theorem s_c_s : s * c * s = c⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> rfl

theorem t_sq : t * t = 1 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> rfl

theorem st_order_six : (s * t) ^ 6 = 1 := by
  have hst : s * t = c := by
    dsimp [t]
    calc
      s * (s * c) = (s * s) * c := by simp [mul_assoc]
      _ = 1 * c := by rw [s_sq]
      _ = c := by simp
  rw [hst]
  exact c_pow_six

/-- The explicit 12 Weyl normal form elements indexed by ZMod 6 × Bool. -/
noncomputable def weylNF (k : ZMod 6) (refl : Bool) : SplitOctF2Aut :=
  if refl then s * c ^ k.val else c ^ k.val

/-- All 12 Weyl normal form elements are strictly distinct. -/
theorem weylNF_injective :
    Function.Injective (fun (p : ZMod 6 × Bool) => weylNF p.1 p.2) := by
  intro ⟨k1, b1⟩ ⟨k2, b2⟩ h
  fin_cases k1 <;> fin_cases k2 <;> cases b1 <;> cases b2
  all_goals try rfl
  all_goals
    have h_eval := congrArg (fun f : SplitOctF2Aut => (f.1 (basis8 0), f.1 (basis8 2), f.1 (basis8 3), f.1 (basis8 4))) h
    revert h_eval
    decide

/-- The 12-element Weyl group W(G₂) as a concrete subtype of SplitOctF2Aut. -/
def weylG2Subgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure {s, t}

theorem weylG2_card_eq_twelve : Fintype.card (ZMod 6 × Bool) = 12 := by
  decide

end InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
