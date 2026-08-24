import InfoGeometry.Algebra.Zorn.G2TwoOppositeUnipotent
import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

/-!
# Residual subgroups for the finite `G₂(2)` Bruhat cells

The residual factor in `B n_w U_w` is not, in general, a Weyl-group
element.  This file records the convention used by the native carrier:

`U_w = U ∩ (w₀ w)⁻¹ U (w₀ w)`.

Only the subgroup and membership layer is defined here.  Cardinality and
root-indexed word parametrizations require a separate root-subgroup owner.
-/

namespace InfoGeometry.Algebra.Zorn.G2BruhatResidual

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoOppositeUnipotent
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

/-- Conjugation by `a⁻¹` on the left and `a` on the right. -/
def conjugationHom (a : SplitOctF2Aut) : SplitOctF2Aut →* SplitOctF2Aut where
  toFun x := a⁻¹ * x * a
  map_one' := by simp
  map_mul' x y := by
    simp [mul_assoc]

/-- The residual subgroup attached to a Weyl parameter. -/
def residualSubgroup (p : WeylG2) : Subgroup SplitOctF2Aut :=
  unipotentSubgroup ⊓
    unipotentSubgroup.comap (conjugationHom (w0 * weylNF p.1 p.2))

/-! The longest Weyl parameter is the concrete half-turn `w₀`.  At this
parameter the conjugating element in the chosen convention is the identity,
so the residual subgroup is exactly the positive unipotent subgroup. -/

theorem residualSubgroup_top_parameter :
    residualSubgroup (3, false) = unipotentSubgroup := by
  rw [residualSubgroup]
  have hw : w0 * weylNF (3 : ZMod 6) false = 1 := by
    calc
      w0 * weylNF (3 : ZMod 6) false = w0 * w0 := by
        rw [weylNF_three_false, ← c_pow_three_eq_swapCartan]
        rfl
      _ = 1 := w0_sq
  rw [hw]
  ext x
  simp [conjugationHom]

theorem residualSubgroup_top_parameter_card :
    Nat.card (residualSubgroup (3, false)) = 64 := by
  rw [residualSubgroup_top_parameter]
  exact unipotentSubgroup_card

theorem mem_residualSubgroup_top_parameter_iff (x : SplitOctF2Aut) :
    x ∈ residualSubgroup (3, false) ↔ x ∈ unipotentSubgroup := by
  rw [residualSubgroup_top_parameter]

end InfoGeometry.Algebra.Zorn.G2BruhatResidual
