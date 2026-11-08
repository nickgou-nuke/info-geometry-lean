import InfoGeometry.Algebra.Zorn.G2TwoExplicitGenerators
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity
import Mathlib.Tactic

/-!
# Exact order and normal form of the concrete simple-root subgroup

The two certified involutions `unipotentShortAut true` and `unipotentLongAut true`
generate a dihedral subgroup of order exactly 8, isomorphic to D₄.
-/

namespace InfoGeometry.Algebra.Zorn.G2Unipotent

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem simpleRootSubgroup_card_ge_eight :
    8 ≤ Fintype.card simpleRootSubgroup :=
  simpleRootSubgroup_card_lower_bound_eight

theorem simpleRootSubgroup_exact_card :
    Fintype.card simpleRootSubgroup = 8 :=
  simpleRootSubgroup_card_eq_eight

/-- The two concrete involutions invert their product by conjugation: s (s l) s = (s l)⁻¹ -/
theorem simpleRootProduct_conjugate_inverse :
    unipotentShortAut true *
        (unipotentShortAut true * unipotentLongAut true) *
        unipotentShortAut true =
      (unipotentShortAut true * unipotentLongAut true)⁻¹ := by
  calc
    unipotentShortAut true *
          (unipotentShortAut true * unipotentLongAut true) *
          unipotentShortAut true =
        (unipotentShortAut true * unipotentShortAut true) *
          unipotentLongAut true * unipotentShortAut true := by
            group
    _ = unipotentLongAut true * unipotentShortAut true := by
          rw [unipotentShortAut_order true]
          simp only [_root_.one_mul]
    _ = (unipotentShortAut true * unipotentLongAut true)⁻¹ := by
          rw [mul_inv_rev, unipotentShortAut_inv, unipotentLongAut_inv]

/-- Exact Normal Form Representation:
    Every element of simpleRootSubgroup is of the form p^k or s * p^k for k ∈ Fin 4, where p = s * l. -/
theorem simpleRootSubgroup_normal_form (x : simpleRootSubgroup) :
    ∃ k : Fin 4,
      (x : SplitOctF2Aut) =
          (unipotentShortAut true * unipotentLongAut true) ^ k.1 ∨
        (x : SplitOctF2Aut) =
          unipotentShortAut true *
            (unipotentShortAut true * unipotentLongAut true) ^ k.1 := by
  obtain ⟨i, rfl⟩ := eightRootSubgroupWords_surjective x
  fin_cases i
  · refine ⟨0, Or.inl ?_⟩; rfl
  · refine ⟨1, Or.inl ?_⟩; rfl
  · refine ⟨2, Or.inl ?_⟩; rfl
  · refine ⟨3, Or.inl ?_⟩; rfl
  · refine ⟨0, Or.inr ?_⟩; rfl
  · refine ⟨2, Or.inr ?_⟩; rfl
  · refine ⟨3, Or.inr ?_⟩; rfl
  · refine ⟨1, Or.inr ?_⟩
    dsimp [eightRootSubgroupWords]
    have hs : unipotentShortAut true * unipotentShortAut true = 1 := unipotentShortAut_order true
    calc (unipotentLongAut true : SplitOctF2Aut) = 1 * unipotentLongAut true := (_root_.one_mul _).symm
    _ = (unipotentShortAut true * unipotentShortAut true) * unipotentLongAut true := by rw [hs]
    _ = unipotentShortAut true * (unipotentShortAut true * unipotentLongAut true) := by rw [mul_assoc]
    _ = unipotentShortAut true * (unipotentShortAut true * unipotentLongAut true) ^ 1 := by rw [pow_one]

end InfoGeometry.Algebra.Zorn.G2Unipotent
