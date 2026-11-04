/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TKKJordanPairData
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTitsFiveGradedClosurePoset

/-!
# The nilpotent Peirce tower as a five-graded Lie algebra

This bridge packages the concrete Peirce sectors into the reusable TKK
five-grade interface. Additive torsion-freeness is assumed because the
component-to-adjoint-eigenspace identification uses distinct integer weights.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTits

open TKKJordanPairData
open OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset
open OperatorAlgebra.PeirceSpine.YangMillsVortexPoset (P Q)

attribute [local instance 100] LieRing.ofAssociativeRing

variable {B : Type*} [Ring B] [StarRing B]

/-- Finite index corresponding to a TKK grade, ordered as `+2,+1,0,-1,-2`.
The map agrees with `peirceFiveGradeDegree` and `TKKJordanPairData.weight`. -/
def tkkGradeIndex : TKKGrade → Fin 5
  | .m2 => 4
  | .m1 => 3
  | .z0 => 2
  | .p1 => 1
  | .p2 => 0

theorem peirceFiveGradeDegree_tkkGradeIndex (i : TKKGrade) :
    peirceFiveGradeDegree (tkkGradeIndex i) = TKKJordanPairData.weight i := by
  cases i <;> rfl

/-- The five Peirce submodules, indexed by the TKK grades. -/
def tkkPeirceGrade (N_plus : B) (i : TKKGrade) : Submodule ℤ B :=
  peirceFiveGradeSubmodule N_plus (tkkGradeIndex i)

/-- The regular nilpotent generator belongs to the extremal positive Peirce
grade, without any additive-torsion-freeness assumption. -/
theorem N_plus_mem_tkkGrade_p2 (N_plus : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    N_plus ∈ tkkPeirceGrade N_plus .p2 := by
  change N_plus ∈ peirceGradePlus2Subgroup N_plus
  refine ⟨N_plus, ?_⟩
  change P N_plus * N_plus * Q N_plus = N_plus
  have hPN : P N_plus * N_plus = N_plus := by
    dsimp [P]
    exact h_reg
  have hNQ : N_plus * Q N_plus = N_plus := by
    exact YangMillsVortexPoset.N_plus_mul_Q N_plus h_reg
  calc P N_plus * N_plus * Q N_plus
      = N_plus * Q N_plus := by rw [hPN]
    _ = N_plus := hNQ

/-- The adjoint nilpotent generator belongs to the extremal negative Peirce
grade, without any additive-torsion-freeness assumption. -/
theorem star_N_plus_mem_tkkGrade_m2 (N_plus : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus ∈ tkkPeirceGrade N_plus .m2 := by
  change star N_plus ∈ peirceGradeMinus2Subgroup N_plus
  refine ⟨star N_plus, ?_⟩
  change Q N_plus * star N_plus * P N_plus = star N_plus
  have hQstar : Q N_plus * star N_plus = star N_plus := by
    exact YangMillsVortexPoset.Q_mul_star_N_plus N_plus h_reg
  have hstarP : star N_plus * P N_plus = star N_plus := by
    exact YangMillsVortexPoset.star_N_plus_mul_P N_plus h_reg
  calc Q N_plus * star N_plus * P N_plus
      = star N_plus * P N_plus := by
        rw [hQstar]
    _ = star N_plus := hstarP

/-- Package the nilpotent Peirce sectors as a concrete five-graded Lie algebra.
The hypotheses on the nilpotent generate the Peirce decomposition; torsion
freeness ensures the integer adjoint grades identify those components. -/
noncomputable def nilpotentPairFiveGradedLieAlgebra
    (N_plus : B) (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus)
    [IsAddTorsionFree B] : FiveGradedLieAlgebra ℤ where
  L := B
  grade := tkkPeirceGrade N_plus
  bracket_mem_some := by
    intro i j k hijk x y hx hy
    have hdegree : peirceFiveGradeDegree (tkkGradeIndex i) +
        peirceFiveGradeDegree (tkkGradeIndex j) =
        peirceFiveGradeDegree (tkkGradeIndex k) := by
      cases i <;> cases j <;> cases k <;>
        simp_all [TKKJordanPairData.gradeAdd, TKKJordanPairData.ofWeight,
          TKKJordanPairData.weight, tkkGradeIndex, peirceFiveGradeDegree]
    have hbracket := peirceFiveGrade_bracket_mem_peirce N_plus h_nil h_reg
      (tkkGradeIndex i) (tkkGradeIndex j) (tkkGradeIndex k) x y hx hy hdegree
    simpa [tkkPeirceGrade, comm, LieRing.of_associative_ring_bracket] using hbracket
  bracket_eq_zero_none := by
    intro i j hij x y hx hy
    let d : ℤ := peirceFiveGradeDegree (tkkGradeIndex i) +
      peirceFiveGradeDegree (tkkGradeIndex j)
    have hd2 : d ≠ 2 := by
      cases i <;> cases j <;>
        simp [d, tkkGradeIndex, peirceFiveGradeDegree,
          TKKJordanPairData.gradeAdd, TKKJordanPairData.ofWeight,
          TKKJordanPairData.weight] at hij ⊢
    have hd1 : d ≠ 1 := by
      cases i <;> cases j <;>
        simp [d, tkkGradeIndex, peirceFiveGradeDegree,
          TKKJordanPairData.gradeAdd, TKKJordanPairData.ofWeight,
          TKKJordanPairData.weight] at hij ⊢
    have hd0 : d ≠ 0 := by
      cases i <;> cases j <;>
        simp [d, tkkGradeIndex, peirceFiveGradeDegree,
          TKKJordanPairData.gradeAdd, TKKJordanPairData.ofWeight,
          TKKJordanPairData.weight] at hij ⊢
    have hdm1 : d ≠ -1 := by
      cases i <;> cases j <;>
        simp [d, tkkGradeIndex, peirceFiveGradeDegree,
          TKKJordanPairData.gradeAdd, TKKJordanPairData.ofWeight,
          TKKJordanPairData.weight] at hij ⊢
    have hdm2 : d ≠ -2 := by
      cases i <;> cases j <;>
        simp [d, tkkGradeIndex, peirceFiveGradeDegree,
          TKKJordanPairData.gradeAdd, TKKJordanPairData.ofWeight,
          TKKJordanPairData.weight] at hij ⊢
    have hbracket := peirceFiveGrade_bracket_eq_zero_of_degree_sum_outside
      N_plus h_nil h_reg (tkkGradeIndex i) (tkkGradeIndex j) x y d hx hy rfl
      hd2 hd1 hd0 hdm1 hdm2
    simpa [comm, LieRing.of_associative_ring_bracket] using hbracket

end InfoGeometry.OperatorAlgebra.PeirceSpine.KantorKoecherTits
