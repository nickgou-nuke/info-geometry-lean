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

/-- Every positive Jordan-associator KKT generator belongs to the concrete
positive extremal Peirce grade, independently of additive torsion-freeness. -/
theorem K_plus2_mem_tkkGrade_p2 (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    K_plus2 N_plus X ∈ tkkPeirceGrade N_plus .p2 := by
  have hPN : P N_plus * N_plus = N_plus :=
    YangMillsVortexPoset.P_mul_N_plus N_plus h_reg
  have hNQ : N_plus * Q N_plus = N_plus :=
    YangMillsVortexPoset.N_plus_mul_Q N_plus h_reg
  have hG : G_plus2 N_plus X ∈ peirceGradePlus2Subgroup N_plus := by
    change G_plus2 N_plus X ∈ Set.range (peirceGradePlus2 N_plus)
    refine ⟨N_plus * X * N_plus, ?_⟩
    change P N_plus * (N_plus * X * N_plus) * Q N_plus = N_plus * X * N_plus
    calc P N_plus * (N_plus * X * N_plus) * Q N_plus
        = (P N_plus * N_plus) * X * (N_plus * Q N_plus) := by noncomm_ring
      _ = N_plus * X * N_plus := by rw [hPN, hNQ]
  change K_plus2 N_plus X ∈ peirceGradePlus2Subgroup N_plus
  rw [K_plus2_eq_two_sandwich N_plus X h_nil]
  exact (peirceGradePlus2Subgroup N_plus).nsmul_mem hG 2

/-- Every negative Jordan-associator KKT generator belongs to the concrete
negative extremal Peirce grade, independently of additive torsion-freeness. -/
theorem K_minus2_mem_tkkGrade_m2 (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    K_minus2 N_plus X ∈ tkkPeirceGrade N_plus .m2 := by
  have hQstar : Q N_plus * star N_plus = star N_plus :=
    YangMillsVortexPoset.Q_mul_star_N_plus N_plus h_reg
  have hstarP : star N_plus * P N_plus = star N_plus :=
    YangMillsVortexPoset.star_N_plus_mul_P N_plus h_reg
  have hG : G_minus2 N_plus X ∈ peirceGradeMinus2Subgroup N_plus := by
    change G_minus2 N_plus X ∈ Set.range (peirceGradeMinus2 N_plus)
    refine ⟨star N_plus * X * star N_plus, ?_⟩
    change Q N_plus * (star N_plus * X * star N_plus) * P N_plus =
      star N_plus * X * star N_plus
    calc Q N_plus * (star N_plus * X * star N_plus) * P N_plus
        = (Q N_plus * star N_plus) * X * (star N_plus * P N_plus) := by noncomm_ring
      _ = star N_plus * X * star N_plus := by rw [hQstar, hstarP]
  change K_minus2 N_plus X ∈ peirceGradeMinus2Subgroup N_plus
  rw [K_minus2_eq_two_sandwich N_plus X h_nil]
  exact (peirceGradeMinus2Subgroup N_plus).nsmul_mem hG 2

/-- The closure owner's positive Jordan-associator generator is homogeneous
of adjoint degree `+2`, without additive torsion-freeness. -/
theorem closure_K_plus2_mem_adjoint_grade (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset.K_plus2 N_plus X ∈
      OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset.KKTAdjointGradeSubmodule
        N_plus 2 := by
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Sigma N_plus)
      (OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset.K_plus2 N_plus X) =
      (2 : ℤ) •
        OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset.K_plus2 N_plus X
  simpa [two_nsmul] using
    (OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset.comm_Sigma_K_plus2
      N_plus X h_nil h_reg)

/-- The closure owner's negative Jordan-associator generator is homogeneous
of adjoint degree `-2`, without additive torsion-freeness. -/
theorem closure_K_minus2_mem_adjoint_grade (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset.K_minus2 N_plus X ∈
      OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset.KKTAdjointGradeSubmodule
        N_plus (-2) := by
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Sigma N_plus)
      (OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset.K_minus2 N_plus X) =
      (-2 : ℤ) •
        OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset.K_minus2 N_plus X
  simpa [two_nsmul] using
    (OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset.comm_Sigma_K_minus2
      N_plus X h_nil h_reg)

/-- Direct Peirce-corner closure of the `(+1,+1)` bracket, without passing
through adjoint eigenvalues or assuming additive torsion-freeness. -/
theorem peirce_p1_bracket_mem_p2 (N_plus x y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus)
    (hx : x ∈ tkkPeirceGrade N_plus .p1)
    (hy : y ∈ tkkPeirceGrade N_plus .p1) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y ∈
      tkkPeirceGrade N_plus .p2 := by
  change x ∈ peirceGradePlus1Subgroup N_plus at hx
  change y ∈ peirceGradePlus1Subgroup N_plus at hy
  rcases hx with ⟨X, rfl⟩
  rcases hy with ⟨Y, rfl⟩
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (peirceGradePlus1 N_plus X) (peirceGradePlus1 N_plus Y) ∈
        peirceGradePlus2Subgroup N_plus
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (peirceGradePlus1 N_plus X) (peirceGradePlus1 N_plus Y) ∈
        Set.range (peirceGradePlus2 N_plus)
  refine ⟨X * peirceR N_plus * Y - Y * peirceR N_plus * X, ?_⟩
  exact (comm_peirceGradePlus1_self_closed N_plus X Y h_nil h_reg).symm

/-- Direct Peirce-corner closure of the `(-1,-1)` bracket into grade `-2`,
without additive torsion-freeness. -/
theorem peirce_m1_bracket_mem_m2 (N_plus x y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus)
    (hx : x ∈ tkkPeirceGrade N_plus .m1)
    (hy : y ∈ tkkPeirceGrade N_plus .m1) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y ∈
      tkkPeirceGrade N_plus .m2 := by
  change x ∈ peirceGradeMinus1Subgroup N_plus at hx
  change y ∈ peirceGradeMinus1Subgroup N_plus at hy
  rcases hx with ⟨X, rfl⟩
  rcases hy with ⟨Y, rfl⟩
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (peirceGradeMinus1 N_plus X) (peirceGradeMinus1 N_plus Y) ∈
        peirceGradeMinus2Subgroup N_plus
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (peirceGradeMinus1 N_plus X) (peirceGradeMinus1 N_plus Y) ∈
        Set.range (peirceGradeMinus2 N_plus)
  refine ⟨X * peirceR N_plus * Y - Y * peirceR N_plus * X, ?_⟩
  exact (comm_peirceGradeMinus1_self_closed N_plus X Y h_nil h_reg).symm

/-- The out-of-range `(+2,+1)` bracket vanishes by orthogonality of its
Peirce corners, with no additive torsion assumption. -/
theorem peirce_p2_p1_bracket_eq_zero (N_plus x y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus)
    (hx : x ∈ tkkPeirceGrade N_plus .p2)
    (hy : y ∈ tkkPeirceGrade N_plus .p1) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y = 0 := by
  change x ∈ peirceGradePlus2Subgroup N_plus at hx
  change y ∈ peirceGradePlus1Subgroup N_plus at hy
  rcases hx with ⟨X, rfl⟩
  rcases hy with ⟨Y, rfl⟩
  exact comm_peirceGradePlus2_plus1 N_plus X Y h_nil h_reg

/-- The out-of-range `(-2,-1)` bracket vanishes by orthogonality of its
Peirce corners, with no additive torsion assumption. -/
theorem peirce_m2_m1_bracket_eq_zero (N_plus x y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus)
    (hx : x ∈ tkkPeirceGrade N_plus .m2)
    (hy : y ∈ tkkPeirceGrade N_plus .m1) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y = 0 := by
  change x ∈ peirceGradeMinus2Subgroup N_plus at hx
  change y ∈ peirceGradeMinus1Subgroup N_plus at hy
  rcases hx with ⟨X, rfl⟩
  rcases hy with ⟨Y, rfl⟩
  exact comm_peirceGradeMinus2_minus1 N_plus X Y h_nil h_reg

/-- The extremal positive Peirce grade is abelian, so its bracket lies
outside the five-grade window and vanishes without torsion assumptions. -/
theorem peirce_p2_bracket_eq_zero (N_plus x y : B)
    (h_nil : N_plus * N_plus = 0)
    (hx : x ∈ tkkPeirceGrade N_plus .p2)
    (hy : y ∈ tkkPeirceGrade N_plus .p2) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y = 0 := by
  change x ∈ peirceGradePlus2Subgroup N_plus at hx
  change y ∈ peirceGradePlus2Subgroup N_plus at hy
  rcases hx with ⟨X, rfl⟩
  rcases hy with ⟨Y, rfl⟩
  exact comm_peirceGradePlus2_self N_plus X Y h_nil

/-- The extremal negative Peirce grade is abelian, so its bracket lies
outside the five-grade window and vanishes without torsion assumptions. -/
theorem peirce_m2_bracket_eq_zero (N_plus x y : B)
    (h_nil : N_plus * N_plus = 0)
    (hx : x ∈ tkkPeirceGrade N_plus .m2)
    (hy : y ∈ tkkPeirceGrade N_plus .m2) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y = 0 := by
  change x ∈ peirceGradeMinus2Subgroup N_plus at hx
  change y ∈ peirceGradeMinus2Subgroup N_plus at hy
  rcases hx with ⟨X, rfl⟩
  rcases hy with ⟨Y, rfl⟩
  exact comm_peirceGradeMinus2_self N_plus X Y h_nil

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
