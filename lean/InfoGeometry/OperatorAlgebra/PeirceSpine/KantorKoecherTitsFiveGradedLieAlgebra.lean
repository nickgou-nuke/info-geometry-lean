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

omit [StarRing B] in
private theorem corner_sandwich_outer (e f x : B) :
    e * (f * x * f) * e = (e * f) * x * (f * e) := by
  noncomm_ring

omit [StarRing B] in
private theorem comm_sandwich_corner (e x y : B)
    (hee : e * e = e) :
    (e * x * e) * (e * y * e) - (e * y * e) * (e * x * e) =
      e * (x * e * y - y * e * x) * e := by
  calc (e * x * e) * (e * y * e) - (e * y * e) * (e * x * e)
      = (e * x * (e * e) * y * e) - (e * y * (e * e) * x * e) := by
          noncomm_ring
    _ = e * (x * e * y - y * e * x) * e := by rw [hee]; noncomm_ring

/-- The positive-sheet diagonal corner belongs to the grade-zero range. -/
theorem peirceGradeZero_P_corner_mem (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    G_0_P N_plus X ∈ peirceGradeZeroSubgroup N_plus := by
  change G_0_P N_plus X ∈ Set.range (peirceGradeZero N_plus)
  refine ⟨G_0_P N_plus X, ?_⟩
  have hP2 : P N_plus * P N_plus = P N_plus :=
    YangMillsVortexPoset.P_idem N_plus h_reg
  have hQ2 : Q N_plus * Q N_plus = Q N_plus :=
    YangMillsVortexPoset.Q_idem N_plus h_reg
  have hPQ : P N_plus * Q N_plus = 0 :=
    YangMillsVortexPoset.P_mul_Q N_plus h_nil
  have hQP : Q N_plus * P N_plus = 0 :=
    YangMillsVortexPoset.Q_mul_P N_plus h_nil
  have hPR := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).1
  have hRP := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).2.1
  change P N_plus * (P N_plus * X * P N_plus) * P N_plus +
      Q N_plus * (P N_plus * X * P N_plus) * Q N_plus +
      peirceR N_plus * (P N_plus * X * P N_plus) * peirceR N_plus =
    P N_plus * X * P N_plus
  rw [corner_sandwich_outer, corner_sandwich_outer, corner_sandwich_outer]
  simp [hP2, hQP, hPQ, hRP, hPR]

/-- The negative-sheet diagonal corner belongs to the grade-zero range. -/
theorem peirceGradeZero_Q_corner_mem (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    G_0_Q N_plus X ∈ peirceGradeZeroSubgroup N_plus := by
  change G_0_Q N_plus X ∈ Set.range (peirceGradeZero N_plus)
  refine ⟨G_0_Q N_plus X, ?_⟩
  have hP2 : P N_plus * P N_plus = P N_plus :=
    YangMillsVortexPoset.P_idem N_plus h_reg
  have hQ2 : Q N_plus * Q N_plus = Q N_plus :=
    YangMillsVortexPoset.Q_idem N_plus h_reg
  have hPQ : P N_plus * Q N_plus = 0 :=
    YangMillsVortexPoset.P_mul_Q N_plus h_nil
  have hQP : Q N_plus * P N_plus = 0 :=
    YangMillsVortexPoset.Q_mul_P N_plus h_nil
  have hQR := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).2.2.1
  have hRQ := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).2.2.2
  change P N_plus * (Q N_plus * X * Q N_plus) * P N_plus +
      Q N_plus * (Q N_plus * X * Q N_plus) * Q N_plus +
      peirceR N_plus * (Q N_plus * X * Q N_plus) * peirceR N_plus =
    Q N_plus * X * Q N_plus
  rw [corner_sandwich_outer, corner_sandwich_outer, corner_sandwich_outer]
  simp [hQ2, hPQ, hQP, hQR, hRQ]

/-- The neutral exterior diagonal corner belongs to the grade-zero range. -/
theorem peirceGradeZero_R_corner_mem (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    G_0_neutral N_plus X ∈ peirceGradeZeroSubgroup N_plus := by
  change G_0_neutral N_plus X ∈ Set.range (peirceGradeZero N_plus)
  refine ⟨G_0_neutral N_plus X, ?_⟩
  have hP2 : P N_plus * P N_plus = P N_plus :=
    YangMillsVortexPoset.P_idem N_plus h_reg
  have hQ2 : Q N_plus * Q N_plus = Q N_plus :=
    YangMillsVortexPoset.Q_idem N_plus h_reg
  have hPQ : P N_plus * Q N_plus = 0 :=
    YangMillsVortexPoset.P_mul_Q N_plus h_nil
  have hQP : Q N_plus * P N_plus = 0 :=
    YangMillsVortexPoset.Q_mul_P N_plus h_nil
  have hPR := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).1
  have hRP := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).2.1
  have hQR := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).2.2.1
  have hRQ := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).2.2.2
  have hR2 : peirceR N_plus * peirceR N_plus = peirceR N_plus := by
    have hGap2 := OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap_idem
      N_plus h_nil h_reg
    dsimp [peirceR]
    rw [mul_sub, mul_one, sub_mul, one_mul, hGap2, sub_self, sub_zero]
  change P N_plus * (peirceR N_plus * X * peirceR N_plus) * P N_plus +
      Q N_plus * (peirceR N_plus * X * peirceR N_plus) * Q N_plus +
      peirceR N_plus * (peirceR N_plus * X * peirceR N_plus) * peirceR N_plus =
    peirceR N_plus * X * peirceR N_plus
  rw [corner_sandwich_outer, corner_sandwich_outer, corner_sandwich_outer]
  simp [hR2, hPR, hRP, hQR, hRQ]

/-- The left generator of grade `+1` lies in its Peirce range. -/
theorem peirceGradePlus1_L_corner_mem (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    G_plus1_L N_plus X ∈ peirceGradePlus1Subgroup N_plus := by
  change G_plus1_L N_plus X ∈ Set.range (peirceGradePlus1 N_plus)
  refine ⟨G_plus1_L N_plus X, ?_⟩
  have hPN : P N_plus * N_plus = N_plus :=
    YangMillsVortexPoset.P_mul_N_plus N_plus h_reg
  have hPR := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).1
  have hRQ := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).2.2.2
  have hRN : peirceR N_plus * N_plus = 0 := by
    dsimp [peirceR]
    rw [sub_mul, one_mul,
      OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap_mul_N_plus
        N_plus h_nil h_reg,
      sub_self]
  have hR2 : peirceR N_plus * peirceR N_plus = peirceR N_plus := by
    have hGap2 := OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap_idem
      N_plus h_nil h_reg
    dsimp [peirceR]
    rw [mul_sub, mul_one, sub_mul, one_mul, hGap2, sub_self, sub_zero]
  dsimp [G_plus1_L, peirceGradePlus1, peircePR, peirceRQ]
  change P N_plus * (N_plus * X * peirceR N_plus) * peirceR N_plus +
      peirceR N_plus * (N_plus * X * peirceR N_plus) * Q N_plus =
    N_plus * X * peirceR N_plus
  have h1 : P N_plus * (N_plus * X * peirceR N_plus) * peirceR N_plus =
      N_plus * X * peirceR N_plus := by
    calc P N_plus * (N_plus * X * peirceR N_plus) * peirceR N_plus
        = (P N_plus * N_plus) * X * (peirceR N_plus * peirceR N_plus) := by noncomm_ring
      _ = N_plus * X * peirceR N_plus := by rw [hPN, hR2]
  have h2 : peirceR N_plus * (N_plus * X * peirceR N_plus) * Q N_plus = 0 := by
    calc peirceR N_plus * (N_plus * X * peirceR N_plus) * Q N_plus
        = (peirceR N_plus * N_plus) * X * (peirceR N_plus * Q N_plus) := by noncomm_ring
      _ = 0 := by rw [hRN, hRQ, zero_mul, mul_zero]
  rw [h1, h2, add_zero]

/-- The right generator of grade `+1` lies in its Peirce range. -/
theorem peirceGradePlus1_R_corner_mem (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    G_plus1_R N_plus X ∈ peirceGradePlus1Subgroup N_plus := by
  change G_plus1_R N_plus X ∈ Set.range (peirceGradePlus1 N_plus)
  refine ⟨G_plus1_R N_plus X, ?_⟩
  have hNQ : N_plus * Q N_plus = N_plus :=
    YangMillsVortexPoset.N_plus_mul_Q N_plus h_reg
  have hPR := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).1
  have hR2 : peirceR N_plus * peirceR N_plus = peirceR N_plus := by
    have hGap2 := OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap_idem
      N_plus h_nil h_reg
    dsimp [peirceR]
    rw [mul_sub, mul_one, sub_mul, one_mul, hGap2, sub_self, sub_zero]
  dsimp [G_plus1_R, peirceGradePlus1, peircePR, peirceRQ]
  change P N_plus * (peirceR N_plus * X * N_plus) * peirceR N_plus +
      peirceR N_plus * (peirceR N_plus * X * N_plus) * Q N_plus =
    peirceR N_plus * X * N_plus
  have h1 : P N_plus * (peirceR N_plus * X * N_plus) * peirceR N_plus = 0 := by
    calc P N_plus * (peirceR N_plus * X * N_plus) * peirceR N_plus
        = (P N_plus * peirceR N_plus) * X * (N_plus * peirceR N_plus) := by noncomm_ring
      _ = 0 := by rw [hPR]; simp
  have h2 : peirceR N_plus * (peirceR N_plus * X * N_plus) * Q N_plus =
      peirceR N_plus * X * N_plus := by
    calc peirceR N_plus * (peirceR N_plus * X * N_plus) * Q N_plus
        = (peirceR N_plus * peirceR N_plus) * X * (N_plus * Q N_plus) := by noncomm_ring
      _ = peirceR N_plus * X * N_plus := by rw [hR2, hNQ]
  rw [h1, h2, zero_add]

/-- Direct grade-zero self-bracket closure from its three diagonal corners. -/
theorem peirce_z0_bracket_mem_z0 (N_plus x y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus)
    (hx : x ∈ tkkPeirceGrade N_plus .z0)
    (hy : y ∈ tkkPeirceGrade N_plus .z0) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y ∈
      tkkPeirceGrade N_plus .z0 := by
  change x ∈ peirceGradeZeroSubgroup N_plus at hx
  change y ∈ peirceGradeZeroSubgroup N_plus at hy
  rcases hx with ⟨X, rfl⟩
  rcases hy with ⟨Y, rfl⟩
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (peirceGradeZero N_plus X) (peirceGradeZero N_plus Y) ∈
        peirceGradeZeroSubgroup N_plus
  rw [comm_peirceGradeZero_closed N_plus X Y h_nil h_reg]
  have hP2 : P N_plus * P N_plus = P N_plus :=
    YangMillsVortexPoset.P_idem N_plus h_reg
  have hQ2 : Q N_plus * Q N_plus = Q N_plus :=
    YangMillsVortexPoset.Q_idem N_plus h_reg
  have hR2 : peirceR N_plus * peirceR N_plus = peirceR N_plus := by
    have hGap2 := OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap_idem
      N_plus h_nil h_reg
    dsimp [peirceR]
    rw [mul_sub, mul_one, sub_mul, one_mul, hGap2, sub_self, sub_zero]
  have hP : comm (G_0_P N_plus X) (G_0_P N_plus Y) =
      G_0_P N_plus (X * P N_plus * Y - Y * P N_plus * X) := by
    dsimp [comm, G_0_P]
    exact comm_sandwich_corner (P N_plus) X Y hP2
  have hQ : comm (G_0_Q N_plus X) (G_0_Q N_plus Y) =
      G_0_Q N_plus (X * Q N_plus * Y - Y * Q N_plus * X) := by
    dsimp [comm, G_0_Q]
    exact comm_sandwich_corner (Q N_plus) X Y hQ2
  have hR : comm (G_0_neutral N_plus X) (G_0_neutral N_plus Y) =
      G_0_neutral N_plus (X * peirceR N_plus * Y -
        Y * peirceR N_plus * X) := by
    dsimp [comm, G_0_neutral]
    exact comm_sandwich_corner (peirceR N_plus) X Y hR2
  rw [hP, hQ, hR]
  exact (peirceGradeZeroSubgroup N_plus).add_mem
    ((peirceGradeZeroSubgroup N_plus).add_mem
      (peirceGradeZero_P_corner_mem N_plus _ h_nil h_reg)
      (peirceGradeZero_Q_corner_mem N_plus _ h_nil h_reg))
    (peirceGradeZero_R_corner_mem N_plus _ h_nil h_reg)

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

/-- The mixed `(+2,-1)` bracket lands in grade `+1` by direct Peirce-corner
composition, without additive torsion-freeness. -/
theorem peirce_p2_m1_bracket_mem_p1 (N_plus x y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus)
    (hx : x ∈ tkkPeirceGrade N_plus .p2)
    (hy : y ∈ tkkPeirceGrade N_plus .m1) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y ∈
      tkkPeirceGrade N_plus .p1 := by
  change x ∈ peirceGradePlus2Subgroup N_plus at hx
  change y ∈ peirceGradeMinus1Subgroup N_plus at hy
  rcases hx with ⟨X, rfl⟩
  rcases hy with ⟨Y, rfl⟩
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (peirceGradePlus2 N_plus X) (peirceGradeMinus1 N_plus Y) ∈
        peirceGradePlus1Subgroup N_plus
  exact comm_peirceGradePlus2_minus1_mem N_plus X Y h_nil h_reg

/-- The mixed `(+1,-2)` bracket lands in grade `-1` by direct Peirce-corner
composition, without additive torsion-freeness. -/
theorem peirce_p1_m2_bracket_mem_m1 (N_plus x y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus)
    (hx : x ∈ tkkPeirceGrade N_plus .p1)
    (hy : y ∈ tkkPeirceGrade N_plus .m2) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y ∈
      tkkPeirceGrade N_plus .m1 := by
  change x ∈ peirceGradePlus1Subgroup N_plus at hx
  change y ∈ peirceGradeMinus2Subgroup N_plus at hy
  rcases hx with ⟨X, rfl⟩
  rcases hy with ⟨Y, rfl⟩
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (peirceGradePlus1 N_plus X) (peirceGradeMinus2 N_plus Y) ∈
        peirceGradeMinus1Subgroup N_plus
  exact comm_peirceGradePlus1_minus2_mem N_plus X Y h_nil h_reg

/-- The mixed `(-2,+1)` bracket lands in grade `-1` by direct Peirce-corner
composition, without additive torsion-freeness. -/
theorem peirce_m2_p1_bracket_mem_m1 (N_plus x y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus)
    (hx : x ∈ tkkPeirceGrade N_plus .m2)
    (hy : y ∈ tkkPeirceGrade N_plus .p1) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y ∈
      tkkPeirceGrade N_plus .m1 := by
  change x ∈ peirceGradeMinus2Subgroup N_plus at hx
  change y ∈ peirceGradePlus1Subgroup N_plus at hy
  rcases hx with ⟨X, rfl⟩
  rcases hy with ⟨Y, rfl⟩
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (peirceGradeMinus2 N_plus X) (peirceGradePlus1 N_plus Y) ∈
        peirceGradeMinus1Subgroup N_plus
  rw [comm_peirceGradeMinus2_plus1_closed N_plus X Y h_nil h_reg]
  exact ⟨X * P N_plus * Y * peirceR N_plus -
    Y * Q N_plus * X * P N_plus, rfl⟩

/-- The mixed `(+2,0)` bracket stays in grade `+2` by Peirce-corner
composition, without additive torsion-freeness. -/
theorem peirce_p2_z0_bracket_mem_p2 (N_plus x y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus)
    (hx : x ∈ tkkPeirceGrade N_plus .p2)
    (hy : y ∈ tkkPeirceGrade N_plus .z0) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y ∈
      tkkPeirceGrade N_plus .p2 := by
  change x ∈ peirceGradePlus2Subgroup N_plus at hx
  change y ∈ peirceGradeZeroSubgroup N_plus at hy
  rcases hx with ⟨X, rfl⟩
  rcases hy with ⟨Y, rfl⟩
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (peirceGradePlus2 N_plus X) (peirceGradeZero N_plus Y) ∈
        peirceGradePlus2Subgroup N_plus
  exact comm_peirceGradePlus2_zero_mem N_plus X Y h_nil h_reg

/-- The mixed `(-2,0)` bracket stays in grade `-2` by Peirce-corner
composition, without additive torsion-freeness. -/
theorem peirce_m2_z0_bracket_mem_m2 (N_plus x y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus)
    (hx : x ∈ tkkPeirceGrade N_plus .m2)
    (hy : y ∈ tkkPeirceGrade N_plus .z0) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y ∈
      tkkPeirceGrade N_plus .m2 := by
  change x ∈ peirceGradeMinus2Subgroup N_plus at hx
  change y ∈ peirceGradeZeroSubgroup N_plus at hy
  rcases hx with ⟨X, rfl⟩
  rcases hy with ⟨Y, rfl⟩
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (peirceGradeMinus2 N_plus X) (peirceGradeZero N_plus Y) ∈
        peirceGradeMinus2Subgroup N_plus
  exact comm_peirceGradeMinus2_zero_mem N_plus X Y h_nil h_reg

/-- The mixed `(+1,-1)` bracket belongs to grade zero: its `P`, `Q`, and
neutral Peirce corners are exactly the three terms of the owner's closure
formula. This direct inclusion does not use additive torsion-freeness. -/
theorem peirce_p1_m1_bracket_mem_z0 (N_plus x y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus)
    (hx : x ∈ tkkPeirceGrade N_plus .p1)
    (hy : y ∈ tkkPeirceGrade N_plus .m1) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y ∈
      tkkPeirceGrade N_plus .z0 := by
  change x ∈ peirceGradePlus1Subgroup N_plus at hx
  change y ∈ peirceGradeMinus1Subgroup N_plus at hy
  rcases hx with ⟨X, rfl⟩
  rcases hy with ⟨Y, rfl⟩
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (peirceGradePlus1 N_plus X) (peirceGradeMinus1 N_plus Y) ∈
        peirceGradeZeroSubgroup N_plus
  rw [comm_peirceGradePlus1_minus1_closed N_plus X Y h_nil h_reg]
  change _ ∈ Set.range (peirceGradeZero N_plus)
  let A := X * peirceR N_plus * Y
  let C := Y * peirceR N_plus * X
  let D := X * Q N_plus * Y - Y * P N_plus * X
  let Z := P N_plus * A * P N_plus - Q N_plus * C * Q N_plus +
    peirceR N_plus * D * peirceR N_plus
  refine ⟨Z, ?_⟩
  -- The witness is already a sum of the three mutually orthogonal diagonal corners.
  -- Expanding the Peirce projection therefore returns it unchanged.
  have hP2 : P N_plus * P N_plus = P N_plus :=
    YangMillsVortexPoset.P_idem N_plus h_reg
  have hQ2 : Q N_plus * Q N_plus = Q N_plus :=
    YangMillsVortexPoset.Q_idem N_plus h_reg
  have hPQ : P N_plus * Q N_plus = 0 :=
    YangMillsVortexPoset.P_mul_Q N_plus h_nil
  have hQP : Q N_plus * P N_plus = 0 :=
    YangMillsVortexPoset.Q_mul_P N_plus h_nil
  have hPR := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).1
  have hRP := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).2.1
  have hQR := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).2.2.1
  have hRQ := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).2.2.2
  have hR2 : peirceR N_plus * peirceR N_plus = peirceR N_plus := by
    have hGap2 := OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap_idem
      N_plus h_nil h_reg
    dsimp [peirceR]
    rw [mul_sub, mul_one, sub_mul, one_mul, hGap2, sub_self, sub_zero]
  dsimp [Z, A, C, D, peirceGradeZero, peircePP, peirceQQ, peirceRR]
  simp only [mul_add, add_mul, mul_sub, sub_mul]
  simp only [corner_sandwich_outer, hP2, hQ2, hPQ, hQP, hPR, hRP, hQR, hRQ,
    hR2, zero_mul, mul_zero, zero_add, add_zero, sub_zero, zero_sub]
  dsimp [G_0_P, G_0_Q]
  noncomm_ring

/-- Reversed-order grade-zero closure for the `(-1,+1)` bracket, obtained
from Lie antisymmetry and closure of the grade-zero additive subgroup. -/
theorem peirce_m1_p1_bracket_mem_z0 (N_plus x y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus)
    (hx : x ∈ tkkPeirceGrade N_plus .m1)
    (hy : y ∈ tkkPeirceGrade N_plus .p1) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y ∈
      tkkPeirceGrade N_plus .z0 := by
  change x ∈ peirceGradeMinus1Subgroup N_plus at hx
  change y ∈ peirceGradePlus1Subgroup N_plus at hy
  change InfoGeometry.OperatorAlgebra.PeirceSpine.comm x y ∈
    peirceGradeZeroSubgroup N_plus
  rw [OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset.kkt_comm_antisymm]
  exact (peirceGradeZeroSubgroup N_plus).neg_mem
    (peirce_p1_m1_bracket_mem_z0 N_plus y x h_nil h_reg hy hx)

/-- Opposite extremal Peirce corners bracket directly into the diagonal
grade-zero range, without using adjoint eigenvalue separation. -/
theorem peirce_p2_m2_bracket_mem_z0 (N_plus X Y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (peirceGradePlus2 N_plus X) (peirceGradeMinus2 N_plus Y) ∈
        peirceGradeZeroSubgroup N_plus := by
  change _ ∈ Set.range (peirceGradeZero N_plus)
  refine ⟨X * Q N_plus * Y * P N_plus - Y * P N_plus * X * Q N_plus, ?_⟩
  have hP2 : P N_plus * P N_plus = P N_plus :=
    YangMillsVortexPoset.P_idem N_plus h_reg
  have hQ2 : Q N_plus * Q N_plus = Q N_plus :=
    YangMillsVortexPoset.Q_idem N_plus h_reg
  have hPQ : P N_plus * Q N_plus = 0 :=
    YangMillsVortexPoset.P_mul_Q N_plus h_nil
  have hQP : Q N_plus * P N_plus = 0 :=
    YangMillsVortexPoset.Q_mul_P N_plus h_nil
  have hPR := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).1
  have hRP := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).2.1
  have hQR := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).2.2.1
  have hRQ := (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).2.2.2
  have hR2 : peirceR N_plus * peirceR N_plus = peirceR N_plus := by
    have hGap2 := OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap_idem
      N_plus h_nil h_reg
    dsimp [peirceR]
    rw [mul_sub, mul_one, sub_mul, one_mul, hGap2, sub_self, sub_zero]
  dsimp [peirceGradeZero, peircePP, peirceQQ, peirceRR,
    peirceGradePlus2, peircePQ, peirceGradeMinus2, peirceQP,
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  have h₁ : (P N_plus * X * Q N_plus) * (Q N_plus * Y * P N_plus) =
      P N_plus * X * Q N_plus * Y * P N_plus := by
    calc (P N_plus * X * Q N_plus) * (Q N_plus * Y * P N_plus)
        = P N_plus * X * (Q N_plus * Q N_plus) * Y * P N_plus := by noncomm_ring
      _ = P N_plus * X * Q N_plus * Y * P N_plus := by rw [hQ2]
  have h₂ : (Q N_plus * Y * P N_plus) * (P N_plus * X * Q N_plus) =
      Q N_plus * Y * P N_plus * X * Q N_plus := by
    calc (Q N_plus * Y * P N_plus) * (P N_plus * X * Q N_plus)
        = Q N_plus * Y * (P N_plus * P N_plus) * X * Q N_plus := by noncomm_ring
      _ = Q N_plus * Y * P N_plus * X * Q N_plus := by rw [hP2]
  rw [h₁, h₂]
  noncomm_ring [hP2, hQ2, hPQ, hQP, hPR, hRP, hQR, hRQ, hR2]

/-- Reversing the opposite-extremal bracket preserves grade-zero membership. -/
theorem peirce_m2_p2_bracket_mem_z0 (N_plus X Y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (peirceGradeMinus2 N_plus X) (peirceGradePlus2 N_plus Y) ∈
        peirceGradeZeroSubgroup N_plus := by
  rw [OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset.kkt_comm_antisymm]
  exact (peirceGradeZeroSubgroup N_plus).neg_mem
    (peirce_p2_m2_bracket_mem_z0 N_plus Y X h_nil h_reg)

/-- The grade-zero sector acts on grade `+1` by a bracket that remains in
grade `+1`. The result is assembled from the existing six Peirce corner
bracket identities. -/
theorem peirce_z0_p1_bracket_mem_p1 (N_plus X Y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (peirceGradeZero N_plus X) (peirceGradePlus1 N_plus Y) ∈
        peirceGradePlus1Subgroup N_plus := by
  let T := star N_plus * Y + Y * star N_plus
  have hRstar : peirceR N_plus * star N_plus = 0 := by
    dsimp [peirceR]
    rw [sub_mul, one_mul,
      OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap_mul_star_N_plus
        N_plus h_nil h_reg,
      sub_self]
  have hstarGap : star N_plus *
      OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap N_plus =
        star N_plus := by
    rw [OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap_eq_anticomm
      N_plus h_nil h_reg]
    dsimp [OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.anticomm]
    calc star N_plus * (N_plus * star N_plus + star N_plus * N_plus)
        = (star N_plus * N_plus) * star N_plus +
          (star N_plus * star N_plus) * N_plus := by noncomm_ring
      _ = star N_plus := by
          rw [OperatorAlgebra.PeirceSpine.YangMillsVortexPoset.star_N_plus_reg
                N_plus h_reg,
              OperatorAlgebra.PeirceSpine.YangMillsVortexPoset.star_N_plus_sq
                N_plus h_nil,
              zero_mul, add_zero]
  have hstarR : star N_plus * peirceR N_plus = 0 := by
    dsimp [peirceR]
    rw [mul_sub, mul_one, hstarGap, sub_self]
  have hparam : G_plus1 N_plus T = peirceGradePlus1 N_plus Y := by
    have hleft : N_plus * T * peirceR N_plus =
        P N_plus * Y * peirceR N_plus := by
      change N_plus * (star N_plus * Y + Y * star N_plus) * peirceR N_plus =
        (N_plus * star N_plus) * Y * peirceR N_plus
      calc N_plus * (star N_plus * Y + Y * star N_plus) * peirceR N_plus
          = N_plus * star N_plus * Y * peirceR N_plus +
            N_plus * Y * star N_plus * peirceR N_plus := by noncomm_ring
        _ = N_plus * star N_plus * Y * peirceR N_plus := by
            calc N_plus * star N_plus * Y * peirceR N_plus +
                  N_plus * Y * star N_plus * peirceR N_plus
                = N_plus * star N_plus * Y * peirceR N_plus +
                    (N_plus * Y) * (star N_plus * peirceR N_plus) := by
                      rw [mul_assoc (N_plus * Y) (star N_plus) (peirceR N_plus)]
              _ = N_plus * star N_plus * Y * peirceR N_plus := by
                    rw [hstarR, mul_zero, add_zero]
        _ = (N_plus * star N_plus) * Y * peirceR N_plus := by rfl
    have hright : peirceR N_plus * T * N_plus =
        peirceR N_plus * Y * Q N_plus := by
      change peirceR N_plus * (star N_plus * Y + Y * star N_plus) * N_plus =
        peirceR N_plus * Y * (star N_plus * N_plus)
      calc peirceR N_plus * (star N_plus * Y + Y * star N_plus) * N_plus
          = peirceR N_plus * (star N_plus * (Y * N_plus)) +
            peirceR N_plus * (Y * (star N_plus * N_plus)) := by noncomm_ring
        _ = peirceR N_plus * (Y * (star N_plus * N_plus)) := by
            calc peirceR N_plus * (star N_plus * (Y * N_plus)) +
                  peirceR N_plus * (Y * (star N_plus * N_plus))
                = (peirceR N_plus * star N_plus) * (Y * N_plus) +
                    peirceR N_plus * (Y * (star N_plus * N_plus)) := by
                      rw [← mul_assoc (peirceR N_plus) (star N_plus) (Y * N_plus)]
              _ = peirceR N_plus * (Y * (star N_plus * N_plus)) := by
                    rw [hRstar, zero_mul, zero_add]
        _ = peirceR N_plus * Y * (star N_plus * N_plus) := by
            rw [← mul_assoc]
    change N_plus * T * peirceR N_plus + peirceR N_plus * T * N_plus = _
    rw [hleft, hright]
    rfl
  have hclosure := comm_G_plus1_G_0_closed N_plus T X h_nil h_reg
  have hnormal :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm
          (peirceGradePlus1 N_plus Y) (peirceGradeZero N_plus X) =
        G_plus1_L N_plus
            (T * peirceR N_plus * X - star N_plus * X * N_plus * T) +
          G_plus1_R N_plus
            (T * N_plus * X * star N_plus - X * peirceR N_plus * T) := by
    rw [← hparam]
    simpa [peirceGradeZero, peircePP, peirceQQ, peirceRR,
      peirceR, G_0_P, G_0_Q, G_0_neutral] using hclosure
  have hsum :
      G_plus1_L N_plus
          (T * peirceR N_plus * X - star N_plus * X * N_plus * T) +
        G_plus1_R N_plus
          (T * N_plus * X * star N_plus - X * peirceR N_plus * T) ∈
        peirceGradePlus1Subgroup N_plus := by
    apply (peirceGradePlus1Subgroup N_plus).add_mem
    · exact peirceGradePlus1_L_corner_mem N_plus _ h_nil h_reg
    · exact peirceGradePlus1_R_corner_mem N_plus _ h_nil h_reg
  rw [OperatorAlgebra.PeirceSpine.KantorKoecherTitsClosurePoset.kkt_comm_antisymm,
    hnormal]
  exact (peirceGradePlus1Subgroup N_plus).neg_mem hsum

/-- The Peirce grade `-1` generator indexed by `Y` is the closure owner's
`G_minus1` generator indexed by `N_plus * Y + Y * N_plus`. -/
theorem peirce_m1_eq_G_minus1 (N_plus Y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    peirceGradeMinus1 N_plus Y =
      G_minus1 N_plus (N_plus * Y + Y * N_plus) := by
  let T := N_plus * Y + Y * N_plus
  have hR_N : peirceR N_plus * N_plus = 0 := by
    dsimp [peirceR]
    rw [sub_mul, one_mul,
      OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap_mul_N_plus
        N_plus h_nil h_reg,
      sub_self]
  have hN_R : N_plus * peirceR N_plus = 0 := by
    dsimp [peirceR]
    have hNG : N_plus *
        OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap N_plus =
          N_plus := by
      rw [OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap_eq_anticomm
        N_plus h_nil h_reg]
      dsimp [OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.anticomm]
      rw [mul_add, ← mul_assoc N_plus N_plus (star N_plus), h_nil, zero_mul,
        ← mul_assoc N_plus (star N_plus) N_plus, h_reg, zero_add]
    rw [mul_sub, mul_one, hNG, sub_self]
  have hleft : star N_plus * T * peirceR N_plus =
      Q N_plus * Y * peirceR N_plus := by
    dsimp [T, Q]
    calc star N_plus * (N_plus * Y + Y * N_plus) * peirceR N_plus
        = star N_plus * N_plus * Y * peirceR N_plus +
          star N_plus * Y * N_plus * peirceR N_plus := by noncomm_ring
      _ = star N_plus * N_plus * Y * peirceR N_plus := by
          rw [mul_assoc (star N_plus * Y) N_plus (peirceR N_plus),
            hN_R, mul_zero, add_zero]
  have hright : peirceR N_plus * T * star N_plus =
      peirceR N_plus * Y * P N_plus := by
    dsimp [T, P]
    calc peirceR N_plus * (N_plus * Y + Y * N_plus) * star N_plus
        = peirceR N_plus * N_plus * Y * star N_plus +
          peirceR N_plus * Y * N_plus * star N_plus := by noncomm_ring
      _ = peirceR N_plus * Y * N_plus * star N_plus := by
          rw [mul_assoc (peirceR N_plus * N_plus) Y (star N_plus),
            hR_N, zero_mul, zero_add]
      _ = peirceR N_plus * Y * (N_plus * star N_plus) := by
          rw [mul_assoc (peirceR N_plus * Y) N_plus (star N_plus)]
  dsimp [peirceGradeMinus1, peirceRP, peirceQR,
    G_minus1, G_minus1_L, G_minus1_R]
  dsimp [T] at hleft hright
  change peirceR N_plus * Y * P N_plus + Q N_plus * Y * peirceR N_plus =
    star N_plus * (N_plus * Y + Y * N_plus) * peirceR N_plus +
      peirceR N_plus * (N_plus * Y + Y * N_plus) * star N_plus
  rw [hleft, hright, add_comm]

/-- The closure owner's left grade `-1` corner lies in the concrete Peirce
grade `-1` subgroup. -/
theorem peirceGradeMinus1_L_corner_mem (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    G_minus1_L N_plus X ∈ peirceGradeMinus1Subgroup N_plus := by
  change G_minus1_L N_plus X ∈ Set.range (peirceGradeMinus1 N_plus)
  refine ⟨G_minus1_L N_plus X, ?_⟩
  have hRstar : peirceR N_plus * star N_plus = 0 := by
    dsimp [peirceR]
    rw [sub_mul, one_mul,
      OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap_mul_star_N_plus
        N_plus h_nil h_reg,
      sub_self]
  have hQstar : Q N_plus * star N_plus = star N_plus :=
    YangMillsVortexPoset.Q_mul_star_N_plus N_plus h_reg
  have hR2 : peirceR N_plus * peirceR N_plus = peirceR N_plus := by
    have hGap2 := OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap_idem
      N_plus h_nil h_reg
    dsimp [peirceR]
    rw [mul_sub, mul_one, sub_mul, one_mul, hGap2, sub_self, sub_zero]
  dsimp [G_minus1_L, peirceGradeMinus1, peirceRP, peirceQR]
  change peirceR N_plus * (star N_plus * X * peirceR N_plus) * P N_plus +
      Q N_plus * (star N_plus * X * peirceR N_plus) * peirceR N_plus =
    star N_plus * X * peirceR N_plus
  have hleft : peirceR N_plus * (star N_plus * X * peirceR N_plus) * P N_plus = 0 := by
    calc peirceR N_plus * (star N_plus * X * peirceR N_plus) * P N_plus
        = (peirceR N_plus * star N_plus) * (X * peirceR N_plus * P N_plus) := by
            noncomm_ring
      _ = 0 := by rw [hRstar, zero_mul]
  have hright : Q N_plus * (star N_plus * X * peirceR N_plus) * peirceR N_plus =
      star N_plus * X * peirceR N_plus := by
    calc Q N_plus * (star N_plus * X * peirceR N_plus) * peirceR N_plus
        = (Q N_plus * star N_plus) * X *
          (peirceR N_plus * peirceR N_plus) := by noncomm_ring
      _ = star N_plus * X * peirceR N_plus := by rw [hQstar, hR2]
  rw [hleft, hright, zero_add]

/-- The closure owner's right grade `-1` corner lies in the concrete Peirce
grade `-1` subgroup. -/
theorem peirceGradeMinus1_R_corner_mem (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    G_minus1_R N_plus X ∈ peirceGradeMinus1Subgroup N_plus := by
  change G_minus1_R N_plus X ∈ Set.range (peirceGradeMinus1 N_plus)
  refine ⟨G_minus1_R N_plus X, ?_⟩
  have hQR : Q N_plus * peirceR N_plus = 0 :=
    (peirce_chiral_neutral_orthogonal N_plus h_nil h_reg).2.2.1
  have hstarP : star N_plus * P N_plus = star N_plus :=
    YangMillsVortexPoset.star_N_plus_mul_P N_plus h_reg
  have hR2 : peirceR N_plus * peirceR N_plus = peirceR N_plus := by
    have hGap2 := OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset.Gap_idem
      N_plus h_nil h_reg
    dsimp [peirceR]
    rw [mul_sub, mul_one, sub_mul, one_mul, hGap2, sub_self, sub_zero]
  dsimp [G_minus1_R, peirceGradeMinus1, peirceRP, peirceQR]
  change peirceR N_plus * (peirceR N_plus * X * star N_plus) * P N_plus +
      Q N_plus * (peirceR N_plus * X * star N_plus) * peirceR N_plus =
    peirceR N_plus * X * star N_plus
  have hleft : peirceR N_plus * (peirceR N_plus * X * star N_plus) * P N_plus =
      peirceR N_plus * X * star N_plus := by
    calc peirceR N_plus * (peirceR N_plus * X * star N_plus) * P N_plus
        = (peirceR N_plus * peirceR N_plus) * X * (star N_plus * P N_plus) := by
            noncomm_ring
      _ = peirceR N_plus * X * star N_plus := by rw [hR2, hstarP]
  have hright : Q N_plus * (peirceR N_plus * X * star N_plus) * peirceR N_plus = 0 := by
    calc Q N_plus * (peirceR N_plus * X * star N_plus) * peirceR N_plus
        = (Q N_plus * peirceR N_plus) * (X * star N_plus * peirceR N_plus) := by
            noncomm_ring
      _ = 0 := by rw [hQR, zero_mul]
  rw [hleft, hright, add_zero]

/-- The grade-zero sector acts on grade `-1` by a bracket that remains in
grade `-1`, proved from direct Peirce-corner closure. -/
theorem peirce_z0_m1_bracket_mem_m1 (N_plus X Y : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      (peirceGradeZero N_plus X) (peirceGradeMinus1 N_plus Y) ∈
        peirceGradeMinus1Subgroup N_plus := by
  let T := N_plus * Y + Y * N_plus
  let A := N_plus * X * star N_plus * T - T * peirceR N_plus * X
  let C := X * peirceR N_plus * T - T * star N_plus * X * N_plus
  have hclosure := comm_G_0_G_minus1_closed N_plus X T h_nil h_reg
  have hnormal :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm
          (peirceGradeZero N_plus X) (peirceGradeMinus1 N_plus Y) =
        G_minus1_L N_plus A + G_minus1_R N_plus C := by
    rw [peirce_m1_eq_G_minus1 N_plus Y h_nil h_reg]
    simpa [peirceGradeZero, peircePP, peirceQQ, peirceRR,
      peirceR, G_0_P, G_0_Q, G_0_neutral, A, C] using hclosure
  rw [hnormal]
  apply (peirceGradeMinus1Subgroup N_plus).add_mem
  · exact peirceGradeMinus1_L_corner_mem N_plus A h_nil h_reg
  · exact peirceGradeMinus1_R_corner_mem N_plus C h_nil h_reg

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
