import InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.SplitOctonionQuaternionEllBridge

noncomputable section

namespace InfoGeometry.Clifford.GogberashviliAppendixE

open InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Clifford.SplitOctonionQuaternionEllBridge

abbrev Carrier := ZornCell ℝ

def DnPlusJ (n : Fin 3) : Carrier := (1 / 2 : ℝ) • (oneZ + J n)
def DnMinusJ (n : Fin 3) : Carrier := (1 / 2 : ℝ) • (oneZ + negZ (J n))
def DPlusI : Carrier := (1 / 2 : ℝ) • (oneZ + I)
def DMinusI : Carrier := (1 / 2 : ℝ) • (oneZ + negZ I)

def GnPlusJ (n : Fin 3) : Carrier := (1 / 2 : ℝ) • (J n + j n)
def GnMinusJ (n : Fin 3) : Carrier := (1 / 2 : ℝ) • (J n + negZ (j n))
def GnPlusI (n : Fin 3) : Carrier := (1 / 2 : ℝ) • (I + j n)
def GnMinusI (n : Fin 3) : Carrier := (1 / 2 : ℝ) • (I + negZ (j n))

theorem DnPlusJ_idempotent (n : Fin 3) :
    DnPlusJ n * DnPlusJ n = DnPlusJ n := by
  change D_plus n * D_plus n = D_plus n
  exact D_plus_idempotent n

theorem DnMinusJ_idempotent (n : Fin 3) :
    DnMinusJ n * DnMinusJ n = DnMinusJ n := by
  change D_minus n * D_minus n = D_minus n
  exact D_minus_idempotent n

theorem DnPlusJ_mul_DnMinusJ (n : Fin 3) :
    DnPlusJ n * DnMinusJ n = 0 := by
  change D_plus n * D_minus n = 0
  exact D_plus_mul_D_minus n

theorem DnMinusJ_mul_DnPlusJ (n : Fin 3) :
    DnMinusJ n * DnPlusJ n = 0 := by
  fin_cases n <;>
    change ZornCell.mulZ _ _ = 0
  all_goals
    unfold DnMinusJ DnPlusJ
    apply zorn_ext <;>
      dsimp only [zero_val, GogberashviliSplitOctonionBasis.addZ_val,
        GogberashviliSplitOctonionBasis.smulZ_val, ZornCell.mulZ,
        negZ, GogberashviliSplitOctonionBasis.smulZ,
        GogberashviliSplitOctonionBasis.addZ,
        GogberashviliSplitOctonionBasis.zeroZ, oneZ, J, j] <;> norm_num

theorem DPlusI_idempotent : DPlusI * DPlusI = DPlusI := by
  change rhoPlus * rhoPlus = rhoPlus
  exact rhoPlus_idempotent

theorem DMinusI_idempotent : DMinusI * DMinusI = DMinusI := by
  change rhoMinus * rhoMinus = rhoMinus
  exact rhoMinus_idempotent

theorem DPlusI_mul_DMinusI : DPlusI * DMinusI = 0 := by
  change rhoPlus * rhoMinus = 0
  exact rhoPlus_mul_rhoMinus

theorem DMinusI_mul_DPlusI : DMinusI * DPlusI = 0 := by
  change rhoMinus * rhoPlus = 0
  exact rhoMinus_mul_rhoPlus

theorem GnPlusJ_sq (n : Fin 3) : GnPlusJ n * GnPlusJ n = 0 := by
  fin_cases n <;>
    change ZornCell.mulZ _ _ = 0
  all_goals
    unfold GnPlusJ
    apply zorn_ext <;>
      dsimp only [zero_val, GogberashviliSplitOctonionBasis.addZ_val,
        GogberashviliSplitOctonionBasis.smulZ_val, ZornCell.mulZ,
        negZ, GogberashviliSplitOctonionBasis.smulZ,
        GogberashviliSplitOctonionBasis.addZ, GogberashviliSplitOctonionBasis.zeroZ, J, j] <;> ring

theorem GnMinusJ_sq (n : Fin 3) : GnMinusJ n * GnMinusJ n = 0 := by
  fin_cases n <;>
    change ZornCell.mulZ _ _ = 0
  all_goals
    unfold GnMinusJ
    apply zorn_ext <;>
      dsimp only [zero_val, GogberashviliSplitOctonionBasis.addZ_val,
        GogberashviliSplitOctonionBasis.smulZ_val, ZornCell.mulZ,
        negZ, GogberashviliSplitOctonionBasis.smulZ,
        GogberashviliSplitOctonionBasis.addZ, GogberashviliSplitOctonionBasis.zeroZ, J, j] <;> ring

theorem GnPlusI_sq (n : Fin 3) : GnPlusI n * GnPlusI n = 0 := by
  change G_plus n * G_plus n = 0
  exact G_plus_nilpotent n

theorem GnMinusI_sq (n : Fin 3) : GnMinusI n * GnMinusI n = 0 := by
  change G_minus n * G_minus n = 0
  exact G_minus_nilpotent n

theorem DnPlusJ_mul_GnPlusI (n : Fin 3) :
    DnPlusJ n * GnPlusI n = 0 := by
  fin_cases n <;> change ZornCell.mulZ _ _ = 0
  all_goals
    unfold DnPlusJ GnPlusI
    apply zorn_ext <;>
      dsimp only [zero_val, GogberashviliSplitOctonionBasis.addZ_val,
        GogberashviliSplitOctonionBasis.smulZ_val, ZornCell.mulZ,
        negZ, GogberashviliSplitOctonionBasis.smulZ,
        GogberashviliSplitOctonionBasis.addZ,
        GogberashviliSplitOctonionBasis.zeroZ, oneZ, I, J, j] <;> norm_num

theorem DnPlusJ_mul_GnMinusI (n : Fin 3) :
    DnPlusJ n * GnMinusI n = GnMinusI n := by
  fin_cases n <;> change ZornCell.mulZ _ _ = _
  all_goals
    unfold DnPlusJ GnMinusI
    apply zorn_ext <;>
      dsimp only [zero_val, GogberashviliSplitOctonionBasis.addZ_val,
        GogberashviliSplitOctonionBasis.smulZ_val, ZornCell.mulZ,
        negZ, GogberashviliSplitOctonionBasis.smulZ,
        GogberashviliSplitOctonionBasis.addZ,
        GogberashviliSplitOctonionBasis.zeroZ, oneZ, I, J, j] <;> norm_num

theorem DnMinusJ_mul_GnPlusI (n : Fin 3) :
    DnMinusJ n * GnPlusI n = GnPlusI n := by
  fin_cases n <;> change ZornCell.mulZ _ _ = _
  all_goals
    unfold DnMinusJ GnPlusI
    apply zorn_ext <;>
      dsimp only [zero_val, GogberashviliSplitOctonionBasis.addZ_val,
        GogberashviliSplitOctonionBasis.smulZ_val, ZornCell.mulZ,
        negZ, GogberashviliSplitOctonionBasis.smulZ,
        GogberashviliSplitOctonionBasis.addZ,
        GogberashviliSplitOctonionBasis.zeroZ, oneZ, I, J, j] <;> norm_num

theorem DnMinusJ_mul_GnMinusI (n : Fin 3) :
    DnMinusJ n * GnMinusI n = 0 := by
  fin_cases n <;> change ZornCell.mulZ _ _ = 0
  all_goals
    unfold DnMinusJ GnMinusI
    apply zorn_ext <;>
      dsimp only [zero_val, GogberashviliSplitOctonionBasis.addZ_val,
        GogberashviliSplitOctonionBasis.smulZ_val, ZornCell.mulZ,
        negZ, GogberashviliSplitOctonionBasis.smulZ,
        GogberashviliSplitOctonionBasis.addZ,
        GogberashviliSplitOctonionBasis.zeroZ, oneZ, I, J, j] <;> norm_num

theorem GnPlusJ_mul_GnMinusJ (n : Fin 3) :
    GnPlusJ n * GnMinusJ n = DPlusI := by
  fin_cases n <;>
    change ZornCell.mulZ _ _ = _
  all_goals
    unfold GnPlusJ GnMinusJ DPlusI
    apply zorn_ext <;>
      dsimp only [zero_val, GogberashviliSplitOctonionBasis.addZ_val,
        GogberashviliSplitOctonionBasis.smulZ_val, ZornCell.mulZ,
        negZ, GogberashviliSplitOctonionBasis.smulZ,
        GogberashviliSplitOctonionBasis.addZ, GogberashviliSplitOctonionBasis.zeroZ, oneZ, I, J, j] <;> norm_num

theorem GnMinusJ_mul_GnPlusJ (n : Fin 3) :
    GnMinusJ n * GnPlusJ n = DMinusI := by
  fin_cases n <;>
    change ZornCell.mulZ _ _ = _
  all_goals
    unfold GnMinusJ GnPlusJ DMinusI
    apply zorn_ext <;>
      dsimp only [zero_val, GogberashviliSplitOctonionBasis.addZ_val,
        GogberashviliSplitOctonionBasis.smulZ_val, ZornCell.mulZ,
        negZ, GogberashviliSplitOctonionBasis.smulZ,
        GogberashviliSplitOctonionBasis.addZ, GogberashviliSplitOctonionBasis.zeroZ, oneZ, I, J, j] <;> norm_num

theorem GnPlusI_mul_GnMinusI (n : Fin 3) :
    GnPlusI n * GnMinusI n = DnMinusJ n := by
  change G_plus n * G_minus n = D_minus n
  exact G_plus_mul_G_minus n

theorem GnMinusI_mul_GnPlusI (n : Fin 3) :
    GnMinusI n * GnPlusI n = DnPlusJ n := by
  fin_cases n <;>
    change ZornCell.mulZ _ _ = _
  all_goals
    unfold GnMinusI GnPlusI DnPlusJ
    apply zorn_ext <;>
      dsimp only [zero_val, GogberashviliSplitOctonionBasis.addZ_val,
        GogberashviliSplitOctonionBasis.smulZ_val, ZornCell.mulZ,
        negZ, GogberashviliSplitOctonionBasis.smulZ,
        GogberashviliSplitOctonionBasis.addZ, GogberashviliSplitOctonionBasis.zeroZ, oneZ, I, J, j] <;> norm_num

theorem DnPlusJ_add_DnMinusJ (n : Fin 3) :
    DnPlusJ n + DnMinusJ n = oneZ := by
  fin_cases n <;>
    apply zorn_ext <;>
      dsimp only [DnPlusJ, DnMinusJ, zero_val,
        GogberashviliSplitOctonionBasis.addZ_val,
        GogberashviliSplitOctonionBasis.smulZ_val, negZ,
        GogberashviliSplitOctonionBasis.smulZ,
        GogberashviliSplitOctonionBasis.addZ,
        GogberashviliSplitOctonionBasis.zeroZ, oneZ, J, j] <;> norm_num

theorem GnPlusJ_anticommutator_GnMinusJ (n : Fin 3) :
    GnPlusJ n * GnMinusJ n + GnMinusJ n * GnPlusJ n = oneZ := by
  rw [GnPlusJ_mul_GnMinusJ, GnMinusJ_mul_GnPlusJ]
  exact rhoPlus_add_rhoMinus

theorem GnPlusI_anticommutator_GnMinusI (n : Fin 3) :
    GnPlusI n * GnMinusI n + GnMinusI n * GnPlusI n = oneZ := by
  rw [GnPlusI_mul_GnMinusI, GnMinusI_mul_GnPlusI]
  fin_cases n <;>
    apply zorn_ext <;>
      dsimp only [DnMinusJ, DnPlusJ, zero_val,
        GogberashviliSplitOctonionBasis.addZ_val,
        GogberashviliSplitOctonionBasis.smulZ_val, negZ,
        GogberashviliSplitOctonionBasis.smulZ,
        GogberashviliSplitOctonionBasis.addZ,
        GogberashviliSplitOctonionBasis.zeroZ, oneZ, J, j] <;> norm_num

end InfoGeometry.Clifford.GogberashviliAppendixE
