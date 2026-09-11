import InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Quaternionic split doubling by the hyperbolic unit `ℓ`

This is a semantic dictionary over the existing Gogberashvili/Zorn basis.
The quaternionic units are `j n`, the distinguished split unit is `I`, and
its lifted directions are `J n = I * j n`.  No second multiplication table
is introduced here.
-/

namespace InfoGeometry.Clifford.SplitOctonionQuaternionEllBridge

open InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

abbrev Carrier := ZornCell ℝ

abbrev quaternionUnit (i : Fin 3) : Carrier := j i

abbrev ell : Carrier := I

abbrev ellLift (i : Fin 3) : Carrier := J i

noncomputable def rhoPlus : Carrier := (1 / 2 : ℝ) • (oneZ + ell)

noncomputable def rhoMinus : Carrier := (1 / 2 : ℝ) • (oneZ + negZ ell)

noncomputable def wittPlus (i : Fin 3) : Carrier :=
  (1 / 2 : ℝ) • (quaternionUnit i + ellLift i)

noncomputable def wittMinus (i : Fin 3) : Carrier :=
  (1 / 2 : ℝ) • (quaternionUnit i + negZ (ellLift i))

theorem ell_sq : ell * ell = oneZ := by
  exact I_sq

theorem quaternionUnit_sq (i : Fin 3) :
    quaternionUnit i * quaternionUnit i = negZ oneZ := by
  exact j_sq i

theorem ell_anticomm_quaternionUnit (i : Fin 3) :
    ell * quaternionUnit i = negZ (quaternionUnit i * ell) := by
  rw [I_mul_j, j_mul_I]
  fin_cases i <;> apply zorn_ext <;> simp [negZ]

theorem ellLift_eq_ell_mul_quaternionUnit (i : Fin 3) :
    ellLift i = ell * quaternionUnit i := by
  exact (I_mul_j i).symm

theorem rhoPlus_idempotent : rhoPlus * rhoPlus = rhoPlus := by
  unfold rhoPlus ell
  change mulZ ((1 / 2 : ℝ) • (oneZ + I)) ((1 / 2 : ℝ) • (oneZ + I)) = _
  apply zorn_ext <;>
    dsimp only [GogberashviliSplitOctonionBasis.smulZ_val,
      GogberashviliSplitOctonionBasis.addZ_val,
      GogberashviliSplitOctonionBasis.smulZ,
      GogberashviliSplitOctonionBasis.addZ, oneZ, I, ZornCell.mulZ] <;> norm_num

theorem rhoMinus_idempotent : rhoMinus * rhoMinus = rhoMinus := by
  unfold rhoMinus ell
  change mulZ ((1 / 2 : ℝ) • (oneZ + negZ I)) ((1 / 2 : ℝ) • (oneZ + negZ I)) = _
  apply zorn_ext <;>
    dsimp only [GogberashviliSplitOctonionBasis.smulZ_val,
      GogberashviliSplitOctonionBasis.addZ_val,
      GogberashviliSplitOctonionBasis.smulZ,
      GogberashviliSplitOctonionBasis.addZ, oneZ, negZ, I, ZornCell.mulZ] <;> norm_num

theorem rhoPlus_mul_rhoMinus : rhoPlus * rhoMinus = 0 := by
  unfold rhoPlus rhoMinus ell
  change mulZ ((1 / 2 : ℝ) • (oneZ + I)) ((1 / 2 : ℝ) • (oneZ + negZ I)) = 0
  apply zorn_ext <;>
    dsimp only [GogberashviliSplitOctonionBasis.smulZ_val,
      GogberashviliSplitOctonionBasis.addZ_val,
      GogberashviliSplitOctonionBasis.smulZ,
      GogberashviliSplitOctonionBasis.addZ,
      GogberashviliSplitOctonionBasis.zero_val,
      oneZ, negZ, I, zeroZ, ZornCell.mulZ] <;> norm_num

theorem rhoMinus_mul_rhoPlus : rhoMinus * rhoPlus = 0 := by
  unfold rhoPlus rhoMinus ell
  change mulZ ((1 / 2 : ℝ) • (oneZ + negZ I)) ((1 / 2 : ℝ) • (oneZ + I)) = 0
  apply zorn_ext <;>
    dsimp only [GogberashviliSplitOctonionBasis.smulZ_val,
      GogberashviliSplitOctonionBasis.addZ_val,
      GogberashviliSplitOctonionBasis.smulZ,
      GogberashviliSplitOctonionBasis.addZ,
      GogberashviliSplitOctonionBasis.zero_val,
      oneZ, negZ, I, zeroZ, ZornCell.mulZ] <;> norm_num

theorem rhoPlus_add_rhoMinus : rhoPlus + rhoMinus = oneZ := by
  unfold rhoPlus rhoMinus ell
  apply zorn_ext <;>
    dsimp only [GogberashviliSplitOctonionBasis.smulZ_val,
      GogberashviliSplitOctonionBasis.addZ_val,
      GogberashviliSplitOctonionBasis.smulZ,
      GogberashviliSplitOctonionBasis.addZ, oneZ, negZ, I] <;> norm_num

theorem wittPlus_sq (i : Fin 3) : wittPlus i * wittPlus i = 0 := by
  fin_cases i
  all_goals
    unfold wittPlus quaternionUnit ellLift
    change mulZ ((1 / 2 : ℝ) • (j _ + J _)) ((1 / 2 : ℝ) • (j _ + J _)) = 0
    apply zorn_ext <;>
      dsimp only [GogberashviliSplitOctonionBasis.smulZ_val,
        GogberashviliSplitOctonionBasis.addZ_val,
        GogberashviliSplitOctonionBasis.smulZ,
        GogberashviliSplitOctonionBasis.addZ,
        GogberashviliSplitOctonionBasis.zero_val,
        zeroZ, j, J, ZornCell.mulZ] <;> ring

theorem wittMinus_sq (i : Fin 3) : wittMinus i * wittMinus i = 0 := by
  fin_cases i
  all_goals
    unfold wittMinus quaternionUnit ellLift
    change mulZ ((1 / 2 : ℝ) • (j _ + negZ (J _)))
      ((1 / 2 : ℝ) • (j _ + negZ (J _))) = 0
    apply zorn_ext <;>
      dsimp only [GogberashviliSplitOctonionBasis.smulZ_val,
        GogberashviliSplitOctonionBasis.addZ_val,
        GogberashviliSplitOctonionBasis.smulZ,
        GogberashviliSplitOctonionBasis.addZ,
        GogberashviliSplitOctonionBasis.zero_val,
        negZ, zeroZ, j, J, ZornCell.mulZ] <;> ring

theorem splitPlane_sq (a b : ℝ) (i : Fin 3) :
    (a • quaternionUnit i + b • ellLift i) *
        (a • quaternionUnit i + b • ellLift i) =
      (b ^ 2 - a ^ 2) • oneZ := by
  fin_cases i <;>
    unfold quaternionUnit ellLift <;>
    change ZornCell.mulZ _ _ = _ <;>
    apply zorn_ext <;>
    dsimp only [GogberashviliSplitOctonionBasis.smulZ_val,
      GogberashviliSplitOctonionBasis.addZ_val,
      GogberashviliSplitOctonionBasis.smulZ,
      GogberashviliSplitOctonionBasis.addZ,
      GogberashviliSplitOctonionBasis.oneZ,
      GogberashviliSplitOctonionBasis.j,
      GogberashviliSplitOctonionBasis.J,
      ZornCell.mulZ] <;>
    ring

/-! Named split-plane corollaries.  This owner is the raw signature/null
seed; associative reciprocal spectral flow belongs to the projective owner. -/

theorem splitPlane_nullPlus_sq (i : Fin 3) :
    wittPlus i * wittPlus i = 0 :=
  wittPlus_sq i

theorem splitPlane_nullMinus_sq (i : Fin 3) :
    wittMinus i * wittMinus i = 0 :=
  wittMinus_sq i

theorem splitPlane_reconstruction (a b : ℝ) (i : Fin 3) :
    a • quaternionUnit i + b • ellLift i =
      (a + b) • wittPlus i + (a - b) • wittMinus i := by
  unfold wittPlus wittMinus quaternionUnit ellLift
  fin_cases i <;> apply zorn_ext <;>
    dsimp only [GogberashviliSplitOctonionBasis.smulZ_val,
      GogberashviliSplitOctonionBasis.addZ_val,
      GogberashviliSplitOctonionBasis.smulZ,
      GogberashviliSplitOctonionBasis.addZ,
      GogberashviliSplitOctonionBasis.j,
      GogberashviliSplitOctonionBasis.J,
      GogberashviliSplitOctonionBasis.negZ] <;> ring

theorem splitPlane_quadratic_form (a b : ℝ) (i : Fin 3) :
    (a • quaternionUnit i + b • ellLift i) *
        (a • quaternionUnit i + b • ellLift i) =
      (b ^ 2 - a ^ 2) • oneZ :=
  splitPlane_sq a b i

theorem ell_mul_quaternionUnit (i : Fin 3) :
    ell * quaternionUnit i = ellLift i := by
  exact I_mul_j i

theorem ell_mul_ellLift (i : Fin 3) :
    ell * ellLift i = quaternionUnit i := by
  fin_cases i
  all_goals
    unfold ell ellLift quaternionUnit
    change mulZ I (J _) = j _
    exact I_mul_J _

end InfoGeometry.Clifford.SplitOctonionQuaternionEllBridge
