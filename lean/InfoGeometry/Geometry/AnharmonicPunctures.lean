import InfoGeometry.Clifford.SplitAtomInvolutions
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Puncture permutations are not the modular action

The two transformations of C minus {0,1} are genuine permutations, with
Coxeter relations.  The modular generators are separately bundled in native
SL(2,Z).  Translation is not a self-map of the punctured carrier.  All
logarithmic differential identities below are local rational identities;
there is no global logarithm or KMS identification in this file.
-/

noncomputable section

namespace InfoGeometry.Geometry.AnharmonicPunctures

/-- The three-punctured sphere in its finite affine chart. -/
def Punctured := {z : ℂ // z ≠ 0 ∧ z ≠ 1}

def exchange (z : Punctured) : Punctured :=
  ⟨1 - z.1, by
    constructor
    · exact sub_ne_zero.mpr (Ne.symm z.2.2)
    · intro h
      apply z.2.1
      linear_combination -h⟩

def inversion (z : Punctured) : Punctured :=
  ⟨z.1⁻¹, inv_ne_zero z.2.1, by
    intro h
    apply z.2.2
    have h' := congrArg (fun w : ℂ => w⁻¹) h
    simpa only [inv_inv, inv_one] using h'⟩

@[simp] theorem exchange_exchange (z : Punctured) : exchange (exchange z) = z := by
  apply Subtype.ext
  change 1 - (1 - z.1) = z.1
  ring

@[simp] theorem inversion_inversion (z : Punctured) : inversion (inversion z) = z := by
  apply Subtype.ext
  exact inv_inv z.1

def exchangeEquiv : Equiv.Perm Punctured where
  toFun := exchange
  invFun := exchange
  left_inv := exchange_exchange
  right_inv := exchange_exchange

def inversionEquiv : Equiv.Perm Punctured where
  toFun := inversion
  invFun := inversion
  left_inv := inversion_inversion
  right_inv := inversion_inversion

/-- The braid relation for the two puncture transpositions. -/
theorem exchange_inversion_exchange (z : Punctured) :
    exchange (inversion (exchange z)) = inversion (exchange (inversion z)) := by
  apply Subtype.ext
  change 1 - (1 - z.1)⁻¹ = (1 - z.1⁻¹)⁻¹
  have h1 : 1 - z.1 ≠ 0 := (exchange z).2.1
  have h2 : 1 - z.1⁻¹ ≠ 0 := (exchange (inversion z)).2.1
  have hz : z.1 - 1 ≠ 0 := sub_ne_zero.mpr z.2.2
  field_simp [z.2.1, h1, h2, hz] <;> ring

theorem puncture_cycle_cubed (z : Punctured) :
    exchange (inversion (exchange (inversion (exchange (inversion z))))) = z := by
  rw [exchange_inversion_exchange]
  simp only [inversion_inversion, exchange_exchange]

theorem exchangeEquiv_sq : exchangeEquiv * exchangeEquiv = 1 := by
  ext z
  exact exchange_exchange z

theorem inversionEquiv_sq : inversionEquiv * inversionEquiv = 1 := by
  ext z
  exact inversion_inversion z

theorem puncture_permutation_order_three : (exchangeEquiv * inversionEquiv) ^ 3 = 1 := by
  ext z
  exact puncture_cycle_cubed z

/-- Holomorphic 1-z fixes a point, not the entire vertical bisector. -/
theorem exchange_fixed_iff (z : ℂ) : 1 - z = z ↔ z = (1 / 2 : ℂ) := by
  constructor
  · intro h
    linear_combination (-1 / 2 : ℂ) * h
  · intro h
    linear_combination (-2 : ℂ) * h

/-- Modular S has action z -> -1/z, not z -> 1/z. -/
def modularS : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two]⟩

def modularT : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, 1; 0, 1], by norm_num [Matrix.det_fin_two]⟩

theorem modularS_square :
    (modularS : Matrix (Fin 2) (Fin 2) ℤ) * modularS = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularS, Matrix.mul_apply, Fin.sum_univ_two]

theorem modularST_cube :
    ((modularS : Matrix (Fin 2) (Fin 2) ℤ) * modularT) ^ 3 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularS, modularT, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

/-- A concrete obstruction to restricting the translation to this carrier. -/
theorem translation_not_preserves_punctures :
    ¬ ∀ z : ℂ, z ≠ 0 ∧ z ≠ 1 → (z + 1 ≠ 0 ∧ z + 1 ≠ 1) := by
  intro h
  have hbad := h (-1) (by norm_num)
  norm_num at hbad

def ratio (z : ℂ) : ℂ := z / (z - 1)

def logCoefficient (z : ℂ) : ℂ := 1 / z - 1 / (z - 1)

theorem logCoefficient_normal_form (z : Punctured) :
    logCoefficient z.1 = -1 / (z.1 * (z.1 - 1)) := by
  dsimp [logCoefficient]
  field_simp [z.2.1, sub_ne_zero.mpr z.2.2] <;> ring

theorem ratio_hasDerivAt (z : Punctured) :
    HasDerivAt ratio (-1 / (z.1 - 1) ^ 2) z.1 := by
  simpa [ratio] using
    (hasDerivAt_id z.1).div ((hasDerivAt_id z.1).sub_const 1)
      (sub_ne_zero.mpr z.2.2)

theorem ratio_logarithmic_derivative (z : Punctured) :
    (-1 / (z.1 - 1) ^ 2) / ratio z.1 = logCoefficient z.1 := by
  dsimp [ratio, logCoefficient]
  field_simp [z.2.1, sub_ne_zero.mpr z.2.2] <;> ring

/-- The pullback includes the derivative -1. -/
theorem exchange_log_form (z : Punctured) :
    logCoefficient (exchange z).1 * (-1) = -logCoefficient z.1 := by
  change logCoefficient (1 - z.1) * (-1) = -logCoefficient z.1
  dsimp [logCoefficient]
  field_simp [z.2.1, sub_ne_zero.mpr z.2.2,
    sub_ne_zero.mpr (Ne.symm z.2.2)] <;> ring

/-- Inversion permutes the residues; it does not preserve this coefficient. -/
theorem inversion_log_form (z : Punctured) :
    logCoefficient (inversion z).1 * (-1 / z.1 ^ 2) = -1 / (z.1 - 1) := by
  change logCoefficient z.1⁻¹ * (-1 / z.1 ^ 2) = -1 / (z.1 - 1)
  have hi : z.1⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (inversion z).2.2
  dsimp [logCoefficient]
  have h1 : 1 - z.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm z.2.2)
  field_simp [z.2.1, sub_ne_zero.mpr z.2.2, hi, h1] <;> ring

abbrev CMat2 := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- The coefficient lives in the complexified Cartan, not in R J. -/
def complexCartanGenerator : CMat2 :=
  (InfoGeometry.Clifford.SplitAtom.J).map (algebraMap ℝ ℂ)

def cartanCoefficient (z : Punctured) : CMat2 :=
  (logCoefficient z.1 / 2) • complexCartanGenerator

theorem cartanCoefficient_commute (z w : Punctured) :
    cartanCoefficient z * cartanCoefficient w =
      cartanCoefficient w * cartanCoefficient z := by
  simp only [cartanCoefficient, smul_mul_smul_comm, mul_comm]

theorem cartanCoefficient_lie_zero (z w : Punctured) :
    ⁅cartanCoefficient z, cartanCoefficient w⁆ = 0 := by
  rw [Ring.lie_def, cartanCoefficient_commute, sub_self]

end InfoGeometry.Geometry.AnharmonicPunctures
