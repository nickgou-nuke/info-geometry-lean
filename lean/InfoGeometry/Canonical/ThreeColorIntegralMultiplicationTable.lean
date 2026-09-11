import InfoGeometry.Canonical.StandardIntegralSplitOctonionMultiplication
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open Submodule

/-!
  Coordinate-level multiplication consequences for the three pure colour
  planes. The underlying product is the executable `basisMul` tensor from
  `StandardIntegralSplitOctonionMultiplication`.
-/

def DZ : Submodule ℤ StandardIntegralSplitOctonion :=
  span ℤ {oneOct, lOct}

def Pr : Submodule ℤ StandardIntegralSplitOctonion :=
  span ℤ {iOct, ilOct}

def Pg : Submodule ℤ StandardIntegralSplitOctonion :=
  span ℤ {jOct, jlOct}

def Pb : Submodule ℤ StandardIntegralSplitOctonion :=
  span ℤ {kOct, klOct}

theorem red_basis_mul_green_mem_blue :
    splitOctonionMul iOct jOct ∈ Pb := by
  rw [i_mul_j_eq_k]
  exact subset_span (Set.mem_insert _ _)

def nr_plus : StandardIntegralSplitOctonion := iOct + ilOct
def nr_minus : StandardIntegralSplitOctonion := iOct - ilOct
def ng_plus : StandardIntegralSplitOctonion := jOct + jlOct
def ng_minus : StandardIntegralSplitOctonion := jOct - jlOct
def nb_plus : StandardIntegralSplitOctonion := kOct + klOct
def nb_minus : StandardIntegralSplitOctonion := kOct - klOct

theorem redPlus_mul_greenPlus :
    splitOctonionMul nr_plus ng_plus = 2 • nb_minus := by
  ext r <;> fin_cases r <;> native_decide

theorem redMinus_mul_greenMinus :
    splitOctonionMul nr_minus ng_minus = 2 • nb_plus := by
  ext r <;> fin_cases r <;> native_decide

theorem redPlus_mul_greenMinus :
    splitOctonionMul nr_plus ng_minus = 0 := by
  ext r <;> fin_cases r <;> native_decide

theorem redMinus_mul_greenPlus :
    splitOctonionMul nr_minus ng_plus = 0 := by
  ext r <;> fin_cases r <;> native_decide

def splitAssociator (x y z : StandardIntegralSplitOctonion) :
    StandardIntegralSplitOctonion :=
  splitOctonionMul (splitOctonionMul x y) z -
    splitOctonionMul x (splitOctonionMul y z)

theorem i_l_j_associator_value :
    splitAssociator iOct lOct jOct = (-2 : ℤ) • klOct := by
  ext r <;> fin_cases r <;> native_decide

theorem i_l_j_associator_ne_zero :
    splitAssociator iOct lOct jOct ≠ 0 := by
  rw [i_l_j_associator_value]
  intro h
  have hk : ((-2 : ℤ) • klOct) IntegralSplitBasis.kl =
      (0 : StandardIntegralSplitOctonion) IntegralSplitBasis.kl := by
    rw [h]
  norm_num [klOct, splitBasisVector] at hk

end InfoGeometry.Canonical
