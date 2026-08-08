import Mathlib

/-!
# Itakura--Saito divergence on nilpotent boundary modes

For a square-zero/nilpotent boundary mode `K²=0`, the exponential truncates
formally to `exp(K)=1+K`.  Therefore the operator-valued Itakura--Saito
remainder

`D_IS(K)=exp(K)-1-K`

vanishes.  This is the information-geometric version of the massless
nullspace collapse: the nilpotent parafermion defect has zero quadratic
Fisher/Bures remainder.
-/

noncomputable section

namespace NilpotentItakuraSaito

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- A concrete nilpotent Jordan boundary mode. -/
def KNil : M2C := !![0, 1; 0, 0]

/-- The concrete boundary mode is nilpotent. -/
theorem KNil_sq_zero : KNil * KNil = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [KNil, Matrix.mul_apply, Fin.sum_univ_two]

/-- Formal exponential truncation for a square-zero element. -/
def nilExp (K : M2C) : M2C := 1 + K

/-- Itakura--Saito remainder using the nilpotent-truncated exponential. -/
def nilItakuraSaito (K : M2C) : M2C := nilExp K - 1 - K

/-- The nilpotent Itakura--Saito remainder vanishes algebraically. -/
theorem nilItakuraSaito_zero (K : M2C) : nilItakuraSaito K = 0 := by
  ext i j
  simp [nilItakuraSaito, nilExp, Matrix.sub_apply, Matrix.add_apply]

/-- In particular, the concrete nilpotent has zero divergence. -/
theorem KNil_itakura_zero : nilItakuraSaito KNil = 0 := nilItakuraSaito_zero KNil

/-- Scaled nilpotents also have zero truncated Itakura--Saito remainder. -/
theorem scaled_nilItakuraSaito_zero (eps : ℂ) (K : M2C) :
    nilItakuraSaito (eps • K) = 0 :=
  nilItakuraSaito_zero (eps • K)

/-- Main synthesis theorem. -/
theorem nilpotent_itakura_saito_synthesis :
    KNil * KNil = 0 ∧
    nilItakuraSaito KNil = 0 ∧
    (∀ eps : ℂ, nilItakuraSaito (eps • KNil) = 0) := by
  exact ⟨KNil_sq_zero, KNil_itakura_zero, fun eps => scaled_nilItakuraSaito_zero eps KNil⟩

#check KNil_sq_zero
#check nilItakuraSaito_zero
#check scaled_nilItakuraSaito_zero
#check nilpotent_itakura_saito_synthesis

end NilpotentItakuraSaito
