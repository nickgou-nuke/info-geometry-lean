import InfoGeometry.Clifford.Cl55ThreeColorChiralSums

/-!
# Native colour CAR readout

The colour lanes live in the repository-owned noncommutative `Cl(5,5)`
carrier.  This module is deliberately only a finite CAR/grade readout; it
does not claim a Standard Model representation or an identification with a
matrix/tensor-product toy.
-/

noncomputable section

namespace InfoGeometry.Physics.ColorCARStandardModel

open InfoGeometry.Clifford.Clifford55

abbrev CAR3 : Type := Cl55

def carAnn0 : CAR3 := chiralPlus55 0
def carAnn1 : CAR3 := chiralPlus55 1
def carAnn2 : CAR3 := chiralPlus55 2

def carCre0 : CAR3 := chiralMinus55 0
def carCre1 : CAR3 := chiralMinus55 1
def carCre2 : CAR3 := chiralMinus55 2

def vacuum : CAR3 := 1

def fureyGeneration : Submodule ℝ CAR3 :=
  Submodule.span ℝ {
    vacuum,
    carCre0, carCre1, carCre2,
    carCre0 * carCre1, carCre1 * carCre2, carCre0 * carCre2,
    carCre0 * carCre1 * carCre2
  }

theorem vacuum_mem_fureyGeneration : vacuum ∈ fureyGeneration := by
  exact Submodule.subset_span (by simp [fureyGeneration])

theorem carCre0_mem_fureyGeneration : carCre0 ∈ fureyGeneration := by
  exact Submodule.subset_span (by simp [fureyGeneration])

theorem carCre1_mem_fureyGeneration : carCre1 ∈ fureyGeneration := by
  exact Submodule.subset_span (by simp [fureyGeneration])

theorem carCre2_mem_fureyGeneration : carCre2 ∈ fureyGeneration := by
  exact Submodule.subset_span (by simp [fureyGeneration])

def fureyConjugateGeneration : Submodule ℝ CAR3 :=
  Submodule.span ℝ {
    vacuum,
    carAnn0, carAnn1, carAnn2,
    carAnn0 * carAnn1, carAnn1 * carAnn2, carAnn0 * carAnn2,
    carAnn0 * carAnn1 * carAnn2
  }

theorem vacuum_mem_fureyConjugateGeneration : vacuum ∈ fureyConjugateGeneration := by
  exact Submodule.subset_span (by simp [fureyConjugateGeneration])

theorem carAnn0_mem_fureyConjugateGeneration : carAnn0 ∈ fureyConjugateGeneration := by
  exact Submodule.subset_span (by simp [fureyConjugateGeneration])

theorem carAnn1_mem_fureyConjugateGeneration : carAnn1 ∈ fureyConjugateGeneration := by
  exact Submodule.subset_span (by simp [fureyConjugateGeneration])

theorem carAnn2_mem_fureyConjugateGeneration : carAnn2 ∈ fureyConjugateGeneration := by
  exact Submodule.subset_span (by simp [fureyConjugateGeneration])

theorem carAnn_mem_fureyConjugateGeneration (i : Fin 3) :
    chiralPlus55 i ∈ fureyConjugateGeneration := by
  fin_cases i
  · simpa [carAnn0] using carAnn0_mem_fureyConjugateGeneration
  · simpa [carAnn1] using carAnn1_mem_fureyConjugateGeneration
  · simpa [carAnn2] using carAnn2_mem_fureyConjugateGeneration

def numberOp0 : CAR3 := carAnn0 * carCre0
def numberOp1 : CAR3 := carAnn1 * carCre1
def numberOp2 : CAR3 := carAnn2 * carCre2

theorem numberOp0_idem : numberOp0 * numberOp0 = numberOp0 :=
  chiralNumber55_idem 0

theorem numberOp1_idem : numberOp1 * numberOp1 = numberOp1 :=
  chiralNumber55_idem 1

theorem numberOp2_idem : numberOp2 * numberOp2 = numberOp2 :=
  chiralNumber55_idem 2

def N_plus : Cl55 := chiralPlus55 0 * chiralMinus55 0
def N_minus : Cl55 := chiralMinus55 0 * chiralPlus55 0

theorem N_plus_add_N_minus : N_plus + N_minus = (1 : Cl55) := by
  simpa [N_plus, N_minus] using
    (chiralPlus55_minus55_anticommutator (0 : Fin 3) 0)

theorem N_plus_mul_N_minus : N_plus * N_minus = 0 := by
  change (chiralPlus55 0 * chiralMinus55 0) *
      (chiralMinus55 0 * chiralPlus55 0) = 0
  rw [show (chiralPlus55 0 * chiralMinus55 0) *
      (chiralMinus55 0 * chiralPlus55 0) =
      chiralPlus55 0 * (chiralMinus55 0 * chiralMinus55 0) *
        chiralPlus55 0 by noncomm_ring]
  rw [chiralMinus55_sq]
  simp

theorem N_minus_mul_N_plus : N_minus * N_plus = 0 := by
  change (chiralMinus55 0 * chiralPlus55 0) *
      (chiralPlus55 0 * chiralMinus55 0) = 0
  rw [show (chiralMinus55 0 * chiralPlus55 0) *
      (chiralPlus55 0 * chiralMinus55 0) =
      chiralMinus55 0 * (chiralPlus55 0 * chiralPlus55 0) *
        chiralMinus55 0 by noncomm_ring]
  rw [chiralPlus55_sq]
  simp

theorem color_car_native_closure :
    chiralPlusSum * chiralPlusSum = 0 ∧
    chiralMinusSum * chiralMinusSum = 0 ∧
    chiralMinusSum * chiralPlusSum +
        chiralPlusSum * chiralMinusSum = (3 : Cl55) ∧
    numberOp0 * numberOp0 = numberOp0 ∧
    numberOp1 * numberOp1 = numberOp1 ∧
    numberOp2 * numberOp2 = numberOp2 := by
  exact ⟨chiralPlusSum_sq, chiralMinusSum_sq,
    chiralMinusSum_plusSum_anticommutator,
    numberOp0_idem, numberOp1_idem, numberOp2_idem⟩

end InfoGeometry.Physics.ColorCARStandardModel
