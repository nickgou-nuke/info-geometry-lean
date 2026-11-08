import InfoGeometry.Canonical.AnalyticalIndexCore
import InfoGeometry.OperatorAlgebra.ChiralFredholmIndex
import InfoGeometry.Physics.BdGChiralBlockMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite chiral index of the real two-dimensional mass block

The grading is minus the existing BdG grading. Projectors come from
`AnalyticalIndexCore`; the index is the existing kernel-minus-cokernel
Fredholm index. This finite calculation asserts neither an AZ classification
nor preservation of a spectral gap at zero mass.
-/

noncomputable section

namespace InfoGeometry.KTheory.ConcreteFredholmIndex

open InfoGeometry.Physics
open InfoGeometry.Canonical.AnalyticalIndex
open InfoGeometry.OperatorAlgebra.ChiralFredholmIndex

abbrev Vec2R := Fin 2 → ℝ

abbrev grading : Module.End ℝ Vec2R := -(chiralGrading : BdGBlock ℝ).mulVecLin
abbrev dirac (mass : ℝ) : Module.End ℝ Vec2R := (diracOperator mass).mulVecLin
abbrev P_plus : Module.End ℝ Vec2R := chiralProjectorPlus grading
abbrev P_minus : Module.End ℝ Vec2R := chiralProjectorMinus grading
abbrev E_plus := LinearMap.range P_plus
abbrev E_minus := LinearMap.range P_minus

theorem P_plus_apply (vector : Vec2R) : P_plus vector = ![0, vector 1] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [P_plus, chiralProjectorPlus, grading, chiralGrading,
      dotProduct, Fin.sum_univ_two] <;> norm_num <;> ring

theorem P_minus_apply (vector : Vec2R) : P_minus vector = ![vector 0, 0] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [P_minus, chiralProjectorMinus, grading, chiralGrading,
      dotProduct, Fin.sum_univ_two] <;> norm_num <;> ring

theorem dirac_apply (mass : ℝ) (vector : Vec2R) :
    dirac mass vector = ![mass * vector 1, mass * vector 0] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [dirac, diracOperator, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mem_E_plus_iff (vector : Vec2R) : vector ∈ E_plus ↔ vector 0 = 0 := by
  constructor
  · rintro ⟨preimage, rfl⟩
    simp [P_plus_apply]
  · intro hzero
    refine ⟨vector, ?_⟩
    rw [P_plus_apply]
    ext coordinate
    fin_cases coordinate <;> simp [hzero]

theorem mem_E_minus_iff (vector : Vec2R) : vector ∈ E_minus ↔ vector 1 = 0 := by
  constructor
  · rintro ⟨preimage, rfl⟩
    simp [P_minus_apply]
  · intro hzero
    refine ⟨vector, ?_⟩
    rw [P_minus_apply]
    ext coordinate
    fin_cases coordinate <;> simp [hzero]

def plusCoordinateEquiv : E_plus ≃ₗ[ℝ] ℝ where
  toFun vector := vector.val 1
  invFun scalar := ⟨![0, scalar], (mem_E_plus_iff _).mpr (by simp)⟩
  left_inv vector := by
    apply Subtype.ext
    ext coordinate
    fin_cases coordinate <;> simp [(mem_E_plus_iff _).mp vector.property]
  right_inv scalar := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def minusCoordinateEquiv : E_minus ≃ₗ[ℝ] ℝ where
  toFun vector := vector.val 0
  invFun scalar := ⟨![scalar, 0], (mem_E_minus_iff _).mpr (by simp)⟩
  left_inv vector := by
    apply Subtype.ext
    ext coordinate
    fin_cases coordinate <;> simp [(mem_E_minus_iff _).mp vector.property]
  right_inv scalar := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem E_plus_finrank : Module.finrank ℝ E_plus = 1 := by
  simpa using plusCoordinateEquiv.finrank_eq

theorem E_minus_finrank : Module.finrank ℝ E_minus = 1 := by
  simpa using minusCoordinateEquiv.finrank_eq

def D_plus (mass : ℝ) : E_plus →ₗ[ℝ] E_minus :=
  (dirac mass).restrict (by
    intro vector hvector
    rw [mem_E_minus_iff, dirac_apply]
    simp [(mem_E_plus_iff _).mp hvector])

def D_minus (mass : ℝ) : E_minus →ₗ[ℝ] E_plus :=
  (dirac mass).restrict (by
    intro vector hvector
    rw [mem_E_plus_iff, dirac_apply]
    simp [(mem_E_minus_iff _).mp hvector])

theorem D_plus_coordinate (mass : ℝ) (vector : E_plus) :
    minusCoordinateEquiv (D_plus mass vector) = mass * plusCoordinateEquiv vector := by
  change (dirac mass vector.val) 0 = mass * vector.val 1
  exact congrFun (dirac_apply mass vector.val) 0

theorem D_minus_coordinate (mass : ℝ) (vector : E_minus) :
    plusCoordinateEquiv (D_minus mass vector) = mass * minusCoordinateEquiv vector := by
  change (dirac mass vector.val) 1 = mass * vector.val 0
  exact congrFun (dirac_apply mass vector.val) 1

theorem ker_D_plus_trivial (mass : ℝ) (hnonzero : mass ≠ 0) :
    LinearMap.ker (D_plus mass) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro first second hequal
  apply plusCoordinateEquiv.injective
  apply mul_left_cancel₀ hnonzero
  simpa only [D_plus_coordinate] using congrArg minusCoordinateEquiv hequal

theorem ker_D_minus_trivial (mass : ℝ) (hnonzero : mass ≠ 0) :
    LinearMap.ker (D_minus mass) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro first second hequal
  apply minusCoordinateEquiv.injective
  apply mul_left_cancel₀ hnonzero
  simpa only [D_minus_coordinate] using congrArg plusCoordinateEquiv hequal

theorem D_plus_zero : D_plus 0 = 0 := by
  apply LinearMap.ext
  intro vector
  apply minusCoordinateEquiv.injective
  simp [D_plus_coordinate]

theorem D_minus_zero : D_minus 0 = 0 := by
  apply LinearMap.ext
  intro vector
  apply plusCoordinateEquiv.injective
  simp [D_minus_coordinate]

theorem massless_kernel_dimensions :
    Module.finrank ℝ (LinearMap.ker (D_plus 0)) = 1 ∧
      Module.finrank ℝ (LinearMap.ker (D_minus 0)) = 1 := by
  rw [D_plus_zero, D_minus_zero, LinearMap.ker_zero, LinearMap.ker_zero]
  constructor
  · simpa using E_plus_finrank
  · simpa using E_minus_finrank

theorem massive_kernel_dimensions (mass : ℝ) (hnonzero : mass ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (D_plus mass)) = 0 ∧
      Module.finrank ℝ (LinearMap.ker (D_minus mass)) = 0 := by
  simp [ker_D_plus_trivial mass hnonzero, ker_D_minus_trivial mass hnonzero]

def fredholmDatum (mass : ℝ) : FredholmIndexDatum E_plus E_minus where
  operator := D_plus mass
  kernelFinite := inferInstance
  cokernelFinite := inferInstance

abbrev fredholm_index (mass : ℝ) : ℤ := (fredholmDatum mass).index

/-- Rank-nullity computes the actual kernel-minus-cokernel index for every mass. -/
theorem fredholm_index_eq_zero (mass : ℝ) : fredholm_index mass = 0 := by
  change (Module.finrank ℝ (LinearMap.ker (D_plus mass)) : ℤ) -
    (Module.finrank ℝ (E_minus ⧸ LinearMap.range (D_plus mass)) : ℤ) = 0
  have hdomain := (D_plus mass).finrank_range_add_finrank_ker
  have hcodomain := (LinearMap.range (D_plus mass)).finrank_quotient_add_finrank
  rw [E_plus_finrank] at hdomain
  rw [E_minus_finrank] at hcodomain
  omega

theorem fredholm_index_eq_chiral_kernel_difference (mass : ℝ) :
    fredholm_index mass =
      (Module.finrank ℝ (LinearMap.ker (D_plus mass)) : ℤ) -
        (Module.finrank ℝ (LinearMap.ker (D_minus mass)) : ℤ) := by
  rw [fredholm_index_eq_zero]
  by_cases hzero : mass = 0
  · subst mass
    rw [massless_kernel_dimensions.1, massless_kernel_dimensions.2]
    norm_num
  · rw [(massive_kernel_dimensions mass hzero).1,
      (massive_kernel_dimensions mass hzero).2]
    norm_num

theorem fredholm_index_massive (mass : ℝ) (_hnonzero : mass ≠ 0) :
    fredholm_index mass = 0 := fredholm_index_eq_zero mass

theorem fredholm_index_massless : fredholm_index 0 = 0 := fredholm_index_eq_zero 0

end InfoGeometry.KTheory.ConcreteFredholmIndex
