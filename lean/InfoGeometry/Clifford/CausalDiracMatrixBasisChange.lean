import InfoGeometry.Clifford.Cl11SheetDiracMatrices
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl11WittBasis
import InfoGeometry.Clifford.Cl11CircularBasis
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace InfoGeometry.Clifford

open Matrix

variable (B : Type*) [CommRing B] [Algebra ℚ B] [Algebra ℂ B]
  [IsScalarTower ℚ ℂ B] [Invertible (2 : B)]

@[simp] private theorem map_complex_half_mul_two :
    (algebraMap ℂ B) (1 / 2) * 2 = 1 := by
  have h2 : (2 : B) = (algebraMap ℂ B) 2 := (map_ofNat _ _).symm
  calc
    (algebraMap ℂ B) (1 / 2) * 2 =
        (algebraMap ℂ B) (1 / 2) * (algebraMap ℂ B) 2 := by rw [h2]
    _ = (algebraMap ℂ B) ((1 / 2) * 2) := (map_mul _ _ _).symm
    _ = 1 := by norm_num

@[simp] private theorem map_complex_I_sq :
    (algebraMap ℂ B) Complex.I * (algebraMap ℂ B) Complex.I = -1 := by
  calc
    (algebraMap ℂ B) Complex.I * (algebraMap ℂ B) Complex.I =
        (algebraMap ℂ B) (Complex.I * Complex.I) := (map_mul _ _ _).symm
    _ = -1 := by rw [Complex.I_mul_I, map_neg, map_one]

@[simp] private theorem neg_map_I_mul_I_mul_half_mul_two :
    -((algebraMap ℂ B) Complex.I *
        ((algebraMap ℂ B) Complex.I * (algebraMap ℂ B) (1 / 2)) * 2) = 1 := by
  rw [show
    (algebraMap ℂ B) Complex.I *
        ((algebraMap ℂ B) Complex.I * (algebraMap ℂ B) (1 / 2)) * 2 =
      ((algebraMap ℂ B) Complex.I * (algebraMap ℂ B) Complex.I) *
        ((algebraMap ℂ B) (1 / 2) * 2) by ring]
  rw [map_complex_I_sq, map_complex_half_mul_two]
  ring

macro "basis_ring" : tactic => `(tactic| (
  try simp only [Gamma_mat, K_mat, c_plus, c_minus, InfoGeometry.Clifford.e_plus, InfoGeometry.Clifford.e_minus, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
  try simp only [Algebra.smul_def, smul_eq_mul, sub_eq_add_neg, ← map_add, ← map_sub, ← map_neg, map_zero]
  first | done | {
    -- Convert constants to algebraMap
    try (have h2C : (2 : B) = (algebraMap ℂ B) 2 := by exact (map_ofNat _ _).symm; rw [h2C])
    try (have h2Q : (2 : B) = (algebraMap ℚ B) 2 := by exact (map_ofNat _ _).symm; rw [h2Q])
    try (have h1C : (1 : B) = (algebraMap ℂ B) 1 := by exact (map_one _).symm; rw [h1C])
    try (have h1Q : (1 : B) = (algebraMap ℚ B) 1 := by exact (map_one _).symm; rw [h1Q])
    try (have hn1C : (-1 : B) = (algebraMap ℂ B) (-1) := by exact (map_neg _ _).symm ▸ congrArg Neg.neg (map_one _).symm; rw [hn1C])
    try (have hn1Q : (-1 : B) = (algebraMap ℚ B) (-1) := by exact (map_neg _ _).symm ▸ congrArg Neg.neg (map_one _).symm; rw [hn1Q])

    try simp only [IsScalarTower.algebraMap_apply ℚ ℂ B]
    
    -- Pull everything inside the algebraMap
    try simp only [← map_mul, ← map_add, ← map_sub, ← map_neg]
    try norm_num [← map_mul, ← map_add, Complex.I_mul_I]
    try simp only [map_complex_half_mul_two, neg_map_I_mul_I_mul_half_mul_two]
    
    first | done | {
      -- Strip the algebraMap and solve in the base field
      try congr 1
      
      first | done | {
        -- Solve the field equalities
        try ring_nf
        try simp only [Complex.I_sq, Complex.I_mul_I]
        try ring_nf
        try norm_num
      }
    }
  }
))

lemma gamma_eq_witt_add : Gamma_mat (B := B) = InfoGeometry.Clifford.e_plus (B := B) + InfoGeometry.Clifford.e_minus (B := B) := by
  ext i j; fin_cases i <;> fin_cases j <;> basis_ring

lemma k_eq_witt_sub : K_mat (B := B) = InfoGeometry.Clifford.e_plus (B := B) - InfoGeometry.Clifford.e_minus (B := B) := by
  ext i j; fin_cases i <;> fin_cases j <;> basis_ring

lemma k_eq_circ_sub : K_mat (B := B) = (algebraMap ℂ B Complex.I) • (c_plus (B := B) - c_minus (B := B)) := by
  ext i j; fin_cases i <;> fin_cases j <;> basis_ring

end InfoGeometry.Clifford
