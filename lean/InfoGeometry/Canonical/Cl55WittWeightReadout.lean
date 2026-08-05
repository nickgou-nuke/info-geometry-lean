import InfoGeometry.Canonical.Cl55WittLieSubalgebra

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55WittLieRouting

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittCAR

/-! The diagonal `E k k` readout of the Witt-generator Lie algebra.

The weights are recorded as integer-valued functions on the five diagonal
indices.  This is only a weight readout; it does not assert a named root
system or a real-form identification. -/

def creationWeight (i : Fin 5) : Fin 5 → ℤ :=
  fun k => if k = i then 1 else 0

def annihilationWeight (i : Fin 5) : Fin 5 → ℤ :=
  fun k => if k = i then -1 else 0

def zeroWeight (i j : Fin 5) : Fin 5 → ℤ :=
  fun k => (if k = i then 1 else 0) - (if k = j then 1 else 0)

def positiveTwoWeight (i j : Fin 5) : Fin 5 → ℤ :=
  fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)

def negativeTwoWeight (i j : Fin 5) : Fin 5 → ℤ :=
  fun k => (-if k = i then 1 else 0) + (-if k = j then 1 else 0)

theorem diagonal_creation_weight (k i : Fin 5) :
    bracket (E k k) (creation i) =
      (creationWeight i k : ℝ) • creation i := by
  rw [E_creation]
  by_cases h : k = i <;> simp [creationWeight, h]

theorem diagonal_annihilation_weight (k i : Fin 5) :
    bracket (E k k) (annihilation i) =
      (annihilationWeight i k : ℝ) • annihilation i := by
  rw [E_annihilation]
  by_cases h : k = i <;> simp [annihilationWeight, h]

theorem diagonal_zero_weight (k i j : Fin 5) :
    bracket (E k k) (E i j) =
      (zeroWeight i j k : ℝ) • E i j := by
  rw [E_bracket]
  by_cases hki : k = i
  · subst i
    by_cases hkj : k = j
    · subst j
      simp [zeroWeight]
    · simp [zeroWeight, hkj]
  · by_cases hkj : k = j
    · subst j
      simp [zeroWeight, hki]
    · simp [zeroWeight, hki, hkj]

theorem diagonal_positiveTwo_weight (k i j : Fin 5) :
    bracket (E k k) (creation i * creation j) =
      (positiveTwoWeight i j k : ℝ) • (creation i * creation j) := by
  rw [E_creation_quadratic_bracket]
  by_cases hki : k = i
  · subst i
    by_cases hkj : k = j
    · subst j
      simp [positiveTwoWeight, creation_same_site_sq]
    · simp [positiveTwoWeight, hkj]
  · by_cases hkj : k = j
    · subst j
      have hanti : creation i * creation k = -(creation k * creation i) := by
        exact eq_neg_of_add_eq_zero_right
          (by simpa [add_comm] using creation_anticomm i k)
      simp [positiveTwoWeight, hki, hanti]
    · simp [positiveTwoWeight, hki, hkj]

theorem diagonal_negativeTwo_weight (k i j : Fin 5) :
    bracket (E k k) (annihilation i * annihilation j) =
      (negativeTwoWeight i j k : ℝ) • (annihilation i * annihilation j) := by
  rw [E_annihilation_quadratic_bracket]
  by_cases hki : k = i
  · subst i
    by_cases hkj : k = j
    · subst j
      simp [negativeTwoWeight, annihilation_same_site_sq]
    · simp [negativeTwoWeight, hkj]
  · by_cases hkj : k = j
    · subst j
      have hanti : annihilation i * annihilation k =
          -(annihilation k * annihilation i) := by
        exact eq_neg_of_add_eq_zero_right
          (by simpa [add_comm] using annihilation_anticomm i k)
      simp [negativeTwoWeight, hki, hanti]
    · simp [negativeTwoWeight, hki, hkj]

end InfoGeometry.Canonical.Cl55WittLieRouting
