import Mathlib

noncomputable section

namespace SarsChiralMassDilaton

open Real

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

def PR : M2R := !![1, 0; 0, 0]
def PL : M2R := !![0, 0; 0, 1]
def I2 : M2R := 1
def Jmod : M2R := !![0, 1; 1, 0]
def diracMassCoupling (m : ℝ) : M2R := m • Jmod

def diagBlock (A : M2R) : M2R := !![A 0 0, 0; 0, A 1 1]
def offBlock (A : M2R) : M2R := !![0, A 0 1; A 1 0, 0]

@[simp] theorem projectors_orthogonal : PR * PL = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [PR, PL]

@[simp] theorem projectors_sum_identity : PR + PL = I2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [PR, PL, I2]

@[simp] theorem tomita_swaps_left_right : Jmod * PL * Jmod = PR := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [Jmod, PL, PR, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem tomita_swaps_right_left : Jmod * PR * Jmod = PL := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [Jmod, PR, PL, Matrix.mul_apply, Fin.sum_univ_two]

theorem diracMassCoupling_matrix (m : ℝ) :
    diracMassCoupling m = !![0, m; m, 0] := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [diracMassCoupling, Jmod]

@[simp] theorem diracMassCoupling_diag_zero (m : ℝ) :
    diagBlock (diracMassCoupling m) = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [diagBlock, diracMassCoupling, Jmod]

@[simp] theorem diracMassCoupling_offblock_self (m : ℝ) :
    offBlock (diracMassCoupling m) = diracMassCoupling m := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [offBlock, diracMassCoupling, Jmod]

def dilaton (lam : ℝ) : ℝ := Real.exp lam
def localMass (m0 lam : ℝ) : ℝ := m0 * dilaton lam
def comptonScale (hbar c m : ℝ) : ℝ := hbar / (m * c)
/- The rest-gap frequency scale is owned by
`InfoGeometry.Canonical.ZitterbewegungMassEmergence.comptonFrequency`.
This local module does not identify a gap with an observable oscillation. -/

theorem localMass_zero_base (lam : ℝ) : localMass 0 lam = 0 := by simp [localMass]

theorem localMass_positive {m0 lam : ℝ} (hm0 : 0 < m0) : 0 < localMass m0 lam := by
  unfold localMass dilaton
  exact mul_pos hm0 (Real.exp_pos lam)

def springPotential (m lam : ℝ) : ℝ := (m^2 * lam^2) / 2
def restoringForce (m lam : ℝ) : ℝ := - m^2 * lam

theorem springPotential_nonneg (m lam : ℝ) : 0 ≤ springPotential m lam := by
  unfold springPotential
  positivity

theorem springPotential_zero_at_vacuum (m : ℝ) : springPotential m 0 = 0 := by
  norm_num [springPotential]

theorem restoringForce_hooke (m lam : ℝ) : restoringForce m lam = - m^2 * lam := rfl

def localEntropyQuadratic (x : ℝ) : ℝ := x^2 / 2

theorem localEntropyQuadratic_nonneg (x : ℝ) : 0 ≤ localEntropyQuadratic x := by
  unfold localEntropyQuadratic
  positivity

theorem localEntropyQuadratic_zero : localEntropyQuadratic 0 = 0 := by
  norm_num [localEntropyQuadratic]

/-! The former Boolean edge table conflated a rest-energy splitting with
observable Zitterbewegung. The valid finite-dimensional statement is the
characteristic polynomial below; velocity dynamics is formalized separately
in `InfoGeometry.Physics.DiracRest`. -/

theorem diracMassCoupling_characteristic_polynomial (m E : ℝ) :
    Matrix.det (diracMassCoupling m - E • I2) = (E - m) * (E + m) := by
  rw [diracMassCoupling_matrix]
  simp [I2, Matrix.det_fin_two]
  ring

theorem chiral_mass_dilaton_kernel :
    PR * PL = 0 ∧
    PR + PL = I2 ∧
    Jmod * PL * Jmod = PR ∧
    (∀ m : ℝ, diracMassCoupling m = !![0, m; m, 0]) ∧
    (∀ m : ℝ, diagBlock (diracMassCoupling m) = 0) ∧
    (∀ m : ℝ, offBlock (diracMassCoupling m) = diracMassCoupling m) ∧
    (∀ lam : ℝ, localMass 0 lam = 0) ∧
    (∀ m lam : ℝ, 0 ≤ springPotential m lam) ∧
    (∀ m : ℝ, springPotential m 0 = 0) ∧
    (∀ x : ℝ, 0 ≤ localEntropyQuadratic x) ∧
    localEntropyQuadratic 0 = 0 := by
  exact ⟨projectors_orthogonal, projectors_sum_identity, tomita_swaps_left_right,
    diracMassCoupling_matrix, diracMassCoupling_diag_zero, diracMassCoupling_offblock_self,
    localMass_zero_base, springPotential_nonneg, springPotential_zero_at_vacuum,
    localEntropyQuadratic_nonneg, localEntropyQuadratic_zero⟩

end SarsChiralMassDilaton

end noncomputable section
