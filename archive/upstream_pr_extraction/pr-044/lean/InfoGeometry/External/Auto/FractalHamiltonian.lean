import Mathlib.Tactic

/-!
# Fibonacci / golden q fractal Hamiltonian anchors

A finite theorem-honest dynamic anchor for the proposed golden q-CCR/Fibonacci
-/

noncomputable section

namespace FractalHamiltonian

open Matrix

/-- Golden ratio. -/
def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- Golden q parameter `φ⁻¹`. -/
def qPenrose : ℝ := phi⁻¹

/-- Gap-label value `m+nφ`. -/
def gapLabel (m n : ℤ) : ℝ := (m : ℝ) + (n : ℝ) * phi

/-- Golden-ratio equation. -/
theorem phi_sq_eq_phi_add_one : phi ^ 2 = phi + 1 := by
  unfold phi
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith [hs]

/-- `φ>0`. -/
theorem phi_pos : 0 < phi := by
  unfold phi
  positivity

/-- `φ>1`. -/
theorem one_lt_phi : 1 < phi := by
  unfold phi
  have hs : (Real.sqrt 5)^2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

/-- The golden hopping/Toeplitz shift on two states. -/
def shift2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0;
     1, 0]

/-- Symmetric nearest-neighbor hopping term `S+Sᵀ`, written explicitly so the
finite anchor compiles independently of matrix-transpose simp details. -/
def hopping2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1;
     1, 0]

/-- Diagonal Fibonacci potential: thick sector has weight `1`, thin sector `φ⁻¹`. -/
def fibPotential2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0;
     0, qPenrose]

/-- Finite tight-binding Fibonacci Hamiltonian anchor: hopping plus diagonal
quasiperiodic potential. -/
def fibHamiltonian2 : Matrix (Fin 2) (Fin 2) ℝ :=
  hopping2 + fibPotential2

/-- The finite Hamiltonian is symmetric/self-adjoint in the real matrix model. -/
theorem fibHamiltonian2_symmetric : fibHamiltonian2ᵀ = fibHamiltonian2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fibHamiltonian2, hopping2, fibPotential2]

/-- Explicit matrix form of the finite Fibonacci Hamiltonian. -/
theorem fibHamiltonian2_eval :
    fibHamiltonian2 = !![1, 1; 1, qPenrose] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fibHamiltonian2, hopping2, fibPotential2]

/-- Trace of the finite Hamiltonian is `1+φ⁻¹`. -/
theorem fibHamiltonian2_trace : fibHamiltonian2.trace = 1 + qPenrose := by
  rw [fibHamiltonian2_eval]
  simp [qPenrose]

/-- Determinant of the finite Hamiltonian anchor. -/
theorem fibHamiltonian2_det : fibHamiltonian2.det = qPenrose - 1 := by
  rw [fibHamiltonian2_eval]
  simp [qPenrose]

/-- The golden q coefficient is a gap-label value: `φ⁻¹=-1+φ`. -/
theorem qPenrose_eq_gapLabel : qPenrose = gapLabel (-1) 1 := by
  unfold qPenrose gapLabel
  have hphi : phi ≠ 0 := ne_of_gt phi_pos
  field_simp [hphi]
  norm_num
  calc
    1 = phi ^ 2 - phi := by
      rw [phi_sq_eq_phi_add_one]
      ring
    _ = phi * (-1 + phi) := by ring

/-- Finite anchors available for the golden Hamiltonian pipeline. -/
theorem finite_hamiltonian_anchors :
    fibHamiltonian2ᵀ = fibHamiltonian2 ∧
    fibHamiltonian2.trace = 1 + qPenrose ∧
    fibHamiltonian2.det = qPenrose - 1 ∧
    qPenrose = gapLabel (-1) 1 := by
  exact ⟨fibHamiltonian2_symmetric, fibHamiltonian2_trace,
    fibHamiltonian2_det, qPenrose_eq_gapLabel⟩

end FractalHamiltonian
