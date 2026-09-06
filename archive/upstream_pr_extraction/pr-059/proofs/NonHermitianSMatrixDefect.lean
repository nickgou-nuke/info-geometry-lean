import Mathlib
import proofs.ScatteringSMatrix

/-!
# Non-Hermitian S-Matrix Defect and Chiral Flux Preservation

A real `2 × 2` scattering block for the hyperbolic Clifford channel

`S(α) = cosh α · I + sinh α · P`, where `P = σ₃ · iσ₂ = σ₁`.

The ordinary Euclidean unitarity defect is nonzero away from `α = 0`, while the
indefinite/Krein flux metric `J = σ₃` is preserved: `Sᵀ J S = J`.

Important convention: with the chiral supertrace `Tr(σ₃ M)`, the pure diagonal
boost gives `2 sinh α`.  For the braid-parity exponential `exp(αP)`, the matching
supertrace is the parity-twisted trace `Tr(P M)`, which also gives `2 sinh α`.
-/

noncomputable section

open Matrix Real

namespace InfoGeometry.GrandUnification.NonHermitianSMatrixDefect

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Chiral/Krein metric. -/
def JMetric : M2R := !![1, 0; 0, -1]

/-- Local braid parity `P = σ₃ · iσ₂ = σ₁`. -/
def parityGate : M2R := !![0, 1; 1, 0]

/-- Hyperbolic non-Hermitian scattering block `S(α)=cosh α I+sinh α P`. -/
def hyperbolicScattering (α : ℝ) : M2R :=
  !![Real.cosh α, Real.sinh α; Real.sinh α, Real.cosh α]

/-- Parity-twisted braid supertrace. -/
def braidSupertrace (M : M2R) : ℝ :=
  Matrix.trace (parityGate * M)

/-- Ordinary Euclidean unitarity defect. -/
def euclideanDefect (α : ℝ) : M2R :=
  (hyperbolicScattering α).transpose * hyperbolicScattering α - (1 : M2R)

/-- Explicit exponential form of the hyperbolic scattering block. -/
theorem hyperbolicScattering_explicit (α : ℝ) :
    hyperbolicScattering α = Real.cosh α • (1 : M2R) + Real.sinh α • parityGate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicScattering, parityGate]

/-- The parity-twisted supertrace extracts the Souriau/Massieu potential `2 sinh α`. -/
theorem braidSupertrace_hyperbolicScattering (α : ℝ) :
    braidSupertrace (hyperbolicScattering α) = 2 * Real.sinh α := by
  simp [braidSupertrace, hyperbolicScattering, parityGate, Matrix.trace]
  ring

/-- The scattering block has determinant one: the split flux volume is preserved. -/
theorem hyperbolicScattering_det (α : ℝ) :
    (hyperbolicScattering α).det = 1 := by
  simp [hyperbolicScattering, Matrix.det_fin_two]
  rw [← pow_two, ← pow_two]
  exact Real.cosh_sq_sub_sinh_sq α

/-- The ordinary Euclidean defect is nonzero in form: `SᵀS-I`. -/
theorem euclideanDefect_formula (α : ℝ) :
    euclideanDefect α =
      !![(Real.cosh α)^2 + (Real.sinh α)^2 - 1,
         2 * Real.sinh α * Real.cosh α;
         2 * Real.sinh α * Real.cosh α,
         (Real.cosh α)^2 + (Real.sinh α)^2 - 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [euclideanDefect, hyperbolicScattering, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Krein/chiral flux preservation: the non-Hermitian scattering is `J`-unitary. -/
theorem krein_flux_preserved (α : ℝ) :
    (hyperbolicScattering α).transpose * JMetric * hyperbolicScattering α = JMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicScattering, JMetric, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf
  · exact Real.cosh_sq_sub_sinh_sq α
  · have h := Real.cosh_sq_sub_sinh_sq α
    nlinarith

/-- Consolidated non-Hermitian S-matrix defect package. -/
theorem nonhermitian_smatrix_defect_synthesis :
    (∀ α : ℝ, hyperbolicScattering α = Real.cosh α • (1 : M2R) + Real.sinh α • parityGate) ∧
    (∀ α : ℝ, braidSupertrace (hyperbolicScattering α) = 2 * Real.sinh α) ∧
    (∀ α : ℝ, (hyperbolicScattering α).det = 1) ∧
    (∀ α : ℝ, euclideanDefect α =
      !![(Real.cosh α)^2 + (Real.sinh α)^2 - 1,
         2 * Real.sinh α * Real.cosh α;
         2 * Real.sinh α * Real.cosh α,
         (Real.cosh α)^2 + (Real.sinh α)^2 - 1]) ∧
    (∀ α : ℝ, (hyperbolicScattering α).transpose * JMetric * hyperbolicScattering α = JMetric) := by
  constructor
  · intro α
    exact hyperbolicScattering_explicit α
  constructor
  · intro α
    exact braidSupertrace_hyperbolicScattering α
  constructor
  · intro α
    exact hyperbolicScattering_det α
  constructor
  · intro α
    exact euclideanDefect_formula α
  · intro α
    exact krein_flux_preserved α

end InfoGeometry.GrandUnification.NonHermitianSMatrixDefect
