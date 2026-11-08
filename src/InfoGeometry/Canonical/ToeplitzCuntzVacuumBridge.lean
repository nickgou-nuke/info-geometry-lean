import Mathlib.Algebra.Star.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.NoncommRing

/-!
# InfoGeometry.Canonical.ToeplitzCuntzVacuumBridge

Pure algebraic Toeplitz-Cuntz (*)-ring carrier, defect projection P₀,
and algebraic vacuum-sector restoration of Supersymmetry (SUSY QM).

In pure Cuntz 𝒪₂, V₁ V₁* + V₂ V₂* = 1, forcing H = {Q₊, Q₋} = 1 (spontaneous SUSY breaking).
In Toeplitz-Cuntz (*)-ring ℰ₂, V₁ V₁* + V₂ V₂* ≤ 1, introducing the orthogonal defect projector:
`P₀ := 1 - P₊ - P₋ = 1 - V₁ V₁* - V₂ V₂*`.

This restores the complete resolution of identity:
`P₊ + P₋ + P₀ = 1`
and yields the projector Hamiltonian `H = 1 - P₀` with exact bilateral vacuum-sector annihilation:
`Q₊ P₀ = 0`, `Q₋ P₀ = 0`, `H P₀ = 0`, `P₀ H = 0`, `P₀ Q₊ = 0`, `P₀ Q₋ = 0`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzVacuumBridge

variable {R : Type*} [Ring R] [StarRing R]

/-- Toeplitz-Cuntz ℰ₂ algebra generators for partial isometries V₁, V₂. -/
structure ToeplitzCuntzGenerators (R : Type*) [Ring R] [StarRing R] where
  V1 : R
  V2 : R
  V1_isometry : star V1 * V1 = 1
  V2_isometry : star V2 * V2 = 1
  V1_V2_orthogonal : star V1 * V2 = 0
  V2_V1_orthogonal : star V2 * V1 = 0

namespace ToeplitzCuntzGenerators

/-- Positive sector projector P₊ = V₁ V₁*. -/
def PPlus (g : ToeplitzCuntzGenerators R) : R := g.V1 * star g.V1

/-- Negative sector projector P₋ = V₂ V₂*. -/
def PMinus (g : ToeplitzCuntzGenerators R) : R := g.V2 * star g.V2

/-- Vacuum defect projector P₀ = 1 - P₊ - P₋. -/
def P0 (g : ToeplitzCuntzGenerators R) : R := 1 - PPlus g - PMinus g

/-- Positive Chiral Supercharge Q₊ = V₁ V₂*. -/
def QPlus (g : ToeplitzCuntzGenerators R) : R := g.V1 * star g.V2

/-- Negative Chiral Supercharge Q₋ = V₂ V₁*. -/
def QMinus (g : ToeplitzCuntzGenerators R) : R := g.V2 * star g.V1

/-- SUSY Projector Hamiltonian H = {Q₊, Q₋} = P₊ + P₋. -/
def susyHamiltonian (g : ToeplitzCuntzGenerators R) : R := QPlus g * QMinus g + QMinus g * QPlus g

/-- P₊ is idempotent: P₊² = P₊. -/
theorem pplus_idempotent (g : ToeplitzCuntzGenerators R) : PPlus g * PPlus g = PPlus g := by
  dsimp [PPlus]
  have h1 : g.V1 * star g.V1 * (g.V1 * star g.V1) = g.V1 * (star g.V1 * g.V1) * star g.V1 := by noncomm_ring
  rw [h1, g.V1_isometry, mul_one]

/-- P₋ is idempotent: P₋² = P₋. -/
theorem pminus_idempotent (g : ToeplitzCuntzGenerators R) : PMinus g * PMinus g = PMinus g := by
  dsimp [PMinus]
  have h1 : g.V2 * star g.V2 * (g.V2 * star g.V2) = g.V2 * (star g.V2 * g.V2) * star g.V2 := by noncomm_ring
  rw [h1, g.V2_isometry, mul_one]

/-- P₊ is self-adjoint: P₊* = P₊. -/
theorem pplus_star (g : ToeplitzCuntzGenerators R) : star (PPlus g) = PPlus g := by
  dsimp [PPlus]
  simp

/-- P₋ is self-adjoint: P₋* = P₋. -/
theorem pminus_star (g : ToeplitzCuntzGenerators R) : star (PMinus g) = PMinus g := by
  dsimp [PMinus]
  simp

/-- P₊ and P₋ are orthogonal: P₊ P₋ = 0. -/
theorem pplus_pminus_orthogonal (g : ToeplitzCuntzGenerators R) : PPlus g * PMinus g = 0 := by
  dsimp [PPlus, PMinus]
  have h1 : g.V1 * star g.V1 * (g.V2 * star g.V2) = g.V1 * (star g.V1 * g.V2) * star g.V2 := by noncomm_ring
  rw [h1, g.V1_V2_orthogonal, mul_zero, zero_mul]

/-- P₋ and P₊ are orthogonal: P₋ P₊ = 0. -/
theorem pminus_pplus_orthogonal (g : ToeplitzCuntzGenerators R) : PMinus g * PPlus g = 0 := by
  dsimp [PPlus, PMinus]
  have h1 : g.V2 * star g.V2 * (g.V1 * star g.V1) = g.V2 * (star g.V2 * g.V1) * star g.V1 := by noncomm_ring
  rw [h1, g.V2_V1_orthogonal, mul_zero, zero_mul]

/-- P₀ is idempotent: P₀² = P₀. -/
theorem defectProjection_sq (g : ToeplitzCuntzGenerators R) : P0 g * P0 g = P0 g := by
  have hpp : PPlus g * PPlus g = PPlus g := pplus_idempotent g
  have hmm : PMinus g * PMinus g = PMinus g := pminus_idempotent g
  have hpm : PPlus g * PMinus g = 0 := pplus_pminus_orthogonal g
  have hmp : PMinus g * PPlus g = 0 := pminus_pplus_orthogonal g
  dsimp [P0]
  calc (1 - PPlus g - PMinus g) * (1 - PPlus g - PMinus g)
      = 1 - PPlus g - PMinus g - PPlus g + PPlus g * PPlus g + PPlus g * PMinus g
        - PMinus g + PMinus g * PPlus g + PMinus g * PMinus g := by noncomm_ring
    _ = 1 - PPlus g - PMinus g - PPlus g + PPlus g + 0 - PMinus g + 0 + PMinus g := by
        rw [hpp, hmm, hpm, hmp]
    _ = 1 - PPlus g - PMinus g := by noncomm_ring

/-- P₀ is self-adjoint: P₀* = P₀. -/
theorem defectProjection_star (g : ToeplitzCuntzGenerators R) : star (P0 g) = P0 g := by
  dsimp [P0]
  simp [pplus_star g, pminus_star g]

/-- Resolution of identity: P₊ + P₋ + P₀ = 1. -/
theorem toeplitzCuntz_resolution (g : ToeplitzCuntzGenerators R) : PPlus g + PMinus g + P0 g = 1 := by
  dsimp [P0]
  noncomm_ring

/-- P₀ is orthogonal to P₊: P₀ P₊ = 0. -/
theorem p0_pplus_orthogonal (g : ToeplitzCuntzGenerators R) : P0 g * PPlus g = 0 := by
  have hpp := pplus_idempotent g
  have hmp := pminus_pplus_orthogonal g
  dsimp [P0]
  calc (1 - PPlus g - PMinus g) * PPlus g
      = PPlus g - PPlus g * PPlus g - PMinus g * PPlus g := by noncomm_ring
    _ = PPlus g - PPlus g - 0 := by rw [hpp, hmp]
    _ = 0 := by noncomm_ring

/-- P₀ is orthogonal to P₋: P₀ P₋ = 0. -/
theorem p0_pminus_orthogonal (g : ToeplitzCuntzGenerators R) : P0 g * PMinus g = 0 := by
  have hmm := pminus_idempotent g
  have hpm := pplus_pminus_orthogonal g
  dsimp [P0]
  calc (1 - PPlus g - PMinus g) * PMinus g
      = PMinus g - PPlus g * PMinus g - PMinus g * PMinus g := by noncomm_ring
    _ = PMinus g - 0 - PMinus g := by rw [hmm, hpm]
    _ = 0 := by noncomm_ring

/-- Positive supercharge nilpotency: Q₊² = 0. -/
theorem qplus_sq_zero (g : ToeplitzCuntzGenerators R) : QPlus g * QPlus g = 0 := by
  dsimp [QPlus]
  have h1 : g.V1 * star g.V2 * (g.V1 * star g.V2) = g.V1 * (star g.V2 * g.V1) * star g.V2 := by noncomm_ring
  rw [h1, g.V2_V1_orthogonal, mul_zero, zero_mul]

/-- Negative supercharge nilpotency: Q₋² = 0. -/
theorem qminus_sq_zero (g : ToeplitzCuntzGenerators R) : QMinus g * QMinus g = 0 := by
  dsimp [QMinus]
  have h1 : g.V2 * star g.V1 * (g.V2 * star g.V1) = g.V2 * (star g.V1 * g.V2) * star g.V1 := by noncomm_ring
  rw [h1, g.V1_V2_orthogonal, mul_zero, zero_mul]

/-- Product Q₊ Q₋ = P₊. -/
theorem qplus_qminus_eq_pplus (g : ToeplitzCuntzGenerators R) : QPlus g * QMinus g = PPlus g := by
  dsimp [QPlus, QMinus, PPlus]
  have h1 : g.V1 * star g.V2 * (g.V2 * star g.V1) = g.V1 * (star g.V2 * g.V2) * star g.V1 := by noncomm_ring
  rw [h1, g.V2_isometry, mul_one]

/-- Product Q₋ Q₊ = P₋. -/
theorem qminus_qplus_eq_pminus (g : ToeplitzCuntzGenerators R) : QMinus g * QPlus g = PMinus g := by
  dsimp [QPlus, QMinus, PMinus]
  have h1 : g.V2 * star g.V1 * (g.V1 * star g.V2) = g.V2 * (star g.V1 * g.V1) * star g.V2 := by noncomm_ring
  rw [h1, g.V1_isometry, mul_one]

/-- Adjoint relation Q₋ = Q₊*. -/
theorem qminus_eq_star_qplus (g : ToeplitzCuntzGenerators R) : QMinus g = star (QPlus g) := by
  dsimp [QMinus, QPlus]
  simp

/-- SUSY Hamiltonian identity: H = 1 - P₀. -/
theorem susyHamiltonian_eq_one_sub_vacuum (g : ToeplitzCuntzGenerators R) : susyHamiltonian g = 1 - P0 g := by
  have h1 := qplus_qminus_eq_pplus g
  have h2 := qminus_qplus_eq_pminus g
  dsimp [susyHamiltonian, P0]
  rw [h1, h2]
  noncomm_ring

/-- Hamiltonian is an idempotent projection: H² = H. -/
theorem susyHamiltonian_sq (g : ToeplitzCuntzGenerators R) : susyHamiltonian g * susyHamiltonian g = susyHamiltonian g := by
  have hH := susyHamiltonian_eq_one_sub_vacuum g
  have hp0 := defectProjection_sq g
  have hp0_p0 : (1 - P0 g) * (1 - P0 g) = 1 - P0 g := by
    calc (1 - P0 g) * (1 - P0 g) = 1 - P0 g - P0 g + P0 g * P0 g := by noncomm_ring
      _ = 1 - P0 g - P0 g + P0 g := by rw [hp0]
      _ = 1 - P0 g := by noncomm_ring
  rw [hH, hp0_p0]

/-- Hamiltonian is self-adjoint: H* = H. -/
theorem susyHamiltonian_star (g : ToeplitzCuntzGenerators R) : star (susyHamiltonian g) = susyHamiltonian g := by
  have hH := susyHamiltonian_eq_one_sub_vacuum g
  have hp0 := defectProjection_star g
  rw [hH]
  simp [hp0]

/-- Right vacuum annihilation by the Hamiltonian: H P₀ = 0. -/
theorem susyHamiltonian_vacuum_annihilation (g : ToeplitzCuntzGenerators R) : susyHamiltonian g * P0 g = 0 := by
  have hH := susyHamiltonian_eq_one_sub_vacuum g
  have hp0 := defectProjection_sq g
  rw [hH]
  dsimp [P0]
  calc (1 - P0 g) * P0 g = P0 g - P0 g * P0 g := by noncomm_ring
    _ = P0 g - P0 g := by rw [hp0]
    _ = 0 := by noncomm_ring

/-- Left vacuum annihilation by the Hamiltonian: P₀ H = 0. -/
theorem p0_susyHamiltonian_annihilation (g : ToeplitzCuntzGenerators R) : P0 g * susyHamiltonian g = 0 := by
  have hH := susyHamiltonian_eq_one_sub_vacuum g
  have hp0 := defectProjection_sq g
  rw [hH]
  dsimp [P0]
  calc P0 g * (1 - P0 g) = P0 g - P0 g * P0 g := by noncomm_ring
    _ = P0 g - P0 g := by rw [hp0]
    _ = 0 := by noncomm_ring

/-- Right vacuum annihilation by both supercharges: Q₊ P₀ = 0 and Q₋ P₀ = 0. -/
theorem supercharges_vacuum_annihilation (g : ToeplitzCuntzGenerators R) :
    QPlus g * P0 g = 0 ∧ QMinus g * P0 g = 0 := by
  have h1_sub : g.V1 * star g.V2 * (g.V1 * star g.V1) = 0 := by
    have h1 : g.V1 * star g.V2 * (g.V1 * star g.V1) = g.V1 * (star g.V2 * g.V1) * star g.V1 := by noncomm_ring
    rw [h1, g.V2_V1_orthogonal, mul_zero, zero_mul]
  have h1_sub2 : g.V1 * star g.V2 * (g.V2 * star g.V2) = QPlus g := by
    dsimp [QPlus]
    have h1 : g.V1 * star g.V2 * (g.V2 * star g.V2) = g.V1 * (star g.V2 * g.V2) * star g.V2 := by noncomm_ring
    rw [h1, g.V2_isometry, mul_one]
  have h2_sub : g.V2 * star g.V1 * (g.V1 * star g.V1) = QMinus g := by
    dsimp [QMinus]
    have h1 : g.V2 * star g.V1 * (g.V1 * star g.V1) = g.V2 * (star g.V1 * g.V1) * star g.V1 := by noncomm_ring
    rw [h1, g.V1_isometry, mul_one]
  have h2_sub2 : g.V2 * star g.V1 * (g.V2 * star g.V2) = 0 := by
    have h1 : g.V2 * star g.V1 * (g.V2 * star g.V2) = g.V2 * (star g.V1 * g.V2) * star g.V2 := by noncomm_ring
    rw [h1, g.V1_V2_orthogonal, mul_zero, zero_mul]
  constructor
  · dsimp [QPlus, P0, PPlus, PMinus]
    have hsplit : g.V1 * star g.V2 * (1 - g.V1 * star g.V1 - g.V2 * star g.V2)
                = g.V1 * star g.V2 - g.V1 * star g.V2 * (g.V1 * star g.V1) - g.V1 * star g.V2 * (g.V2 * star g.V2) := by noncomm_ring
    rw [hsplit, h1_sub, h1_sub2]
    dsimp [QPlus]
    noncomm_ring
  · dsimp [QMinus, P0, PPlus, PMinus]
    have hsplit : g.V2 * star g.V1 * (1 - g.V1 * star g.V1 - g.V2 * star g.V2)
                = g.V2 * star g.V1 - g.V2 * star g.V1 * (g.V1 * star g.V1) - g.V2 * star g.V1 * (g.V2 * star g.V2) := by noncomm_ring
    rw [hsplit, h2_sub, h2_sub2]
    dsimp [QMinus]
    noncomm_ring

/-- Left vacuum annihilation by both supercharges: P₀ Q₊ = 0 and P₀ Q₋ = 0. -/
theorem p0_supercharges_annihilation (g : ToeplitzCuntzGenerators R) :
    P0 g * QPlus g = 0 ∧ P0 g * QMinus g = 0 := by
  have h1_sub : g.V1 * star g.V1 * (g.V1 * star g.V2) = QPlus g := by
    dsimp [QPlus]
    have h1 : g.V1 * star g.V1 * (g.V1 * star g.V2) = g.V1 * (star g.V1 * g.V1) * star g.V2 := by noncomm_ring
    rw [h1, g.V1_isometry, mul_one]
  have h1_sub2 : g.V2 * star g.V2 * (g.V1 * star g.V2) = 0 := by
    have h1 : g.V2 * star g.V2 * (g.V1 * star g.V2) = g.V2 * (star g.V2 * g.V1) * star g.V2 := by noncomm_ring
    rw [h1, g.V2_V1_orthogonal, mul_zero, zero_mul]
  have h2_sub : g.V1 * star g.V1 * (g.V2 * star g.V1) = 0 := by
    have h1 : g.V1 * star g.V1 * (g.V2 * star g.V1) = g.V1 * (star g.V1 * g.V2) * star g.V1 := by noncomm_ring
    rw [h1, g.V1_V2_orthogonal, mul_zero, zero_mul]
  have h2_sub2 : g.V2 * star g.V2 * (g.V2 * star g.V1) = QMinus g := by
    dsimp [QMinus]
    have h1 : g.V2 * star g.V2 * (g.V2 * star g.V1) = g.V2 * (star g.V2 * g.V2) * star g.V1 := by noncomm_ring
    rw [h1, g.V2_isometry, mul_one]
  constructor
  · dsimp [QPlus, P0, PPlus, PMinus]
    have hsplit : (1 - g.V1 * star g.V1 - g.V2 * star g.V2) * (g.V1 * star g.V2)
                = g.V1 * star g.V2 - g.V1 * star g.V1 * (g.V1 * star g.V2) - g.V2 * star g.V2 * (g.V1 * star g.V2) := by noncomm_ring
    rw [hsplit, h1_sub, h1_sub2]
    dsimp [QPlus]
    noncomm_ring
  · dsimp [QMinus, P0, PPlus, PMinus]
    have hsplit : (1 - g.V1 * star g.V1 - g.V2 * star g.V2) * (g.V2 * star g.V1)
                = g.V2 * star g.V1 - g.V1 * star g.V1 * (g.V2 * star g.V1) - g.V2 * star g.V2 * (g.V2 * star g.V1) := by noncomm_ring
    rw [hsplit, h2_sub, h2_sub2]
    dsimp [QMinus]
    noncomm_ring

/- **Theorem**: Nontrivial Algebraic Vacuum Witness.
    When `P₀ ≠ 0`, the defect projector `p = P₀` serves as an explicit, nonzero witness
    annihilated bilaterally by H, Q₊, and Q₋. -/
/- theorem nontrivial_algebraic_vacuum_witness
    (g : ToeplitzCuntzGenerators R)
    (hP0 : P0 g ≠ 0) :
    ∃ p : R,
      p ≠ 0 ∧
      susyHamiltonian g * p = 0 ∧
      QPlus g * p = 0 ∧
      QMinus g * p = 0 := by
  use P0 g
  exact ⟨hP0,
         susyHamiltonian_vacuum_annihilation g,
         (supercharges_vacuum_annihilation g).1,
         (supercharges_vacuum_annihilation g).2⟩ -/

/- **Master Synthesis Theorem**: Pure Algebraic Toeplitz-Cuntz Vacuum & Defect-Sector Synthesis. -/
/- theorem master_toeplitz_cuntz_vacuum_synthesis (g : ToeplitzCuntzGenerators R) :
    P0 g * P0 g = P0 g ∧
    star (P0 g) = P0 g ∧
    PPlus g + PMinus g + P0 g = 1 ∧
    QPlus g * QPlus g = 0 ∧
    QMinus g * QMinus g = 0 ∧
    susyHamiltonian g = 1 - P0 g ∧
    susyHamiltonian g * P0 g = 0 ∧
    P0 g * susyHamiltonian g = 0 ∧
    (QPlus g * P0 g = 0 ∧ QMinus g * P0 g = 0) ∧
    (P0 g * QPlus g = 0 ∧ P0 g * QMinus g = 0) := by
  exact ⟨defectProjection_sq g,
         defectProjection_star g,
         toeplitzCuntz_resolution g,
         qplus_sq_zero g,
         qminus_sq_zero g,
         susyHamiltonian_eq_one_sub_vacuum g,
         susyHamiltonian_vacuum_annihilation g,
         p0_susyHamiltonian_annihilation g,
         supercharges_vacuum_annihilation g,
         p0_supercharges_annihilation g⟩ -/

end ToeplitzCuntzGenerators

end InfoGeometry.Canonical.ToeplitzCuntzVacuumBridge
