import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Qutrits

A qutrit is modeled by the three-dimensional complex Euclidean space
`EuclideanSpace ℂ (Fin 3)`.  Normalized pure states are its unit sphere, and
single-qutrit gates are Mathlib's native `3 × 3` unitary matrices.

The computational kets reuse the finite matrix adapter's coordinate kets.  The
main results give their orthonormality, the three-amplitude expansion and
normalization law, the dimension of finite qutrit registers, and the unitary
global-phase gate.
-/

noncomputable section

namespace InfoGeometry.Quantum.Qutrit

open Matrix
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix

/-- The three-dimensional complex Hilbert space of one qutrit. -/
abbrev QutritSpace : Type := FinKetSpace (Fin 3)

/-- Normalized qutrit vectors. -/
abbrev QutritState : Type := Metric.sphere (0 : QutritSpace) 1

/-- Single-qutrit gates, represented by Mathlib's unitary group `U(3)`. -/
abbrev QutritGate : Type := Matrix.unitaryGroup (Fin 3) ℂ

/-- Computational basis labels for an `n`-qutrit register. -/
abbrev QutritRegisterIndex (n : ℕ) : Type := Fin n → Fin 3

/-- The finite coordinate Hilbert space of an `n`-qutrit computational register. -/
abbrev QutritRegisterSpace (n : ℕ) : Type :=
  FinKetSpace (QutritRegisterIndex n)

/-- An `n`-qutrit computational basis has `3^n` labels. -/
theorem qutritRegisterIndex_card (n : ℕ) :
    Fintype.card (QutritRegisterIndex n) = 3 ^ n := by
  simp [QutritRegisterIndex]

/-- The computational register realization has complex dimension `3^n`. -/
theorem qutritRegisterSpace_finrank (n : ℕ) :
    Module.finrank ℂ (QutritRegisterSpace n) = 3 ^ n := by
  simp [QutritRegisterSpace, QutritRegisterIndex]

/-- The computational ket `|i⟩`. -/
def ket (i : Fin 3) : QutritSpace :=
  EuclideanSpace.basisFun (Fin 3) ℂ i

/-- The qutrit ket is the generic finite-coordinate ket from the matrix owner. -/
@[simp] theorem ket_eq_ketPi (i : Fin 3) : ket i = ketPi i := by
  simp [ket, ketPi]

/-- The three computational kets form an orthonormal family. -/
theorem ket_orthonormal : Orthonormal ℂ ket := by
  exact (EuclideanSpace.basisFun (Fin 3) ℂ).orthonormal

/-- Every qutrit vector is the sum of its three computational amplitudes. -/
theorem superposition (ψ : QutritSpace) :
    ∑ i, ψ i • ket i = ψ := by
  simpa [ket, ketPi] using
    (EuclideanSpace.basisFun (Fin 3) ℂ).sum_repr ψ

/-- Explicit `α|0⟩ + β|1⟩ + γ|2⟩` form of a qutrit vector. -/
theorem superposition_three (ψ : QutritSpace) :
    ψ = ψ 0 • ket 0 + ψ 1 • ket 1 + ψ 2 • ket 2 := by
  calc
    ψ = ∑ i, ψ i • ket i := (superposition ψ).symm
    _ = ψ 0 • ket 0 + ψ 1 • ket 1 + ψ 2 • ket 2 := Fin.sum_univ_three _

/-- Coordinate normalization of a pure qutrit state. -/
theorem state_normalization (ψ : QutritState) :
    ∑ i, ‖(ψ : QutritSpace) i‖ ^ 2 = 1 := by
  rw [← EuclideanSpace.norm_sq_eq]
  have hnorm : ‖(ψ : QutritSpace)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp ψ.property
  rw [hnorm]
  norm_num

/-- Explicit three-amplitude normalization law. -/
theorem state_normalization_three (ψ : QutritState) :
    ‖(ψ : QutritSpace) 0‖ ^ 2 + ‖(ψ : QutritSpace) 1‖ ^ 2 +
      ‖(ψ : QutritSpace) 2‖ ^ 2 = 1 := by
  simpa only [Fin.sum_univ_three] using state_normalization ψ

/-- The complex phase `exp(iδ)`. -/
def phase (δ : ℝ) : ℂ := Complex.exp (δ * Complex.I)

@[simp] theorem norm_phase (δ : ℝ) : ‖phase δ‖ = 1 := by
  simp [phase]

/-- The scalar `3 × 3` global-phase matrix `exp(iδ) I`. -/
def globalPhaseMatrix (δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  phase δ • 1

/-- The global-phase matrix multiplies every qutrit amplitude by `exp(iδ)`. -/
@[simp] theorem globalPhaseMatrix_apply (δ : ℝ) (ψ : QutritSpace) :
    matrixOp (globalPhaseMatrix δ) ψ = phase δ • ψ := by
  ext i
  rw [matrixOp_apply]
  simp [globalPhaseMatrix, Matrix.smul_mulVec]

/-- The global-phase matrix is unitary. -/
theorem globalPhaseMatrix_mem_unitary (δ : ℝ) :
    globalPhaseMatrix δ ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  have hphase : star (phase δ) * phase δ = 1 := by
    change (starRingEnd ℂ) (phase δ) * phase δ = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, norm_phase]
    norm_num
  rw [Matrix.mem_unitaryGroup_iff']
  calc
    star (globalPhaseMatrix δ) * globalPhaseMatrix δ =
        (star (phase δ) * phase δ) •
          (star (1 : Matrix (Fin 3) (Fin 3) ℂ) * 1) := by
      rw [globalPhaseMatrix, star_smul, smul_mul_smul]
    _ = 1 := by rw [hphase]; simp

/-- The global phase bundled as a genuine element of `U(3)`. -/
def globalPhaseGate (δ : ℝ) : QutritGate :=
  ⟨globalPhaseMatrix δ, globalPhaseMatrix_mem_unitary δ⟩

/-- Global phase sends normalized qutrit vectors to normalized qutrit vectors. -/
def globalPhaseAct (δ : ℝ) (ψ : QutritState) : QutritState :=
  ⟨matrixOp (globalPhaseMatrix δ) ψ, by
    rw [mem_sphere_zero_iff_norm, globalPhaseMatrix_apply, norm_smul, norm_phase]
    simp [mem_sphere_zero_iff_norm.mp ψ.property]⟩

end InfoGeometry.Quantum.Qutrit
