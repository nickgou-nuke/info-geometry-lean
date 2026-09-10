import InfoGeometry.Quantum.Qutrit
import InfoGeometry.Physics.MD014TriSpinZ3Projectors
import InfoGeometry.Physics.HestenesCuntzPhaseSpace
import InfoGeometry.Physics.GellMannSU3
import InfoGeometry.Topology.ArtinBraidS3Quotient
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.RollingSpinorMobiusBridge
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Qutrit braid/incidence bridge

This module connects already-formalized finite qutrit data to the generic
incidence-action layer.

It proves only finite algebraic facts:

* the `Z₃` sector phase from `MD014TriSpinZ3Projectors` is the qutrit clock;
* an explicit cyclic shift matrix has cube `1`;
* clock and shift satisfy the finite Weyl relation under `ω³ = 1`;
* the three sector projectors fix the three computational kets;
* the concrete `S₃` Artin quotient acts on qutrit-label incidence.

It does not claim a Fibonacci-anyon universality theorem, a full `CP²`
projective-space theory, or a physical parafermion model.
-/

noncomputable section

namespace InfoGeometry.Quantum.QutritBraidIncidenceBridge

set_option linter.unusedSimpArgs false

open Matrix
open InfoGeometry.Quantum.Qutrit
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix
open InfoGeometry.Physics.MD014TriSpinZ3Projectors
open InfoGeometry.Physics.HestenesCuntzPhaseSpace
open InfoGeometry.Physics.GellMannSU3
open InfoGeometry.Topology.ArtinBraidS3Quotient
open InfoGeometry.Twistor.RollingSpinorMobiusBridge

/-- Concrete `3 × 3` qutrit matrix carrier. -/
abbrev QutritMatrix := InfoGeometry.Algebra.FiniteSpin.QutritMatrix

/-- The rank-one computational-ket projector `|i⟩⟨i|`.

Since computational ket coordinates are `0` and `1`, no analytic Hilbert-space
adjoint is needed for this finite algebraic readout. -/
def qutritKetProjector (i : Fin 3) : QutritMatrix :=
  fun j k => ket i j * ket i k

/-- Permutation matrix whose action on qutrit kets follows the label permutation.

Mathlib's `permMatrix` convention sends `|i⟩` to `|σ⁻¹ i⟩`, so this bridge uses
`σ.symm` in the matrix to realize the semantic action `|i⟩ ↦ |σ i⟩`. -/
def qutritPermutationMatrix (σ : Equiv.Perm (Fin 3)) : QutritMatrix :=
  Equiv.Perm.permMatrix ℂ σ.symm

/-- The semantic qutrit cycle `0 ↦ 1 ↦ 2 ↦ 0`. -/
def qutritCycle : Equiv.Perm (Fin 3) where
  toFun := fun i =>
    match i with
    | ⟨0, _⟩ => 1
    | ⟨1, _⟩ => 2
    | ⟨2, _⟩ => 0
  invFun := fun i =>
    match i with
    | ⟨0, _⟩ => 2
    | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => 1
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

@[simp] theorem qutritCycle_zero : qutritCycle 0 = 1 := rfl
@[simp] theorem qutritCycle_one : qutritCycle 1 = 2 := rfl
@[simp] theorem qutritCycle_two : qutritCycle 2 = 0 := rfl

/-- Cyclic qutrit shift `|0⟩ ↦ |1⟩`, `|1⟩ ↦ |2⟩`, `|2⟩ ↦ |0⟩`. -/
def qutritShiftMatrix : QutritMatrix :=
  ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]

/-- The cube of the qutrit label cycle is the identity. -/
theorem qutritCycle_cube_identity :
    qutritCycle * qutritCycle * qutritCycle = 1 := by
  apply Equiv.ext
  intro i
  fin_cases i <;> rfl

/-- The semantic qutrit cycle is realized by the explicit cyclic-shift matrix. -/
theorem qutritPermutationMatrix_qutritCycle :
    qutritPermutationMatrix qutritCycle = qutritShiftMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qutritPermutationMatrix, Equiv.Perm.permMatrix, qutritCycle, qutritShiftMatrix]

/-- The explicit cyclic-shift matrix is the permutation matrix of the qutrit label cycle. -/
theorem qutritShiftMatrix_eq_qutritPermutationMatrix_qutritCycle :
    qutritShiftMatrix = qutritPermutationMatrix qutritCycle :=
  qutritPermutationMatrix_qutritCycle.symm

/-- The cube of the cyclic qutrit shift is the identity. -/
theorem qutritShift_cube_identity :
    qutritShiftMatrix * qutritShiftMatrix * qutritShiftMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qutritShiftMatrix, Matrix.mul_apply, Fin.sum_univ_three]

/-- Generalized qutrit Pauli `X`: the finite cyclic shift. -/
def qutritGeneralizedPauliX : QutritMatrix :=
  qutritShiftMatrix

/-- Generalized qutrit Pauli `Z` with formal cubic phase `ω`: the finite sector clock. -/
def qutritGeneralizedPauliZ (ω : ℂ) : QutritMatrix :=
  sectorPhase ω

/-- The generalized qutrit Pauli `X` is exactly the explicit cyclic-shift matrix. -/
theorem qutritGeneralizedPauliX_eq_shift :
    qutritGeneralizedPauliX = qutritShiftMatrix :=
  rfl

/-- The generalized qutrit Pauli `Z` is exactly the `MD014` sector phase. -/
theorem qutritGeneralizedPauliZ_eq_sectorPhase (ω : ℂ) :
    qutritGeneralizedPauliZ ω = sectorPhase ω :=
  rfl

/-- The cube of the generalized qutrit Pauli `X` is the identity. -/
theorem qutritGeneralizedPauliX_cube_identity :
    qutritGeneralizedPauliX * qutritGeneralizedPauliX * qutritGeneralizedPauliX = 1 :=
  qutritShift_cube_identity

/-- The `MD014` sector phase is the qutrit clock and has cube `1` when `ω³=1`. -/
theorem qutritClock_cube_identity (ω : ℂ) (hω : ω ^ 3 = 1) :
    sectorPhase ω * sectorPhase ω * sectorPhase ω = 1 :=
  sectorPhase_cube_identity ω hω

/-- The cube of the generalized qutrit Pauli `Z` is the identity whenever `ω³ = 1`. -/
theorem qutritGeneralizedPauliZ_cube_identity (ω : ℂ) (hω : ω ^ 3 = 1) :
    qutritGeneralizedPauliZ ω * qutritGeneralizedPauliZ ω * qutritGeneralizedPauliZ ω = 1 :=
  qutritClock_cube_identity ω hω

/-- The qutrit clock and cyclic shift satisfy the finite Weyl relation. -/
theorem qutrit_clock_shift_weyl (ω : ℂ) (hω : ω ^ 3 = 1) :
    sectorPhase ω * qutritShiftMatrix = ω • (qutritShiftMatrix * sectorPhase ω) := by
  have hmul : ω * ω * ω = 1 := by
    calc
      ω * ω * ω = ω ^ 3 := by ring
      _ = 1 := hω
  have hpow : ω * ω ^ 2 = 1 := by
    calc
      ω * ω ^ 2 = ω ^ 3 := by ring
      _ = 1 := hω
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorPhase, sectorProjector0, sectorProjector1,
      sectorProjector2, qutritShiftMatrix, Matrix.mul_apply, hpow, hmul]
  all_goals first | exact hpow.symm | ring_nf

/-- The first `MD014` sector projector is the rank-one ket projector `|0⟩⟨0|`. -/
theorem sectorProjector0_eq_qutritKetProjector :
    sectorProjector0 = qutritKetProjector 0 := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [qutritKetProjector, ket, sectorProjector0]

/-- The second `MD014` sector projector is the rank-one ket projector `|1⟩⟨1|`. -/
theorem sectorProjector1_eq_qutritKetProjector :
    sectorProjector1 = qutritKetProjector 1 := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [qutritKetProjector, ket, sectorProjector1]

/-- The third `MD014` sector projector is the rank-one ket projector `|2⟩⟨2|`. -/
theorem sectorProjector2_eq_qutritKetProjector :
    sectorProjector2 = qutritKetProjector 2 := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [qutritKetProjector, ket, sectorProjector2]

/-- Computational-ket projectors pick out their matching ket and kill the other two. -/
theorem qutritKetProjector_matrixOp_ket (i j : Fin 3) :
    matrixOp (qutritKetProjector i) (ket j) = if i = j then ket i else 0 := by
  fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;>
    simp [matrixOp_apply, qutritKetProjector, ket, Matrix.mulVec, Fin.sum_univ_three]

/-- The `MD014` clock is the weighted sum of computational ket projectors. -/
theorem sectorPhase_eq_qutritKetProjector_sum (ω : ℂ) :
    sectorPhase ω =
      qutritKetProjector 0 + ω • qutritKetProjector 1 + (ω ^ 2) • qutritKetProjector 2 := by
  rw [← sectorProjector0_eq_qutritKetProjector,
    ← sectorProjector1_eq_qutritKetProjector,
    ← sectorProjector2_eq_qutritKetProjector]
  rfl

/-- The diagonal Gell-Mann observable `λ₃` is the difference of the first two
qutrit sector projectors. -/
theorem gellMann_gl3_sectorProjectors :
    gl3 = sectorProjector0 - sectorProjector1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl3, sectorProjector0, sectorProjector1]

/-- The diagonal Gell-Mann observable `λ₈` is the finite qutrit sector readout
`P₀ + P₁ - 2P₂` in this repository's unnormalized convention. -/
theorem gellMann_gl8_sectorProjectors :
    gl8 = sectorProjector0 + sectorProjector1 - (2 : ℂ) • sectorProjector2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl8, sectorProjector0, sectorProjector1, sectorProjector2]

/-- Sector projector `P₀` fixes the computational ket `|0⟩`. -/
theorem sectorProjector0_matrixOp_ket0 :
    matrixOp sectorProjector0 (ket 0) = ket 0 := by
  ext i
  fin_cases i <;>
    simp [matrixOp_apply, ket, sectorProjector0, Matrix.mulVec, Fin.sum_univ_three]

/-- Sector projector `P₁` fixes the computational ket `|1⟩`. -/
theorem sectorProjector1_matrixOp_ket1 :
    matrixOp sectorProjector1 (ket 1) = ket 1 := by
  ext i
  fin_cases i <;>
    simp [matrixOp_apply, ket, sectorProjector1, Matrix.mulVec, Fin.sum_univ_three]

/-- Sector projector `P₂` fixes the computational ket `|2⟩`. -/
theorem sectorProjector2_matrixOp_ket2 :
    matrixOp sectorProjector2 (ket 2) = ket 2 := by
  ext i
  fin_cases i <;>
    simp [matrixOp_apply, ket, sectorProjector2, Matrix.mulVec, Fin.sum_univ_three]

/-- The qutrit clock fixes the `|0⟩` sector. -/
theorem sectorPhase_matrixOp_ket0 (ω : ℂ) :
    matrixOp (sectorPhase ω) (ket 0) = ket 0 := by
  ext i
  fin_cases i <;>
    simp [matrixOp_apply, ket, sectorPhase, sectorProjector0, sectorProjector1,
      sectorProjector2, Matrix.mulVec, Fin.sum_univ_three]

/-- The qutrit clock has eigenvalue `ω` on the `|1⟩` sector. -/
theorem sectorPhase_matrixOp_ket1 (ω : ℂ) :
    matrixOp (sectorPhase ω) (ket 1) = ω • ket 1 := by
  ext i
  fin_cases i <;>
    simp [matrixOp_apply, ket, sectorPhase, sectorProjector0, sectorProjector1,
      sectorProjector2, Matrix.mulVec, Fin.sum_univ_three]

/-- The qutrit clock has eigenvalue `ω²` on the `|2⟩` sector. -/
theorem sectorPhase_matrixOp_ket2 (ω : ℂ) :
    matrixOp (sectorPhase ω) (ket 2) = (ω ^ 2) • ket 2 := by
  ext i
  fin_cases i <;>
    simp [matrixOp_apply, ket, sectorPhase, sectorProjector0, sectorProjector1,
      sectorProjector2, Matrix.mulVec, Fin.sum_univ_three]

/-- The three computational kets diagonalize the qutrit clock. -/
theorem sectorPhase_computational_eigenpacket (ω : ℂ) :
    matrixOp (sectorPhase ω) (ket 0) = ket 0 ∧
      matrixOp (sectorPhase ω) (ket 1) = ω • ket 1 ∧
        matrixOp (sectorPhase ω) (ket 2) = (ω ^ 2) • ket 2 :=
  ⟨sectorPhase_matrixOp_ket0 ω, sectorPhase_matrixOp_ket1 ω,
    sectorPhase_matrixOp_ket2 ω⟩

/-- The cyclic shift sends `|0⟩` to `|1⟩`. -/
theorem qutritShiftMatrix_ket0 : matrixOp qutritShiftMatrix (ket 0) = ket 1 := by
  ext i
  fin_cases i <;>
    simp [matrixOp_apply, ket, qutritShiftMatrix, Matrix.mulVec, Fin.sum_univ_three]

/-- The cyclic shift sends `|1⟩` to `|2⟩`. -/
theorem qutritShiftMatrix_ket1 : matrixOp qutritShiftMatrix (ket 1) = ket 2 := by
  ext i
  fin_cases i <;>
    simp [matrixOp_apply, ket, qutritShiftMatrix, Matrix.mulVec, Fin.sum_univ_three]

/-- The cyclic shift sends `|2⟩` to `|0⟩`. -/
theorem qutritShiftMatrix_ket2 : matrixOp qutritShiftMatrix (ket 2) = ket 0 := by
  ext i
  fin_cases i <;>
    simp [matrixOp_apply, ket, qutritShiftMatrix, Matrix.mulVec, Fin.sum_univ_three]

/-- The cyclic-shift action on computational kets as a packet. -/
theorem qutritShiftMatrix_computational_cycle :
    matrixOp qutritShiftMatrix (ket 0) = ket 1 ∧
      matrixOp qutritShiftMatrix (ket 1) = ket 2 ∧
        matrixOp qutritShiftMatrix (ket 2) = ket 0 :=
  ⟨qutritShiftMatrix_ket0, qutritShiftMatrix_ket1, qutritShiftMatrix_ket2⟩

/-- The generalized qutrit Pauli `X` acts on computational kets by the qutrit cycle. -/
theorem qutritGeneralizedPauliX_computational_cycle :
    matrixOp qutritGeneralizedPauliX (ket 0) = ket 1 ∧
      matrixOp qutritGeneralizedPauliX (ket 1) = ket 2 ∧
        matrixOp qutritGeneralizedPauliX (ket 2) = ket 0 :=
  qutritShiftMatrix_computational_cycle

/-- The generalized qutrit Pauli `Z` diagonalizes in the computational basis. -/
theorem qutritGeneralizedPauliZ_computational_eigenpacket (ω : ℂ) :
    matrixOp (qutritGeneralizedPauliZ ω) (ket 0) = ket 0 ∧
      matrixOp (qutritGeneralizedPauliZ ω) (ket 1) = ω • ket 1 ∧
        matrixOp (qutritGeneralizedPauliZ ω) (ket 2) = (ω ^ 2) • ket 2 :=
  sectorPhase_computational_eigenpacket ω

/-- The permutation matrix bridge follows the semantic action on computational kets. -/
theorem qutritPermutationMatrix_matrixOp_ket (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    matrixOp (qutritPermutationMatrix σ) (ket i) = ket (σ i) := by
  ext j
  simp [matrixOp_apply, ket, qutritPermutationMatrix, Matrix.mulVec, Equiv.Perm.permMatrix]
  by_cases h : σ.symm j = i
  · have hj : j = σ i := by
      rw [← h]
      simp
    simp [h, hj]
  · have hj : j ≠ σ i := by
      intro hj
      apply h
      rw [hj]
      simp
    simp [h, hj]

/-- The identity label permutation is realized by the identity qutrit matrix. -/
theorem qutritPermutationMatrix_one :
    qutritPermutationMatrix (1 : Equiv.Perm (Fin 3)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qutritPermutationMatrix, Equiv.Perm.permMatrix]

/-- Qutrit permutation matrices multiply in the same order as semantic label permutations. -/
theorem qutritPermutationMatrix_mul (σ τ : Equiv.Perm (Fin 3)) :
    qutritPermutationMatrix (σ * τ) = qutritPermutationMatrix σ * qutritPermutationMatrix τ := by
  rw [qutritPermutationMatrix, qutritPermutationMatrix, qutritPermutationMatrix]
  have hsymm : (σ * τ).symm = τ.symm * σ.symm := by
    ext i
    rfl
  rw [hsymm]
  rw [Matrix.permMatrix_mul]

/-- The qutrit permutation matrix of `σ⁻¹` is a right inverse to that of `σ`. -/
theorem qutritPermutationMatrix_mul_symm (σ : Equiv.Perm (Fin 3)) :
    qutritPermutationMatrix σ * qutritPermutationMatrix σ.symm = 1 := by
  calc
    qutritPermutationMatrix σ * qutritPermutationMatrix σ.symm =
        qutritPermutationMatrix (σ * σ.symm) := by
      rw [qutritPermutationMatrix_mul]
    _ = qutritPermutationMatrix 1 := by
      congr 1
      ext i
      simp
    _ = 1 := qutritPermutationMatrix_one

/-- The qutrit permutation matrix of `σ⁻¹` is a left inverse to that of `σ`. -/
theorem qutritPermutationMatrix_symm_mul (σ : Equiv.Perm (Fin 3)) :
    qutritPermutationMatrix σ.symm * qutritPermutationMatrix σ = 1 := by
  calc
    qutritPermutationMatrix σ.symm * qutritPermutationMatrix σ =
        qutritPermutationMatrix (σ.symm * σ) := by
      rw [qutritPermutationMatrix_mul]
    _ = qutritPermutationMatrix 1 := by
      congr 1
      ext i
      simp
    _ = 1 := qutritPermutationMatrix_one

/-- The finite qutrit permutation-matrix representation of `S₃` labels. -/
def qutritPermutationMatrixMonoidHom : Equiv.Perm (Fin 3) →* QutritMatrix where
  toFun := qutritPermutationMatrix
  map_one' := qutritPermutationMatrix_one
  map_mul' := qutritPermutationMatrix_mul

/-- The generalized qutrit Pauli `Z` and `X` satisfy the same finite Weyl relation. -/
theorem qutritGeneralizedPauliZ_mul_X (ω : ℂ) (hω : ω ^ 3 = 1) :
    qutritGeneralizedPauliZ ω * qutritGeneralizedPauliX =
      ω • (qutritGeneralizedPauliX * qutritGeneralizedPauliZ ω) :=
  qutrit_clock_shift_weyl ω hω

/-- The qutrit clock/shift pair is a finite Weyl pair whenever `ω³ = 1`. -/
def qutritWeylPair (ω : ℂ) (hω : ω ^ 3 = 1) :
    FiniteWeylPair 3 QutritMatrix where
  coordinate := qutritShiftMatrix
  momentum := sectorPhase ω
  q := ω
  q_pow_dim := hω
  weyl_relation := qutrit_clock_shift_weyl ω hω

/-- The general finite-Weyl commutator theorem specializes to the qutrit clock/shift pair. -/
theorem qutritWeylPair_commutator (ω : ℂ) (hω : ω ^ 3 = 1) :
    (qutritWeylPair ω hω).coordinate * (qutritWeylPair ω hω).momentum -
      (qutritWeylPair ω hω).momentum * (qutritWeylPair ω hω).coordinate =
        (1 - (qutritWeylPair ω hω).q : ℂ) •
          ((qutritWeylPair ω hω).coordinate * (qutritWeylPair ω hω).momentum) :=
  (qutritWeylPair ω hω).coordinate_momentum_commutator

/-- The full permutation group of three labels acts on the qutrit-label incidence carrier. -/
def s3QutritLabelAction :
    IncidenceGeometry.BraidActionOnIncidence (Equiv.Perm (Fin 3))
      IncidenceGeometry.qutritLabelIncidence :=
  IncidenceGeometry.qutritLabelBraidAction (MonoidHom.id (Equiv.Perm (Fin 3)))

/-- The first adjacent-transposition matrix action agrees with the qutrit-label
incidence action on computational kets. -/
theorem qutritPermutationMatrix_sigma1_ket (i : Fin 3) :
    matrixOp (qutritPermutationMatrix sigma1) (ket i) =
      ket (s3QutritLabelAction.pointAct sigma1 i) := by
  rw [qutritPermutationMatrix_matrixOp_ket]
  rfl

/-- The second adjacent-transposition matrix action agrees with the qutrit-label
incidence action on computational kets. -/
theorem qutritPermutationMatrix_sigma2_ket (i : Fin 3) :
    matrixOp (qutritPermutationMatrix sigma2) (ket i) =
      ket (s3QutritLabelAction.pointAct sigma2 i) := by
  rw [qutritPermutationMatrix_matrixOp_ket]
  rfl

/-- The first adjacent-transposition qutrit matrix squares to the identity. -/
theorem qutritPermutationMatrix_sigma1_sq :
    qutritPermutationMatrix sigma1 * qutritPermutationMatrix sigma1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qutritPermutationMatrix, Equiv.Perm.permMatrix, sigma1, Matrix.mul_apply,
      Fin.sum_univ_three, Equiv.swap_apply_def]

/-- The second adjacent-transposition qutrit matrix squares to the identity. -/
theorem qutritPermutationMatrix_sigma2_sq :
    qutritPermutationMatrix sigma2 * qutritPermutationMatrix sigma2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qutritPermutationMatrix, Equiv.Perm.permMatrix, sigma2, Matrix.mul_apply,
      Fin.sum_univ_three, Equiv.swap_apply_def]

/-- The concrete `S₃` Artin relation is realized by qutrit permutation matrices. -/
theorem qutritPermutationMatrix_artin_relation :
    qutritPermutationMatrix sigma1 * qutritPermutationMatrix sigma2 *
        qutritPermutationMatrix sigma1 =
      qutritPermutationMatrix sigma2 * qutritPermutationMatrix sigma1 *
        qutritPermutationMatrix sigma2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qutritPermutationMatrix, Equiv.Perm.permMatrix, sigma1, sigma2, Matrix.mul_apply,
      Fin.sum_univ_three, Equiv.swap_apply_def]

/-- The first adjacent transposition conjugates rank-one qutrit ket projectors by
its label action. -/
theorem qutritPermutationMatrix_sigma1_conj_qutritKetProjector (i : Fin 3) :
    qutritPermutationMatrix sigma1 * qutritKetProjector i * qutritPermutationMatrix sigma1 =
      qutritKetProjector (sigma1 i) := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [qutritPermutationMatrix, qutritKetProjector, ket,
      Equiv.Perm.permMatrix, Matrix.mul_apply, sigma1, Fin.sum_univ_three,
      Equiv.swap_apply_def]

/-- The second adjacent transposition conjugates rank-one qutrit ket projectors by
its label action. -/
theorem qutritPermutationMatrix_sigma2_conj_qutritKetProjector (i : Fin 3) :
    qutritPermutationMatrix sigma2 * qutritKetProjector i * qutritPermutationMatrix sigma2 =
      qutritKetProjector (sigma2 i) := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [qutritPermutationMatrix, qutritKetProjector, ket,
      Equiv.Perm.permMatrix, Matrix.mul_apply, sigma2, Fin.sum_univ_three,
      Equiv.swap_apply_def]

/-- The first adjacent transposition swaps sectors `0` and `1` and fixes sector `2`. -/
theorem qutritPermutationMatrix_sigma1_conj_sectorProjector_packet :
    qutritPermutationMatrix sigma1 * sectorProjector0 * qutritPermutationMatrix sigma1 =
        sectorProjector1 ∧
      qutritPermutationMatrix sigma1 * sectorProjector1 * qutritPermutationMatrix sigma1 =
        sectorProjector0 ∧
      qutritPermutationMatrix sigma1 * sectorProjector2 * qutritPermutationMatrix sigma1 =
        sectorProjector2 := by
  constructor
  · rw [sectorProjector0_eq_qutritKetProjector, sectorProjector1_eq_qutritKetProjector,
      qutritPermutationMatrix_sigma1_conj_qutritKetProjector]
    rfl
  constructor
  · rw [sectorProjector1_eq_qutritKetProjector, sectorProjector0_eq_qutritKetProjector,
      qutritPermutationMatrix_sigma1_conj_qutritKetProjector]
    rfl
  · rw [sectorProjector2_eq_qutritKetProjector,
      qutritPermutationMatrix_sigma1_conj_qutritKetProjector]
    rfl

/-- The second adjacent transposition swaps sectors `1` and `2` and fixes sector `0`. -/
theorem qutritPermutationMatrix_sigma2_conj_sectorProjector_packet :
    qutritPermutationMatrix sigma2 * sectorProjector0 * qutritPermutationMatrix sigma2 =
        sectorProjector0 ∧
      qutritPermutationMatrix sigma2 * sectorProjector1 * qutritPermutationMatrix sigma2 =
        sectorProjector2 ∧
      qutritPermutationMatrix sigma2 * sectorProjector2 * qutritPermutationMatrix sigma2 =
        sectorProjector1 := by
  constructor
  · rw [sectorProjector0_eq_qutritKetProjector,
      qutritPermutationMatrix_sigma2_conj_qutritKetProjector]
    rfl
  constructor
  · rw [sectorProjector1_eq_qutritKetProjector, sectorProjector2_eq_qutritKetProjector,
      qutritPermutationMatrix_sigma2_conj_qutritKetProjector]
    rfl
  · rw [sectorProjector2_eq_qutritKetProjector, sectorProjector1_eq_qutritKetProjector,
      qutritPermutationMatrix_sigma2_conj_qutritKetProjector]
    rfl

/-- Finite qutrit sector transport by the two adjacent transposition matrices. -/
theorem qutrit_adjacent_sector_transport_synthesis :
    (∀ i : Fin 3,
      qutritPermutationMatrix sigma1 * qutritKetProjector i * qutritPermutationMatrix sigma1 =
        qutritKetProjector (sigma1 i)) ∧
    (∀ i : Fin 3,
      qutritPermutationMatrix sigma2 * qutritKetProjector i * qutritPermutationMatrix sigma2 =
        qutritKetProjector (sigma2 i)) ∧
    (qutritPermutationMatrix sigma1 * sectorProjector0 * qutritPermutationMatrix sigma1 =
        sectorProjector1 ∧
      qutritPermutationMatrix sigma1 * sectorProjector1 * qutritPermutationMatrix sigma1 =
        sectorProjector0 ∧
      qutritPermutationMatrix sigma1 * sectorProjector2 * qutritPermutationMatrix sigma1 =
        sectorProjector2) ∧
    (qutritPermutationMatrix sigma2 * sectorProjector0 * qutritPermutationMatrix sigma2 =
        sectorProjector0 ∧
      qutritPermutationMatrix sigma2 * sectorProjector1 * qutritPermutationMatrix sigma2 =
        sectorProjector2 ∧
      qutritPermutationMatrix sigma2 * sectorProjector2 * qutritPermutationMatrix sigma2 =
        sectorProjector1) := by
  exact ⟨qutritPermutationMatrix_sigma1_conj_qutritKetProjector,
    qutritPermutationMatrix_sigma2_conj_qutritKetProjector,
    qutritPermutationMatrix_sigma1_conj_sectorProjector_packet,
    qutritPermutationMatrix_sigma2_conj_sectorProjector_packet⟩

/-- The adjacent-transposition braid shadow preserves qutrit-label incidence. -/
theorem s3QutritLabelAction_sigma1_preserves {i j : Fin 3}
    (hij : IncidenceGeometry.qutritLabelIncidence.Inc i j) :
    IncidenceGeometry.qutritLabelIncidence.Inc
      (s3QutritLabelAction.pointAct sigma1 i)
      (s3QutritLabelAction.lineAct sigma1 j) :=
  IncidenceGeometry.EndAction.preserves_incidence s3QutritLabelAction sigma1 hij

/-- The second adjacent-transposition braid shadow also preserves qutrit-label incidence. -/
theorem s3QutritLabelAction_sigma2_preserves {i j : Fin 3}
    (hij : IncidenceGeometry.qutritLabelIncidence.Inc i j) :
    IncidenceGeometry.qutritLabelIncidence.Inc
      (s3QutritLabelAction.pointAct sigma2 i)
      (s3QutritLabelAction.lineAct sigma2 j) :=
  IncidenceGeometry.EndAction.preserves_incidence s3QutritLabelAction sigma2 hij

/-- The `S₃` Artin braid relation is visible on qutrit-label points. -/
theorem s3QutritLabelAction_artin_point (i : Fin 3) :
    s3QutritLabelAction.pointAct (sigma1 * sigma2 * sigma1) i =
      s3QutritLabelAction.pointAct (sigma2 * sigma1 * sigma2) i := by
  rw [s3_adjacent_artin_relation]

/-- The `S₃` Artin braid relation is visible on qutrit-label lines. -/
theorem s3QutritLabelAction_artin_line (i : Fin 3) :
    s3QutritLabelAction.lineAct (sigma1 * sigma2 * sigma1) i =
      s3QutritLabelAction.lineAct (sigma2 * sigma1 * sigma2) i := by
  rw [s3_adjacent_artin_relation]

/-- The finite qutrit braid/incidence bridge packet.

This synthesis theorem deliberately packages only kernel-checked finite algebra:
clock/shift Weyl data, sector projectors as computational-ket projectors,
Gell-Mann diagonal readouts, concrete `S₃` braid-matrix relations, and incidence
preservation. -/
theorem qutrit_braid_incidence_bridge_synthesis (ω : ℂ) (hω : ω ^ 3 = 1) :
    qutritGeneralizedPauliX * qutritGeneralizedPauliX * qutritGeneralizedPauliX = 1 ∧
    qutritGeneralizedPauliZ ω * qutritGeneralizedPauliZ ω * qutritGeneralizedPauliZ ω = 1 ∧
    qutritGeneralizedPauliZ ω * qutritGeneralizedPauliX =
      ω • (qutritGeneralizedPauliX * qutritGeneralizedPauliZ ω) ∧
    sectorProjector0 = qutritKetProjector 0 ∧
    sectorProjector1 = qutritKetProjector 1 ∧
    sectorProjector2 = qutritKetProjector 2 ∧
    gl3 = sectorProjector0 - sectorProjector1 ∧
    gl8 = sectorProjector0 + sectorProjector1 - (2 : ℂ) • sectorProjector2 ∧
    qutritPermutationMatrix sigma1 * qutritPermutationMatrix sigma1 = 1 ∧
    qutritPermutationMatrix sigma2 * qutritPermutationMatrix sigma2 = 1 ∧
    qutritPermutationMatrix sigma1 * qutritPermutationMatrix sigma2 *
        qutritPermutationMatrix sigma1 =
      qutritPermutationMatrix sigma2 * qutritPermutationMatrix sigma1 *
        qutritPermutationMatrix sigma2 ∧
    (∀ i j, IncidenceGeometry.qutritLabelIncidence.Inc i j →
      IncidenceGeometry.qutritLabelIncidence.Inc
        (s3QutritLabelAction.pointAct sigma1 i)
        (s3QutritLabelAction.lineAct sigma1 j)) ∧
    (∀ i j, IncidenceGeometry.qutritLabelIncidence.Inc i j →
      IncidenceGeometry.qutritLabelIncidence.Inc
        (s3QutritLabelAction.pointAct sigma2 i)
        (s3QutritLabelAction.lineAct sigma2 j)) := by
  exact ⟨qutritGeneralizedPauliX_cube_identity,
    qutritGeneralizedPauliZ_cube_identity ω hω,
    qutritGeneralizedPauliZ_mul_X ω hω,
    sectorProjector0_eq_qutritKetProjector,
    sectorProjector1_eq_qutritKetProjector,
    sectorProjector2_eq_qutritKetProjector,
    gellMann_gl3_sectorProjectors,
    gellMann_gl8_sectorProjectors,
    qutritPermutationMatrix_sigma1_sq,
    qutritPermutationMatrix_sigma2_sq,
    qutritPermutationMatrix_artin_relation,
    (fun _ _ hij => s3QutritLabelAction_sigma1_preserves hij),
    (fun _ _ hij => s3QutritLabelAction_sigma2_preserves hij)⟩

end InfoGeometry.Quantum.QutritBraidIncidenceBridge
