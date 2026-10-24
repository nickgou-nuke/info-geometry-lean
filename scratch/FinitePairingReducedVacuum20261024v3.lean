/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CARMajoranaMatrices
import InfoGeometry.OperatorAlgebra.FinitePairingImplementer
import InfoGeometry.QuantumContext.MatrixStagePartialTrace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

/-! # Reduced vacuum of the native finite pairing rotor

Scratch v3 candidate: not kernel checked. Ordinary, trace-preserving partial trace;
real coefficients. The polynomial identities require no normalization. All
operators use the existing product-index complex matrix carrier. No abstract
CAR hypotheses or additional representation carrier are introduced.
Unitarity and trace-one assertions require real normalization; positivity does
not. Projector terminology is reserved for normalized coefficients.
-/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.FinitePairingReducedVacuum

open scoped Kronecker ComplexOrder
open InfoGeometry.MajoranaPfaffianNaturalClosure
open InfoGeometry.Canonical.CARMajoranaFiniteBridge
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
open FinitePairingImplementer

abbrev a : M2C := annihilationR.map (algebraMap ℝ ℂ)
abbrev A : M2C := creationR.map (algebraMap ℝ ℂ)

def b₁ : ChainOp := a ⊗ₖ (1 : M2C)
def B₁ : ChainOp := A ⊗ₖ (1 : M2C)
def b₂ : ChainOp := parityMatrix ⊗ₖ a
def B₂ : ChainOp := parityMatrix ⊗ₖ A

def vacuum : ChainOp := (b₁ * B₁) * (b₂ * B₂)

/-- Readback of the native support, including the doubly occupied sector. -/
theorem pairSupport_apply (i j : Fin 2 × Fin 2) :
    pairSupport b₁ B₁ b₂ B₂ i j =
      if i = j ∧ (i = (0, 0) ∨ i = (1, 1)) then 1 else 0 := by
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [pairSupport, b₁, B₁, b₂, B₂, a, A, parityMatrix,
      annihilationR, creationR, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kronecker_apply, Matrix.one_apply]

theorem vacuum_apply (i j : Fin 2 × Fin 2) :
    vacuum i j = if i = (0, 0) ∧ j = (0, 0) then 1 else 0 := by
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    norm_num [vacuum, b₁, B₁, b₂, B₂, a, A, parityMatrix,
      annihilationR, creationR, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kronecker_apply, Matrix.one_apply]

/-- The even-sector block is [[c,s],[-s,c]]; odd sectors are fixed. -/
theorem rotor_apply (c s : ℝ) (i j : Fin 2 × Fin 2) :
    rotor b₁ B₁ b₂ B₂ c s i j =
      if i = (0, 0) then
        (if j = (0, 0) then (c : ℂ) else if j = (1, 1) then (s : ℂ) else 0)
      else if i = (1, 1) then
        (if j = (0, 0) then -(s : ℂ) else if j = (1, 1) then (c : ℂ) else 0)
      else if i = j then 1 else 0 := by
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [rotor, pairSupport, current, b₁, B₁, b₂, B₂, a, A, parityMatrix,
      annihilationR, creationR, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply,
      RCLike.real_smul_eq_coe_mul]

/-- Real coefficients make the reverse polynomial the actual adjoint. -/
theorem rotor_conjTranspose (c s : ℝ) :
    (rotor b₁ B₁ b₂ B₂ c s).conjTranspose = rotor b₁ B₁ b₂ B₂ c (-s) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.conjTranspose_apply, rotor_apply]

/-- Real normalization makes the rotor times its adjoint the identity. -/
theorem rotor_mul_conjTranspose (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    rotor b₁ B₁ b₂ B₂ c s * (rotor b₁ B₁ b₂ B₂ c s).conjTranspose = 1 := by
  have hc : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  ring_nf at hc
  rw [rotor_conjTranspose]
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      rotor_apply] <;> ring_nf <;> exact hc

/-- The opposite unitary identity follows by reversing the real parameter. -/
theorem rotor_conjTranspose_mul (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (rotor b₁ B₁ b₂ B₂ c s).conjTranspose * rotor b₁ B₁ b₂ B₂ c s = 1 := by
  have h := rotor_mul_conjTranspose c (-s) (by simpa using hcs)
  simpa only [rotor_conjTranspose, neg_neg] using h

/-- Amplitudes in the existing product basis, with the native pairing sign. -/
def vacuumAmplitude (c s : ℝ) (i : Fin 2 × Fin 2) : ℂ :=
  if i = (0, 0) then (c : ℂ) else if i = (1, 1) then -(s : ℂ) else 0

/-- All sixteen entries of the rotated vacuum outer product, including coherence. -/
theorem rotatedVacuum_apply (c s : ℝ) (i j : Fin 2 × Fin 2) :
    (rotor b₁ B₁ b₂ B₂ c s * vacuum *
      (rotor b₁ B₁ b₂ B₂ c s).conjTranspose) i j =
        vacuumAmplitude c s i * vacuumAmplitude c s j := by
  rw [rotor_conjTranspose]
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      rotor_apply, vacuum_apply, vacuumAmplitude]

/-- Ordinary partial trace removes the pair coherence, without a factor 1/2. -/
theorem reducedVacuum (c s : ℝ) :
    partialTraceSecondOp (rotor b₁ B₁ b₂ B₂ c s * vacuum *
      (rotor b₁ B₁ b₂ B₂ c s).conjTranspose) =
        (c ^ 2 : ℝ) • (a * A) + (s ^ 2 : ℝ) • (A * a) := by
  ext i j
  simp only [partialTraceSecondOp, Fin.sum_univ_two, rotatedVacuum_apply]
  fin_cases i <;> fin_cases j <;>
    simp [vacuumAmplitude, a, A, annihilationR, creationR,
      Matrix.mul_apply, Fin.sum_univ_two, RCLike.real_smul_eq_coe_mul, pow_two]

/-- The actual reduced matrix is a diagonal Gram matrix, even without
normalization. No positivity conclusion is supplied as a hypothesis. -/
theorem reducedVacuum_posSemidef (c s : ℝ) :
    (partialTraceSecondOp (rotor b₁ B₁ b₂ B₂ c s * vacuum *
      (rotor b₁ B₁ b₂ B₂ c s).conjTranspose)).PosSemidef := by
  let G : M2C := Matrix.diagonal ![(c : ℂ), (s : ℂ)]
  have hgram : partialTraceSecondOp (rotor b₁ B₁ b₂ B₂ c s * vacuum *
      (rotor b₁ B₁ b₂ B₂ c s).conjTranspose) = G.conjTranspose * G := by
    rw [reducedVacuum]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [G, a, A, annihilationR, creationR, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.diagonal,
        RCLike.real_smul_eq_coe_mul] <;> ring
  rw [hgram]
  exact Matrix.posSemidef_conjTranspose_mul_self G

/-- Trace of the actual reduced operator, before imposing normalization. -/
theorem reducedVacuum_trace (c s : ℝ) :
    Matrix.trace (partialTraceSecondOp (rotor b₁ B₁ b₂ B₂ c s * vacuum *
      (rotor b₁ B₁ b₂ B₂ c s).conjTranspose)) = ((c ^ 2 + s ^ 2 : ℝ) : ℂ) := by
  rw [reducedVacuum]
  simp [Matrix.trace, Matrix.diag, a, A, annihilationR, creationR,
    Matrix.mul_apply, Fin.sum_univ_two, RCLike.real_smul_eq_coe_mul]

/-- The global rotated vacuum has ordinary trace one under real normalization. -/
theorem rotatedVacuum_trace_one (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    Matrix.trace (rotor b₁ B₁ b₂ B₂ c s * vacuum *
      (rotor b₁ B₁ b₂ B₂ c s).conjTranspose) = 1 := by
  rw [← partialTraceSecondOp_trace, reducedVacuum_trace, hcs]
  norm_num

/-- Purity of the actual reduced matrix, not a scalar proxy for its construction. -/
theorem reducedVacuum_purity (c s : ℝ) :
    let D := partialTraceSecondOp (rotor b₁ B₁ b₂ B₂ c s * vacuum *
      (rotor b₁ B₁ b₂ B₂ c s).conjTranspose)
    (Matrix.trace (D * D)).re = c ^ 4 + s ^ 4 := by
  dsimp only
  rw [reducedVacuum]
  simp [Matrix.trace, Matrix.diag, a, A, annihilationR, creationR,
    Matrix.mul_apply, Fin.sum_univ_two, RCLike.real_smul_eq_coe_mul,
    pow_two, Complex.mul_re] <;> ring

/-- Under normalization, reduced purity is strictly below one exactly when
both empty and occupied amplitudes are nonzero. -/
theorem reducedVacuum_purity_lt_one_iff (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    let D := partialTraceSecondOp (rotor b₁ B₁ b₂ B₂ c s * vacuum *
      (rotor b₁ B₁ b₂ B₂ c s).conjTranspose)
    (Matrix.trace (D * D)).re < 1 ↔ c * s ≠ 0 := by
  dsimp only
  rw [reducedVacuum_purity]
  have hid : c ^ 4 + s ^ 4 + 2 * (c * s) ^ 2 = 1 := by
    have hsquare := congrArg (fun x : ℝ => x ^ 2) hcs
    nlinarith only [hsquare]
  constructor
  · intro h hz
    rw [hz] at hid
    norm_num at hid
    linarith
  · intro h
    have hp : 0 < (c * s) ^ 2 := sq_pos_of_ne_zero h
    linarith

end InfoGeometry.OperatorAlgebra.FinitePairingReducedVacuum

end
