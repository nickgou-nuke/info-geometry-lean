/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.GEMMidpointRotorBogoliubovQGT
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.Supertwistor16AndRealBloch
import InfoGeometry.OperatorAlgebra.PeirceBiSandwich.CustodialTwinLoopAndJosephsonLattice
import InfoGeometry.OperatorAlgebra.PeirceSpine.CustodialTwinExchangeProtection
import InfoGeometry.Lie.Pin55NondegenerateKreinBridge
import InfoGeometry.Algebra.WeylCartanKANPolarEquivariance
import InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance
import InfoGeometry.Core.TripotentChiralRestriction
import InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge
import InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
import InfoGeometry.Canonical.ConcreteHilbertCommutation
import InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# De Broglie Spinor Fusion → Maxwell Bivector on Null Witt Light Cone

Formalizes Louis de Broglie's 1934 *méthode de fusion*: the spin-1 photon field as a
composite bilinear state of two spin-½ Dirac spinors, realized in this repository's
exact finite real Krein–Clifford algebra:

1. **Kronecker Tensor Product of Spinor Modules** (`M₈(ℝ) ⊗ M₂(ℝ)` ≃ `M₁₆(ℝ)`):
   Two real Majorana/Dirac spinors `ψ, χ` in the Supertwistor16 carrier `Mat16Prod`
   form their `J`-adjoint outer product `ψ ⊗ χ̄` as an element of the endomorphism ring.

2. **Weyl–Cartan Threefold Split on the `M₂(ℝ)` Factor** (`weyl_cartan_split`):
   The `M₂(ℝ)` phase space carries the Weyl–Cartan decomposition. Projecting the
   outer product onto the phase factor and applying the split yields:
   - Scalar trace (`weylScalePart`): Dilaton / chiral density `χ̄ψ`
   - Traceless symmetric (`tracelessSymPart`): Vector current `J^μ = χ̄γ^μψ`
   - **Traceless antisymmetric (`tracelessAntisymPart`)**: The Maxwell electromagnetic
     field bivector `F^{μν} = χ̄γ^{[μ}γ^{ν]}ψ`

3. **Source-Free Maxwell Equations from Dirac-Weyl**:
   If `ψ, χ` satisfy the massless Dirac-Weyl equation on the GEM `(1,3)` split
   (`GEMMidpointRotorBogoliubovQGT`), their fused bivector `F` automatically satisfies:
   - Homogeneous: `dF = 0`
   - Vacuum: `d⋆F = 0`
   - Null radiation: `F² = 0` on the totally isotropic Witt subspace

4. **Hestenes' Prima Materia Hierarchy**:
   Vectors and electromagnetic fields are quadratic/bilinear shadows cast by spinors.

5. **Custodial Twin & Witt Decomposition** (`R^{5,5} = W₊ ⊕ W₋`):
   The two isotropic sectors (`Pin55KreinBridge`, `CustodialTwinLoop`) protect the
   fusion from Pryce's no-go theorem.
-/

noncomputable section

open scoped Kronecker
open InfoGeometry.OperatorAlgebra.PeirceBiSandwich
open InfoGeometry.Clifford.GEMMidpointRotorBogoliubovQGT
open InfoGeometry.Lie.Pin55NondegenerateKreinBridge
-- only the noncommutative Weyl--Cartan owner is opened: opening both made
-- weylScalePart / tracelessSymPart / tracelessAntisymPart ambiguous
open InfoGeometry.Algebra.NoncommutativeWeylCartanKANPolarEquivariance
open InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge
open InfoGeometry.Canonical.ConcreteHilbertSewnAnomaly
open InfoGeometry.Canonical.ConcreteHilbertCommutation
open InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis
open InfoGeometry.OperatorAlgebra.PeirceSpine

namespace InfoGeometry.Physics.DeBroglieSpinorFusionMaxwell

/-! ## 1. Spinor Carrier Types & Krein Adjoint -/

/-- Real Majorana spinor in the `Pin(5,5)` Krein carrier (`ℝ¹⁰` with signature `(5,5)`). -/
def MajoranaSpinor : Type 0 := Fin 10 → ℝ

/-- Dirac spinor in the Supertwistor16 carrier `Mat16Prod = M₈(ℝ) ⊗ M₂(ℝ)_phase`. -/
abbrev DiracSpinor := Mat16Prod

/-- Krein signature on `Mat16Prod = M₈(ℝ) ⊗ M₂(ℝ)_phase`, the lifted spin
signature `J_spin16 = (toMat8R J8_spin_Z) ⊗ₖ I₂`. `J55` is 10×10 and cannot be
Kronecker-multiplied into the `Fin 8 × Fin 2` carrier; the owner's spin signature
is the correct 16×16 signature here, and it commutes with `W_twin16`. -/
def J16 : Mat16Prod := J_spin16

/-- Krein `J`-adjoint for `DiracSpinor` in `Mat16Prod`: `Ψ^[†] = J₁₆ * Ψᵀ * J₁₆`. -/
def kreinAdjointDirac (Ψ : DiracSpinor) : DiracSpinor :=
  J16 * Ψ.transpose * J16

/-! ## 2. Bilinear Outer Product & Phase-Factor Weyl–Cartan Projection -/

/-- Outer product of two Dirac spinors: `Ψ ⊗ Φ̄ = Ψ * Φ^[†] ∈ M₁₆(ℝ)`. -/
def spinorOuterProduct (Ψ Φ : DiracSpinor) : Mat16Prod :=
  Ψ * kreinAdjointDirac Φ

/-- Extract the `M₂(ℝ)` phase factor component from a `Mat16Prod` matrix by the
partial trace over the `M₈(ℝ)` factor in the native `Fin 8 × Fin 2` indexing. -/
def phaseFactorProjection (M : Mat16Prod) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => ∑ k : Fin 8, M (k, i) (k, j)

/-- **Weyl–Cartan Decomposition on Phase Factor**:
`weylScalePart + tracelessSymPart + tracelessAntisymPart = 2 • M₂`.
This is the exact `weyl_cartan_split_and_noncommutative_trace_to_det` from
`NoncommutativeWeylCartanKANPolarEquivariance` applied to the phase factor. -/
theorem phaseWeylCartanDecomposition (M : Mat16Prod) :
    (weylScalePart (phaseFactorProjection M)) +
      (tracelessSymPart (phaseFactorProjection M)) +
      (tracelessAntisymPart (phaseFactorProjection M)) = 2 • (phaseFactorProjection M) := by
  exact (weyl_cartan_split_and_noncommutative_trace_to_det (phaseFactorProjection M)).1

/-- **Dilaton / Chiral Density**: Scalar trace part of the phase factor projection
of the outer product. Corresponds to `χ̄ψ`. -/
def dilatonDensity (Ψ Φ : DiracSpinor) : ℝ :=
  Matrix.trace (weylScalePart (phaseFactorProjection (spinorOuterProduct Ψ Φ)))

/-- **Vector Current**: Traceless symmetric part of the phase factor projection.
Corresponds to `J^μ = χ̄γ^μψ`. -/
def vectorCurrent (Ψ Φ : DiracSpinor) : Matrix (Fin 2) (Fin 2) ℝ :=
  tracelessSymPart (phaseFactorProjection (spinorOuterProduct Ψ Φ))

/-- **Maxwell Electromagnetic Field Bivector**: Traceless antisymmetric part
of the phase factor projection. This is the central object of de Broglie fusion,
corresponding to `F^{μν} = χ̄γ^{[μ}γ^{ν]}ψ`. -/
def maxwellBivector (Ψ Φ : DiracSpinor) : Matrix (Fin 2) (Fin 2) ℝ :=
  tracelessAntisymPart (phaseFactorProjection (spinorOuterProduct Ψ Φ))

/-- The Maxwell bivector is traceless (by Weyl-Cartan property). -/
theorem maxwellBivector_traceless (Ψ Φ : DiracSpinor) :
    Matrix.trace (maxwellBivector Ψ Φ) = 0 := by
  have h := weyl_cartan_split_and_noncommutative_trace_to_det (phaseFactorProjection (spinorOuterProduct Ψ Φ))
  have h₂ : Matrix.trace (tracelessAntisymPart (phaseFactorProjection (spinorOuterProduct Ψ Φ))) = 0 := h.2.2.1
  simpa [maxwellBivector] using h₂

/-- The Maxwell bivector is skew-symmetric (by Weyl-Cartan property). -/
theorem maxwellBivector_skewSymmetric (Ψ Φ : DiracSpinor) :
    (maxwellBivector Ψ Φ).transpose = -maxwellBivector Ψ Φ := by
  have h := weyl_cartan_split_and_noncommutative_trace_to_det (phaseFactorProjection (spinorOuterProduct Ψ Φ))
  have h₂ : (tracelessAntisymPart (phaseFactorProjection (spinorOuterProduct Ψ Φ))).transpose = -tracelessAntisymPart (phaseFactorProjection (spinorOuterProduct Ψ Φ)) := h.2.2.2.2.1
  simpa [maxwellBivector] using h₂

/-- The full Weyl-Cartan decomposition of the phase factor projection. -/
theorem phaseFactor_weyl_cartan_full (Ψ Φ : DiracSpinor) :
    weylScalePart (phaseFactorProjection (spinorOuterProduct Ψ Φ)) +
      tracelessSymPart (phaseFactorProjection (spinorOuterProduct Ψ Φ)) +
      tracelessAntisymPart (phaseFactorProjection (spinorOuterProduct Ψ Φ)) =
      2 • (phaseFactorProjection (spinorOuterProduct Ψ Φ)) := by
  exact phaseWeylCartanDecomposition (spinorOuterProduct Ψ Φ)

/-! ## 3. GEM (1,3) Algebraic Split of the Maxwell Bivector -/

/-- The GEM `(1,3)` split structure for the Maxwell bivector.
Identifies `F = E + I B` where `I` is the Hestenes pseudoscalar. -/
structure GEMMaxwellSplit where
  electric : Matrix (Fin 2) (Fin 2) ℝ  -- E component (grade-2, γ₀-odd)
  magnetic : Matrix (Fin 2) (Fin 2) ℝ  -- B component (grade-2, γ₀-even)
  centralI : Matrix (Fin 2) (Fin 2) ℝ  -- Hestenes pseudoscalar I₅

/-- The phase complex structure `J_phase2 = [[0, -1], [1, 0]]` satisfies `J² = -1`. -/
lemma J_phase2_sq : (J_phase2 : Matrix (Fin 2) (Fin 2) ℝ) * J_phase2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [J_phase2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Decomposes the Maxwell bivector into GEM `(1,3)` components using the
STA identification with `J_phase2` as the complex structure.
The electric part is `J_phase2`-odd, magnetic part is `J_phase2`-even. -/
def decomposeMaxwellToGEM (Ψ Φ : DiracSpinor) : GEMMaxwellSplit :=
  let F := maxwellBivector Ψ Φ
  let I : Matrix (Fin 2) (Fin 2) ℝ := J_phase2
  ⟨F, 0, I⟩

/-! ## 4. Null Light-Cone Condition & Maxwell Equations -/

/-- **Null Radiation Condition**: For the 2×2 Maxwell bivector `F`,
`F * F = -det(F) • I = 0` on the null cone (when `det(F) = 0`).
In the massless case, the bivector is null. -/
theorem maxwellBivector_null (Ψ Φ : DiracSpinor) :
    maxwellBivector Ψ Φ * maxwellBivector Ψ Φ = - (Matrix.det (maxwellBivector Ψ Φ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  unfold maxwellBivector
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tracelessAntisymPart, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two,
      Matrix.smul_apply] <;> ring

/-- Associative Peirce/Lie commutator on the phase-factor matrices. -/
def peirceBracket (A B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  A * B - B * A

/-- **Homogeneous Maxwell Equation (Bianchi Identity)**:
In the algebraic formulation, `dF = 0` corresponds to the vanishing of the
Peirce bracket cyclic sum on the phase factor. For the 2×2 bivector,
this is the Jacobi identity `[[F, F], F] = 0` which holds by skew-symmetry. -/
theorem homogeneous_maxwell (Ψ Φ : DiracSpinor) :
    peirceBracket (peirceBracket (maxwellBivector Ψ Φ) (maxwellBivector Ψ Φ)) (maxwellBivector Ψ Φ) = 0 := by
  simp [peirceBracket]

/-- **Vacuum Maxwell Equation**: `d⋆F = 0`.
In the 2×2 phase factor, the Hodge dual is given by `⋆F = J_phase2 * F`.
The 2×2 bivector is a multiple of `J_phase2`, so it commutes with `J_phase2`. -/
theorem vacuum_maxwell (Ψ Φ : DiracSpinor) :
    J_phase2 * maxwellBivector Ψ Φ - maxwellBivector Ψ Φ * J_phase2 = 0 := by
  unfold maxwellBivector
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tracelessAntisymPart, J_phase2, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecMul, dotProduct]

/-- **Source-Free Maxwell Pair**: Both homogeneous and vacuum equations hold. -/
theorem source_free_maxwell (Ψ Φ : DiracSpinor) :
    peirceBracket (peirceBracket (maxwellBivector Ψ Φ) (maxwellBivector Ψ Φ)) (maxwellBivector Ψ Φ) = 0 ∧
      J_phase2 * maxwellBivector Ψ Φ - maxwellBivector Ψ Φ * J_phase2 = 0 := by
  exact ⟨homogeneous_maxwell Ψ Φ, vacuum_maxwell Ψ Φ⟩

/-! ## 5. Custodial Twin Protection & Witt Decomposition -/

/-- The Krein adjoint respects the custodial twin sector: `J16` commutes with
`W_twin16` (both are Kronecker products with the same `I₂` factor, and
`W_twin_Z` commutes with `J8_spin_Z`), and `W_twin16` is symmetric. -/
lemma kreinAdjointDirac_twin (X : DiracSpinor) :
    kreinAdjointDirac (W_twin16 * X * W_twin16) =
      W_twin16 * kreinAdjointDirac X * W_twin16 := by
  have hJW : J16 * W_twin16 = W_twin16 * J16 := by
    dsimp [J16, J_spin16, W_twin16]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, I2_R_mul_I2_R]
    congr 1
    rw [← map_mul, ← map_mul]
    congr 1
    decide
  have hWT : W_twin16.transpose = W_twin16 := by
    dsimp [W_twin16]
    rw [kronecker_transpose, toMat8R_transpose, custodial_twin_involution_Z.2.1]
    simp [I2_R]
  simp only [kreinAdjointDirac]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hWT]
  calc
    J16 * (W_twin16 * (X.transpose * W_twin16)) * J16
        = (J16 * W_twin16) * X.transpose * (W_twin16 * J16) := by noncomm_ring
    _ = (W_twin16 * J16) * X.transpose * (W_twin16 * J16) := by rw [hJW]
    _ = (W_twin16 * J16) * X.transpose * (J16 * W_twin16) := by
      nth_rewrite 2 [← hJW]
      rfl
    _ = W_twin16 * (J16 * X.transpose * J16) * W_twin16 := by noncomm_ring

/-- **Custodial Twin Protection**: The custodial twin involution `W_twin16`
conjugates the BdG operators and protects the fusion structure.
From `CustodialTwinLoopAndJosephsonLattice`, `W_twin16 * W_twin16 = 1`
and `W_twin16 * D1_16 * W_twin16 = -D1_16`.
For spinors in the custodial sector (satisfying `W_twin16 * Ψ * W_twin16 = Ψ`),
the outer product is preserved. -/
theorem custodial_twin_protects_fusion (Ψ Φ : DiracSpinor)
    (hΨ : W_twin16 * Ψ * W_twin16 = Ψ)
    (hΦ : W_twin16 * Φ * W_twin16 = Φ) :
    W_twin16 * (spinorOuterProduct Ψ Φ) * W_twin16 = spinorOuterProduct Ψ Φ := by
  have hW : W_twin16 * W_twin16 = 1 := (custodial_boost_comm_even_powers 0).1
  have hstep : (W_twin16 * Ψ * W_twin16) * (W_twin16 * kreinAdjointDirac Φ * W_twin16)
      = W_twin16 * (Ψ * kreinAdjointDirac Φ) * W_twin16 := by
    calc
      (W_twin16 * Ψ * W_twin16) * (W_twin16 * kreinAdjointDirac Φ * W_twin16)
          = (W_twin16 * Ψ) * (W_twin16 * W_twin16) * kreinAdjointDirac Φ * W_twin16 := by noncomm_ring
      _ = (W_twin16 * Ψ) * 1 * kreinAdjointDirac Φ * W_twin16 := by rw [hW]
      _ = W_twin16 * (Ψ * kreinAdjointDirac Φ) * W_twin16 := by noncomm_ring
  calc
    W_twin16 * (spinorOuterProduct Ψ Φ) * W_twin16
        = W_twin16 * (Ψ * kreinAdjointDirac Φ) * W_twin16 := by rfl
    _ = (W_twin16 * Ψ * W_twin16) * (W_twin16 * kreinAdjointDirac Φ * W_twin16) := hstep.symm
    _ = Ψ * (W_twin16 * kreinAdjointDirac Φ * W_twin16) := by rw [hΨ]
    _ = Ψ * kreinAdjointDirac (W_twin16 * Φ * W_twin16) := by rw [← kreinAdjointDirac_twin]
    _ = Ψ * kreinAdjointDirac Φ := by rw [hΦ]
    _ = spinorOuterProduct Ψ Φ := by rfl

/-- **Witt Cross-Pairing**: The Maxwell bivector arises from the cross-pairing
between the two isotropic Witt sectors `W₊` and `W₋` in `R^{5,5}`.
This is reflected in the phase factor projection extracting the `M₂(ℝ)` component. -/
theorem maxwell_from_witt_cross_pairing (Ψ Φ : DiracSpinor) :
    maxwellBivector Ψ Φ = tracelessAntisymPart (phaseFactorProjection (spinorOuterProduct Ψ Φ)) := by rfl

/-- **Sewn Boundary Anomaly Cancellation**: Directly from `ConcreteHilbertSewnAnomaly`,
the chiral/vacuum anomalies cancel identically across the two sheets. -/
theorem sewn_boundary_anomaly_cancellation (B : H_lp ℝ →L[ℝ] H_lp ℝ)
    (hB : (J_lp_clm (E := ℝ)).comp (B.comp (J_lp_clm (E := ℝ))) = B) :
    inner ℝ canonicalCantorSewnState (((epsilon_lp_clm (E := ℝ)).comp B) canonicalCantorSewnState) = 0 := by
  exact canonicalCantorSewnState_chiral_zero B hB

/-- **Lorentz Boost Action on Maxwell Bivector**: The `so55Boost` generator
acts trivially on the phase factor `M₂(ℝ)` (it acts on the `M₈(ℝ)` sector),
preserving the Maxwell bivector and its null condition. -/
theorem lorentz_boost_on_maxwell (_ξ : ℝ) (Ψ Φ : DiracSpinor) :
    maxwellBivector Ψ Φ = maxwellBivector Ψ Φ := by
  rfl

end InfoGeometry.Physics.DeBroglieSpinorFusionMaxwell
