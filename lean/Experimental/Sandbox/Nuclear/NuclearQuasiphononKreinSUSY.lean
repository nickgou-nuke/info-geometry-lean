import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Matrix

/-!
# Nuclear Quasiphonon Krein SUSY

This module formalizes Target 1 (Section 80):
Nuclear Quasiphonon Krein SUSY: Quasiparticle-Phonon Coupling, Doubled Real Krein Space,
Real Pseudo-SUSY Supercharges, and Affine Soloviev-BdG Identification.

## Mathematical Architecture:
1. **The Doubled Real Krein Supercarrier & Fundamental Involutions**:
   Graded Krein carrier `Matrix (V_b ⊕ V_f) (V_b ⊕ V_f) R` equipped with the fundamental
   grading metric `J = diag(I, -I) = fromBlocks 1 0 0 (-1)`, involutive `J² = 1`, and the
   paracomplex sheet swap `S = fromBlocks 0 1 1 0` with `S² = 1` and `{J, S} = 0`.
2. **Real Pseudo-SUSY Supercharges and SUSY Hamiltonian**:
   Nilpotent off-diagonal supercharges `Q` and `Q†` constructed from particle-phonon coupling
   matrix `V_coup : Matrix V_b V_f R`, satisfying `Q² = 0` and `(Q†)² = 0`. The supersymmetric
   Hamiltonian `H = {Q, Q†}` is block-diagonal `fromBlocks (V Vᵀ) 0 0 (Vᵀ V)` and satisfies exact
   SUSY conservation `[H, Q] = 0` and `[H, Q†] = 0`.
3. **Exact Affine Soloviev QPNM to BdG Decomposition**:
   Affine decomposition of Soloviev Quasiparticle-Phonon Nuclear Model (QPNM) matrix into
   a scalar center and a traceless Bogoliubov-de Gennes (BdG) Hamiltonian block, satisfying
   the characteristic polynomial `H_BdG² = (δ² + V²) I`, Andreev reflection reversal,
   `Tr(H_BdG) = 0`, and `det(H_BdG) = -(δ² + V²)`.
4. **Master Verification Certificate**:
   Bundled structure `NuclearQuasiphononKreinSUSYCertificate` verified via standard core axioms.
-/

namespace Experimental.Sandbox.Nuclear.NuclearQuasiphononKreinSUSY

/-! ### Section 1: The Doubled Real Krein Supercarrier & Fundamental Involutions -/

/-- Fundamental Krein metric on the graded supercarrier `Matrix (V_b ⊕ V_f) (V_b ⊕ V_f) R`. -/
def kreinMetric (V_b V_f : Type*) [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    (R : Type*) [CommRing R] : Matrix (V_b ⊕ V_f) (V_b ⊕ V_f) R :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- Involutive property of the fundamental Krein metric: `J² = 1`. -/
theorem kreinMetric_sq (V_b V_f : Type*) [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    (R : Type*) [CommRing R] :
    (kreinMetric V_b V_f R) * (kreinMetric V_b V_f R) = 1 := by
  rw [kreinMetric, Matrix.fromBlocks_multiply]
  simp

/-- Paracomplex sheet-swap operator on the balanced doubled carrier `(V ⊕ V)`. -/
def sheetSwap (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] :
    Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 0 1 1 0

/-- Involutive property of the paracomplex sheet swap: `S² = 1`. -/
theorem sheetSwap_sq (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] :
    (sheetSwap V R) * (sheetSwap V R) = 1 := by
  rw [sheetSwap, Matrix.fromBlocks_multiply]
  simp

/-- Exact anticommutation between the Krein metric and the sheet-swap operator: `{J, S} = 0`. -/
theorem krein_sheetSwap_anticomm (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R] :
    (kreinMetric V V R) * (sheetSwap V R) + (sheetSwap V R) * (kreinMetric V V R) = 0 := by
  rw [kreinMetric, sheetSwap, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp

/-! ### Section 2: Real Pseudo-SUSY Supercharges and SUSY Hamiltonian -/

/-- Real supercharge Q mapping fermionic phonons to bosonic quasiparticles. -/
def superchargeQ {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [CommRing R] (V_coup : Matrix V_b V_f R) : Matrix (V_b ⊕ V_f) (V_b ⊕ V_f) R :=
  Matrix.fromBlocks 0 V_coup 0 0

/-- Transposed conjugate supercharge Q† mapping bosonic quasiparticles to fermionic phonons. -/
def superchargeQ_dag {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [CommRing R] (V_coup : Matrix V_b V_f R) : Matrix (V_b ⊕ V_f) (V_b ⊕ V_f) R :=
  Matrix.fromBlocks 0 0 V_coupᵀ 0

/-- Nilpotence of the real supercharge: `Q² = 0`. -/
theorem superchargeQ_sq {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [CommRing R] (V_coup : Matrix V_b V_f R) :
    (superchargeQ V_coup) * (superchargeQ V_coup) = 0 := by
  rw [superchargeQ, Matrix.fromBlocks_multiply]
  simp

/-- Nilpotence of the conjugate supercharge: `(Q†)² = 0`. -/
theorem superchargeQ_dag_sq {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [CommRing R] (V_coup : Matrix V_b V_f R) :
    (superchargeQ_dag V_coup) * (superchargeQ_dag V_coup) = 0 := by
  rw [superchargeQ_dag, Matrix.fromBlocks_multiply]
  simp

/-- Supersymmetric Hamiltonian defined by anticommutator `{Q, Q†} = Q Q† + Q† Q`. -/
def susyHamiltonian {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [CommRing R] (V_coup : Matrix V_b V_f R) : Matrix (V_b ⊕ V_f) (V_b ⊕ V_f) R :=
  (superchargeQ V_coup) * (superchargeQ_dag V_coup) + (superchargeQ_dag V_coup) * (superchargeQ V_coup)

/-- Exact block diagonal decomposition of the supersymmetric Hamiltonian. -/
theorem susyHamiltonian_blocks {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [CommRing R] (V_coup : Matrix V_b V_f R) :
    susyHamiltonian V_coup = Matrix.fromBlocks (V_coup * V_coupᵀ) 0 0 (V_coupᵀ * V_coup) := by
  rw [susyHamiltonian, superchargeQ, superchargeQ_dag, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp

/-- Commutation and conservation of supercharge Q with the SUSY Hamiltonian: `[H, Q] = 0`. -/
theorem susyHamiltonian_comm_Q {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [CommRing R] (V_coup : Matrix V_b V_f R) :
    (susyHamiltonian V_coup) * (superchargeQ V_coup) - (superchargeQ V_coup) * (susyHamiltonian V_coup) = 0 := by
  rw [susyHamiltonian_blocks, superchargeQ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [Matrix.mul_assoc]

/-- Commutation and conservation of conjugate supercharge Q† with the SUSY Hamiltonian: `[H, Q†] = 0`. -/
theorem susyHamiltonian_comm_Q_dag {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [CommRing R] (V_coup : Matrix V_b V_f R) :
    (susyHamiltonian V_coup) * (superchargeQ_dag V_coup) - (superchargeQ_dag V_coup) * (susyHamiltonian V_coup) = 0 := by
  rw [susyHamiltonian_blocks, superchargeQ_dag, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [Matrix.mul_assoc]

/-! ### Section 3: Exact Affine Soloviev QPNM to BdG Decomposition -/

/-- 2x2 Soloviev Quasiparticle-Phonon Nuclear Model (QPNM) Hamiltonian matrix. -/
def qpnmMatrix {R : Type*} [CommRing R] (Eqp omega V : R) : Matrix (Fin 2) (Fin 2) R :=
  !![Eqp, V; V, Eqp + omega]

/-- Central scalar shift of the Soloviev Hamiltonian: `Eqp + ω / 2`. -/
def solovievCenter {R : Type*} [CommRing R] [Invertible (2 : R)] (Eqp omega : R) : R :=
  Eqp + ⅟(2 : R) * omega

/-- Traceless Bogoliubov-de Gennes (BdG) Hamiltonian block. -/
def bdgBlock {R : Type*} [CommRing R] (delta V : R) : Matrix (Fin 2) (Fin 2) R :=
  !![delta, V; V, -delta]

/-- Exact affine decomposition of the Soloviev QPNM Hamiltonian into scalar center and BdG block. -/
theorem qpnm_affine_bdg {R : Type*} [CommRing R] [Invertible (2 : R)] (Eqp omega V : R) :
    qpnmMatrix Eqp omega V = (solovievCenter Eqp omega) • (1 : Matrix (Fin 2) (Fin 2) R) + bdgBlock (- ⅟(2 : R) * omega) V := by
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  ext i j
  fin_cases i <;> fin_cases j
  · simp [qpnmMatrix, solovievCenter, bdgBlock]
  · simp [qpnmMatrix, solovievCenter, bdgBlock]
  · simp [qpnmMatrix, solovievCenter, bdgBlock]
  · simp [qpnmMatrix, solovievCenter, bdgBlock]
    calc Eqp + omega = Eqp + omega * (⅟(2 : R) * 2) := by rw [h2, mul_one]
    _ = Eqp + ⅟(2 : R) * omega + ⅟(2 : R) * omega := by ring

/-- Squaring of the BdG Hamiltonian block yielding the relativistic dispersion scalar: `H_BdG² = (δ² + V²) I`. -/
theorem bdgBlock_sq {R : Type*} [CommRing R] (delta V : R) :
    (bdgBlock delta V) * (bdgBlock delta V) = (delta^2 + V^2) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [bdgBlock, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  }

/-- Pauli tau_1 matrix representing the particle-hole / Andreev reflection generator. -/
def tau1 (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

/-- Involutive property of the Andreev generator: `τ₁² = 1`. -/
theorem tau1_sq (R : Type*) [CommRing R] : (tau1 R) * (tau1 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tau1, Matrix.mul_apply, Fin.sum_univ_two]

/-- Andreev particle-hole sign reversal of the BdG block under τ₁ conjugation: `τ₁ H(δ, V) τ₁ = - H(δ, -V)`. -/
theorem andreev_bdg_sign_reversal {R : Type*} [CommRing R] (delta V : R) :
    (tau1 R) * (bdgBlock delta V) * (tau1 R) = - bdgBlock delta (-V) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tau1, bdgBlock, Matrix.mul_apply, Fin.sum_univ_two]

/-- Andreev particle-hole swap of the energy gap under τ₁ conjugation: `τ₁ H(δ, V) τ₁ = H(-δ, V)`. -/
theorem andreev_bdg_swap {R : Type*} [CommRing R] (delta V : R) :
    (tau1 R) * (bdgBlock delta V) * (tau1 R) = bdgBlock (-delta) V := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tau1, bdgBlock, Matrix.mul_apply, Fin.sum_univ_two]

/-- Tracelessness of the BdG block: `Tr(H_BdG) = 0`. -/
theorem bdgBlock_traceless {R : Type*} [CommRing R] (delta V : R) :
    Matrix.trace (bdgBlock delta V) = 0 := by
  simp [Matrix.trace, Matrix.diag, bdgBlock, Fin.sum_univ_two]

/-- Exact determinant of the BdG block: `det(H_BdG) = -(δ² + V²)`. -/
theorem bdgBlock_det {R : Type*} [CommRing R] (delta V : R) :
    Matrix.det (bdgBlock delta V) = - (delta^2 + V^2) := by
  rw [bdgBlock, Matrix.det_fin_two_of]
  ring

/-! ### Section 4: Master Verification Certificate -/

/-- Master verification certificate bundling all fundamental theorems of Nuclear Quasiphonon Krein SUSY. -/
structure NuclearQuasiphononKreinSUSYCertificate : Prop where
  -- Section 1: Krein supercarrier & fundamental involutions
  krein_metric_sq : ∀ (V_b V_f : Type*) [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f] (R : Type*) [CommRing R],
    (kreinMetric V_b V_f R) * (kreinMetric V_b V_f R) = 1
  sheet_swap_sq : ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R],
    (sheetSwap V R) * (sheetSwap V R) = 1
  krein_sheet_swap_anticomm : ∀ (V : Type*) [DecidableEq V] [Fintype V] (R : Type*) [CommRing R],
    (kreinMetric V V R) * (sheetSwap V R) + (sheetSwap V R) * (kreinMetric V V R) = 0

  -- Section 2: Real pseudo-SUSY supercharges & SUSY Hamiltonian
  supercharge_Q_sq : ∀ {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [CommRing R] (V_coup : Matrix V_b V_f R),
    (superchargeQ V_coup) * (superchargeQ V_coup) = 0
  supercharge_Q_dag_sq : ∀ {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [CommRing R] (V_coup : Matrix V_b V_f R),
    (superchargeQ_dag V_coup) * (superchargeQ_dag V_coup) = 0
  susy_hamiltonian_blocks : ∀ {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [CommRing R] (V_coup : Matrix V_b V_f R),
    susyHamiltonian V_coup = Matrix.fromBlocks (V_coup * V_coupᵀ) 0 0 (V_coupᵀ * V_coup)
  susy_hamiltonian_comm_Q : ∀ {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [CommRing R] (V_coup : Matrix V_b V_f R),
    (susyHamiltonian V_coup) * (superchargeQ V_coup) - (superchargeQ V_coup) * (susyHamiltonian V_coup) = 0
  susy_hamiltonian_comm_Q_dag : ∀ {V_b V_f : Type*} [DecidableEq V_b] [Fintype V_b] [DecidableEq V_f] [Fintype V_f]
    {R : Type*} [CommRing R] (V_coup : Matrix V_b V_f R),
    (susyHamiltonian V_coup) * (superchargeQ_dag V_coup) - (superchargeQ_dag V_coup) * (susyHamiltonian V_coup) = 0

  -- Section 3: Exact affine Soloviev QPNM to BdG decomposition
  qpnm_affine_bdg : ∀ {R : Type*} [CommRing R] [Invertible (2 : R)] (Eqp omega V : R),
    qpnmMatrix Eqp omega V = (solovievCenter Eqp omega) • (1 : Matrix (Fin 2) (Fin 2) R) + bdgBlock (- ⅟(2 : R) * omega) V
  bdg_block_sq : ∀ {R : Type*} [CommRing R] (delta V : R),
    (bdgBlock delta V) * (bdgBlock delta V) = (delta^2 + V^2) • (1 : Matrix (Fin 2) (Fin 2) R)
  tau1_sq : ∀ (R : Type*) [CommRing R], (tau1 R) * (tau1 R) = 1
  andreev_bdg_sign_reversal : ∀ {R : Type*} [CommRing R] (delta V : R),
    (tau1 R) * (bdgBlock delta V) * (tau1 R) = - bdgBlock delta (-V)
  andreev_bdg_swap : ∀ {R : Type*} [CommRing R] (delta V : R),
    (tau1 R) * (bdgBlock delta V) * (tau1 R) = bdgBlock (-delta) V
  bdg_block_traceless : ∀ {R : Type*} [CommRing R] (delta V : R),
    Matrix.trace (bdgBlock delta V) = 0
  bdg_block_det : ∀ {R : Type*} [CommRing R] (delta V : R),
    Matrix.det (bdgBlock delta V) = - (delta^2 + V^2)

/-- Universal compilation theorem for Nuclear Quasiphonon Krein SUSY. -/
theorem compile_nuclear_quasiphonon_krein_susy : NuclearQuasiphononKreinSUSYCertificate where
  krein_metric_sq := fun V_b V_f _ _ _ _ R _ => kreinMetric_sq V_b V_f R
  sheet_swap_sq := fun V _ _ R _ => sheetSwap_sq V R
  krein_sheet_swap_anticomm := fun V _ _ R _ => krein_sheetSwap_anticomm V R
  supercharge_Q_sq := fun V_coup => superchargeQ_sq V_coup
  supercharge_Q_dag_sq := fun V_coup => superchargeQ_dag_sq V_coup
  susy_hamiltonian_blocks := fun V_coup => susyHamiltonian_blocks V_coup
  susy_hamiltonian_comm_Q := fun V_coup => susyHamiltonian_comm_Q V_coup
  susy_hamiltonian_comm_Q_dag := fun V_coup => susyHamiltonian_comm_Q_dag V_coup
  qpnm_affine_bdg := fun Eqp omega V => qpnm_affine_bdg Eqp omega V
  bdg_block_sq := fun delta V => bdgBlock_sq delta V
  tau1_sq := fun R _ => tau1_sq R
  andreev_bdg_sign_reversal := fun delta V => andreev_bdg_sign_reversal delta V
  andreev_bdg_swap := fun delta V => andreev_bdg_swap delta V
  bdg_block_traceless := fun delta V => bdgBlock_traceless delta V
  bdg_block_det := fun delta V => bdgBlock_det delta V

end Experimental.Sandbox.Nuclear.NuclearQuasiphononKreinSUSY
