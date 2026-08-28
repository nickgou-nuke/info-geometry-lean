import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import InfoGeometry.Physics.NuclearQuasiparticleCARBridge
import InfoGeometry.Physics.NuclearPhononRPAAlgebra

noncomputable section

open Matrix
open scoped BigOperators

namespace InfoGeometry.Physics.SolovievQPNMEigenproblem

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-!
# Soloviev Quasiparticle-Phonon Nuclear Model (QPNM) Secular Eigenproblem

This module formalizes the exact finite spectral eigenproblem for Soloviev's QPNM:
1. **The State Vector Carrier**:
   $|\Psi\rangle = C \alpha^\dagger |0\rangle + D (\alpha^\dagger Q^\dagger) |0\rangle$,
   with wave function normalization $C^2 + D^2 = 1$.
2. **The Projected QPNM Matrix**:
   $\mathcal{H}_{\text{QPNM}} = \begin{pmatrix} E_{\text{qp}} & V \\ V & E_{\text{qp}} + \omega \end{pmatrix}$,
   where $E_{\text{qp}}$ is the single-quasiparticle energy, $\omega$ is the phonon energy,
   and $V$ is the quasiparticle-phonon interaction matrix element.
3. **The Secular Characteristic Equation**:
   $P(E) = \det(\mathcal{H}_{\text{QPNM}} - E I_2) = (E_{\text{qp}} - E)(E_{\text{qp}} + \omega - E) - V^2 = 0$.
4. **The Soloviev Dispersion / Pole Equation**:
   $(E - E_{\text{qp}})(E - (E_{\text{qp}} + \omega)) = V^2$.
5. **Eigenvector Equivalence**:
   $\mathcal{H}_{\text{QPNM}} \begin{pmatrix} C \\ D \end{pmatrix} = E \begin{pmatrix} C \\ D \end{pmatrix} \iff
    \begin{cases} (E_{\text{qp}} - E) C + V D = 0 \\ V C + (E_{\text{qp}} + \omega - E) D = 0 \end{cases}$.
6. **Spectroscopic Factor**: $S_{\text{qp}} = C^2 \le 1$.

All proofs are complete in native Lean 4 with 0 `sorry`s.
-/

/-- The projected 2-level Soloviev QPNM Hamiltonian matrix. -/
def qpnmMatrix (Eqp omega V : ℝ) : M2R :=
  !![Eqp, V; V, Eqp + omega]

/-- The secular matrix $\mathcal{H}_{\text{QPNM}} - E I_2$. -/
def secularMatrix (Eqp omega V E : ℝ) : M2R :=
  qpnmMatrix Eqp omega V - E • (1 : M2R)

/-- Explicit entries of the secular matrix. -/
theorem secularMatrix_entries (Eqp omega V E : ℝ) :
    secularMatrix Eqp omega V E = !![Eqp - E, V; V, Eqp + omega - E] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [secularMatrix, qpnmMatrix]

/-- **THE SECULAR CHARACTERISTIC DETERMINANT THEOREM**:
    $\det(\mathcal{H}_{\text{QPNM}} - E I_2) = (E_{\text{qp}} - E)(E_{\text{qp}} + \omega - E) - V^2$. -/
theorem secular_determinant_eq (Eqp omega V E : ℝ) :
    det (secularMatrix Eqp omega V E) = (Eqp - E) * (Eqp + omega - E) - V ^ 2 := by
  rw [secularMatrix_entries]
  simp [det_fin_two]
  ring

/-- **THE SOLOVIEV DISPERSION / POLE THEOREM**:
    The energy eigenvalue $E$ satisfies $\det(\mathcal{H} - E I) = 0$ if and only if
    $(E - E_{\text{qp}})(E - (E_{\text{qp}} + \omega)) = V^2$. -/
theorem soloviev_dispersion_iff (Eqp omega V E : ℝ) :
    det (secularMatrix Eqp omega V E) = 0 ↔
      (E - Eqp) * (E - (Eqp + omega)) = V ^ 2 := by
  rw [secular_determinant_eq]
  have h_poly : (Eqp - E) * (Eqp + omega - E) - V ^ 2 = (E - Eqp) * (E - (Eqp + omega)) - V ^ 2 := by ring
  rw [h_poly]
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    exact sub_eq_zero.mpr h

/-- **THE EIGENVALUE EQUATION MATRIX THEOREM**:
    $\mathcal{H}_{\text{QPNM}} \begin{pmatrix} C \\ D \end{pmatrix} = E \begin{pmatrix} C \\ D \end{pmatrix}$
    is equivalent to the coupled algebraic system for quasiparticle amplitude $C$ and phonon amplitude $D$. -/
theorem qpnm_eigenvalue_system (Eqp omega V E C D : ℝ) :
    mulVec (qpnmMatrix Eqp omega V) ![C, D] = E • ![C, D] ↔
      ((Eqp - E) * C + V * D = 0 ∧ V * C + (Eqp + omega - E) * D = 0) := by
  constructor
  · intro h
    have h0 : (mulVec (qpnmMatrix Eqp omega V) ![C, D]) 0 = (E • ![C, D]) 0 := by rw [h]
    have h1 : (mulVec (qpnmMatrix Eqp omega V) ![C, D]) 1 = (E • ![C, D]) 1 := by rw [h]
    simp [qpnmMatrix, mulVec, dotProduct] at h0 h1
    constructor
    · linear_combination h0
    · linear_combination h1
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i
    · simp [qpnmMatrix, mulVec, dotProduct]
      linear_combination h0
    · simp [qpnmMatrix, mulVec, dotProduct]
      linear_combination h1

/-- Spectroscopic factor $S_{\text{qp}} = C^2$ is bounded by 1 on the normalized sphere. -/
theorem spectroscopic_factor_le_one {C D : ℝ} (h_norm : C ^ 2 + D ^ 2 = 1) :
    C ^ 2 ≤ 1 := by
  have : 0 ≤ D ^ 2 := sq_nonneg D
  linarith

/-! ### Grand Soloviev QPNM Synthesis -/

/--
🏆 **GRAND SYNTHESIS: Soloviev Quasiparticle-Phonon Nuclear Model (QPNM)**

Unifies:
1. Exact secular characteristic determinant: $\det(\mathcal{H} - E I) = (E_{\text{qp}} - E)(E_{\text{qp}} + \omega - E) - V^2$.
2. Exact Soloviev pole dispersion equation: $\det(\mathcal{H} - E I) = 0 \iff (E - E_{\text{qp}})(E - E_{\text{qp}} - \omega) = V^2$.
3. Exact eigenvector-system equivalence: $\mathcal{H} \mathbf{c} = E \mathbf{c} \iff (E_{\text{qp}} - E)C + VD = 0 \land VC + (E_{\text{qp}} + \omega - E)D = 0$.
4. Wave function normalization and spectroscopic factor bound: $C^2 + D^2 = 1 \implies S_{\text{qp}} \le 1$.
-/
theorem grand_soloviev_qpnm_synthesis
    (Eqp omega V E C D : ℝ) (h_norm : C ^ 2 + D ^ 2 = 1) :
    (det (secularMatrix Eqp omega V E) = (Eqp - E) * (Eqp + omega - E) - V ^ 2) ∧
    (det (secularMatrix Eqp omega V E) = 0 ↔ (E - Eqp) * (E - (Eqp + omega)) = V ^ 2) ∧
    (mulVec (qpnmMatrix Eqp omega V) ![C, D] = E • ![C, D] ↔
      ((Eqp - E) * C + V * D = 0 ∧ V * C + (Eqp + omega - E) * D = 0)) ∧
    (C ^ 2 ≤ 1) :=
  ⟨secular_determinant_eq Eqp omega V E,
   soloviev_dispersion_iff Eqp omega V E,
   qpnm_eigenvalue_system Eqp omega V E C D,
   spectroscopic_factor_le_one h_norm⟩

end InfoGeometry.Physics.SolovievQPNMEigenproblem
