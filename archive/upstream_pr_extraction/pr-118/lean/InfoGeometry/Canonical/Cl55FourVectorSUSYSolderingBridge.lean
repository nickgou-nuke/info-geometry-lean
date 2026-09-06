import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Geometry.PauliParavectorBridge

/-!
# Cl(5,5) Four-Vector SUSY Soldering Bridge

This owner module formalizes the exact 4-vector supersymmetry algebra in $\mathrm{Cl}(5,5)$,
connecting the paravector representation of four-momentum with chiral supercharges:

1. **Pauli Paravector Representation:**
   $P = P^\mu \sigma_\mu = \begin{pmatrix} P_0 + P_3 & P_1 - i P_2 \\ P_1 + i P_2 & P_0 - P_3 \end{pmatrix}$

2. **Chiral SUSY Anticommutator Tensor:**
   $$\{Q_\alpha, \bar{Q}_{\dot{\beta}}\} = 2 (\sigma^\mu)_{\alpha \dot{\beta}} P_\mu = 2 P_{\alpha \dot{\beta}}$$

3. **Trace and Energy Positivity:**
   $$\operatorname{Tr}(\{Q, \bar{Q}\}) = 4 P_0$$

4. **Mass-Shell / Gram-Determinant Identity:**
   $$\det(\{Q, \bar{Q}\}) = 4 (P_0^2 - \vec{P}^2) = 4 m^2$$
   yielding $\det(\{Q, \bar{Q}\}) = 0$ for massless/null supercharges.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55FourVectorSUSYSolderingBridge

open Matrix
open InfoGeometry.Geometry.PauliParavectorBridge

abbrev Two := Fin 2

/-- The standard 4-vector Pauli paravector $P = P^\mu \sigma_\mu$. -/
def susyPauliParavector (p : Minkowski4) : Matrix Two Two ℂ :=
  pauliMatrix p

/-- The anticommutator tensor of chiral supercharges:
    $\{Q_\alpha, \bar{Q}_{\dot{\beta}}\} = 2 (\sigma^\mu)_{\alpha \dot{\beta}} P_\mu$. -/
def susyAnticommutator (p : Minkowski4) : Matrix Two Two ℂ :=
  (2 : ℂ) • susyPauliParavector p

/-- 🏆 THEOREM 1: The trace of the SUSY anticommutator is 4 times the Hamiltonian energy $P_0$:
    $\operatorname{Tr}(\{Q, \bar{Q}\}) = 4 P_0$. -/
theorem susy_anticommutator_trace (p : Minkowski4) :
    Matrix.trace (susyAnticommutator p) = (4 : ℂ) * (p.t : ℂ) := by
  dsimp [susyAnticommutator, susyPauliParavector, pauliMatrix, toPauliParavector,
    InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector.pauliMatrix,
    Matrix.trace]
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val']
  push_cast
  ring

/-- 🏆 THEOREM 2: The determinant of the SUSY anticommutator matrix gives $4 (P^2)$:
    $\det(\{Q, \bar{Q}\}) = 4 (P_0^2 - \vec{P}^2) = 4 m^2$. -/
theorem susy_anticommutator_det (p : Minkowski4) :
    Matrix.det (susyAnticommutator p) = (4 : ℂ) * ((p.q : ℝ) : ℂ) := by
  dsimp [susyAnticommutator]
  rw [det_smul]
  simp only [Fintype.card_fin]
  have h_det := det_pauliMatrix p
  dsimp [susyPauliParavector]
  rw [h_det]
  ring

/-- 🏆 THEOREM 3: Massless/Null SUSY particles have vanishing supercharge determinant:
    $P^2 = 0 \implies \det(\{Q, \bar{Q}\}) = 0$. -/
theorem susy_massless_det_zero (p : Minkowski4) (hp : p.IsNull) :
    Matrix.det (susyAnticommutator p) = 0 := by
  rw [susy_anticommutator_det]
  dsimp [Minkowski4.IsNull] at hp
  rw [hp]
  simp

/-- 🏆 THEOREM 4: On-mass-shell SUSY particles satisfy $\det(\{Q, \bar{Q}\} / 2) = m^2$. -/
theorem susy_on_mass_shell (p : Minkowski4) (m : ℝ) (hm : p.OnMassShell m) :
    Matrix.det (susyPauliParavector p) = ((m ^ 2 : ℝ) : ℂ) := by
  dsimp [susyPauliParavector]
  rw [det_pauliMatrix]
  dsimp [Minkowski4.OnMassShell] at hm
  rw [hm]

end InfoGeometry.Canonical.Cl55FourVectorSUSYSolderingBridge
