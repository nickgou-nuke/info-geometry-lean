import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
import InfoGeometry.Quantum.PauliSoldering

/-!
# Split-Octonion Double Chiral Dirac/Pauli Soldering Bridge

This module formalizes:
1. **The Double Minkowski Pauli Soldering ($4 \times 4$ Block-Diagonal)**:
   $$\mathbb{S}_{\mathrm{diag}}(t, \mathbf{x}, \tau, \mathbf{y}) = \operatorname{diag}(\slashed{P}(t, \mathbf{x}), \slashed{Q}(\tau, \mathbf{y}))$$
2. **🏆 THEOREM 1 (Double Determinant Difference as Split-Octonion Norm)**:
   $$\det(\slashed{P}) - \det(\slashed{Q}) = N(X)$$
3. **🏆 THEOREM 2 (Energy and Mirror Scale Trace Readouts)**:
   $$\operatorname{Tr}(\slashed{P}) = 2t, \qquad \operatorname{Tr}(\slashed{Q}) = 2\tau$$
-/

noncomputable section

open Matrix
open InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
open InfoGeometry.Quantum.PauliSoldering

namespace InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge

abbrev BiSpinor := Fin 2 ⊕ Fin 2

/-- $2 \times 2$ Pauli soldering matrix $\slashed{P}(t, \mathbf{x})$. -/
def pauliSolder2x2 (t x1 x2 x3 : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  solder ((t : ℂ), (x1 : ℂ), (x2 : ℂ), (x3 : ℂ))

/-- $4 \times 4$ Double Minkowski block-diagonal matrix on $\mathbb{C}^2 \oplus \mathbb{C}^2$. -/
def doubleMinkowskiSolder (t x1 x2 x3 tau y1 y2 y3 : ℝ) : Matrix BiSpinor BiSpinor ℂ :=
  Matrix.fromBlocks
    (pauliSolder2x2 t x1 x2 x3) 0
    0 (pauliSolder2x2 tau y1 y2 y3)

/-- 🏆 THEOREM 1: The difference of the $2 \times 2$ soldered determinants matches the split-octonion norm. -/
theorem doubleMinkowskiSolder_det_diff (t x1 x2 x3 tau y1 y2 y3 : ℝ) :
    (pauliSolder2x2 t x1 x2 x3).det - (pauliSolder2x2 tau y1 y2 y3).det =
      (wittNorm (symmSection t x1 x2 x3 + antiSection tau y1 y2 y3) : ℂ) := by
  dsimp [pauliSolder2x2]
  rw [casimir_as_determinant, casimir_as_determinant]
  have h_split := (wittNorm_direct_sum t x1 x2 x3 tau y1 y2 y3).symm
  have h_cast : (t : ℂ) ^ 2 - ((x1 : ℂ) ^ 2 + (x2 : ℂ) ^ 2 + (x3 : ℂ) ^ 2) - ((tau : ℂ) ^ 2 - ((y1 : ℂ) ^ 2 + (y2 : ℂ) ^ 2 + (y3 : ℂ) ^ 2)) =
      (((t ^ 2 - (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) - (tau ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2))) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h_cast, h_split, wittNorm_eq_circularWitt]

theorem solder_trace_formula (t x1 x2 x3 : ℂ) :
    (solder (t, x1, x2, x3)).trace = 2 * t := by
  dsimp [solder, Matrix.trace, σ0, σ1, σ2, σ3]
  simp
  ring

/-- 🏆 THEOREM 2: The traces of the two blocks read out the physical energy $t$ and mirror scale $\tau$. -/
theorem doubleMinkowskiSolder_traces (t x1 x2 x3 tau y1 y2 y3 : ℝ) :
    (pauliSolder2x2 t x1 x2 x3).trace = 2 * (t : ℂ) ∧
    (pauliSolder2x2 tau y1 y2 y3).trace = 2 * (tau : ℂ) := by
  dsimp [pauliSolder2x2]
  constructor
  · rw [solder_trace_formula]
  · rw [solder_trace_formula]

end InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge
