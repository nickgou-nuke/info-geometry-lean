import InfoGeometry.Arithmetic.BostConnesCriticality
import InfoGeometry.Arithmetic.SpectralGap
import InfoGeometry.Arithmetic.MasterIdentity
import InfoGeometry.Clifford.LogCftMonodromy
import InfoGeometry.Canonical.SplitCliffordJordanWigner
import InfoGeometry.OperatorAlgebra.LogExchangeMonodromy
import InfoGeometry.Algebraic.OddNilpotentOSpBridge
import DAG.AffineProjectiveClosure

/-!
# Finite Jordan-cell readouts

This owner contains only the explicit `Fin 2` Jordan-cell decomposition and
its square-zero matrix consequences.  It does not define a thermodynamic
flow, a KMS phase transition, correlation asymptotics, or a global
`osp(1|2)` representation.
-/

open Complex
open Matrix

namespace InfoGeometry.Arithmetic.LogCFTCritical

open BostConnesCriticality
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Canonical.SplitCliffordJordanWigner

/--
At the critical point `β = 1`, the Virasoro `L₀` on the logarithmic pair is the
rank-two Jordan cell `h·I + N`.  The proof factors through the already-checked
`l0_cell_decomposition` in `LogCftMonodromy`.
-/
theorem virasoro_jordan_block_at_critical (h : ℂ) :
    let L0 := virasoroL0Cell h
    L0 = h • (1 : Matrix (Fin 2) (Fin 2) ℂ) + jordanNilpotent :=
  l0_cell_decomposition h

/--
The stored nilpotent shear squares to zero.
-/
theorem nilpotent_jordan_square_zero :
    (jordanNilpotent : Matrix (Fin 2) (Fin 2) ℂ) * jordanNilpotent = 0 :=
  jordanNilpotent_sq

/--
Explicit entry-level description of the critical Jordan cell.

This closes the finite-matrix “osp(1|2)-style” protection claim at the level
of the explicit `Fin 2` matrices: the diagonal is constant `h`, the only
off-diagonal entry is the nilpotent `1` at `(0,1)`.
-/
theorem osp12_finite_protection_closed :
    let L0 := virasoroL0Cell h
    let N  := jordanNilpotent
    (N * N = (0 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    L0 0 0 = h ∧
    L0 0 1 = (1 : ℂ) ∧
    L0 1 0 = (0 : ℂ) ∧
    L0 1 1 = h := by
  intro L0 N
  refine ⟨jordanNilpotent_sq, rfl, rfl, rfl, rfl⟩

/--
Closure surface: the finite `osp(1|2)`-style protection claim is now reduced to
native matrix lemmas above. Global representation stability remains outside
this finite owner lane.
-/
def osp12_finite_protection (h : ℂ) : Prop :=
  let L0 := virasoroL0Cell h
  let N := jordanNilpotent
  (N * N = (0 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    L0 0 0 = h ∧
    L0 0 1 = (1 : ℂ) ∧
    L0 1 0 = (0 : ℂ) ∧
    L0 1 1 = h

theorem osp12_finite_protection_holds (h : ℂ) :
    osp12_finite_protection h := by
  simpa [osp12_finite_protection] using
    (osp12_finite_protection_closed (h := h))

end InfoGeometry.Arithmetic.LogCFTCritical
