import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.Zeta

open Omega

/-!
The paper-level statement also lists the singular values and the hidden-space
decomposition.  The owner below isolates the finite operator that those claims
must be derived from.  Its entries are defined from the actual BinFold fibers;
no certificate or exhaustive truth proposition is used.
-/

/-- Incidence matrix of the `m = 6` BinFold fibers. -/
def window6CoarseGrainingMatrix : Matrix (X 6) (Fin 64) ℂ :=
  fun x n => if cBinFold 6 n.val = x then 1 else 0

/-- Conjugate-transpose incidence matrix. -/
def window6CoarseGrainingAdjoint : Matrix (Fin 64) (X 6) ℂ :=
  fun n x => star (window6CoarseGrainingMatrix x n)

/-- The finite Gram matrix `B*B`. -/
noncomputable def window6CoarseGrainingGram : Matrix (Fin 64) (Fin 64) ℂ :=
  window6CoarseGrainingAdjoint * window6CoarseGrainingMatrix

/-- Block-all-ones kernel determined by equality of BinFold fibers. -/
def window6FiberGramKernel (n m : Fin 64) : ℂ :=
  if cBinFold 6 n.val = cBinFold 6 m.val then 1 else 0

theorem window6CoarseGrainingMatrix_entry (x : X 6) (n : Fin 64) :
    window6CoarseGrainingMatrix x n =
      if cBinFold 6 n.val = x then 1 else 0 := by
  rfl

theorem window6CoarseGrainingGram_entry (n m : Fin 64) :
    window6CoarseGrainingGram n m = window6FiberGramKernel n m := by
  classical
  simp [window6CoarseGrainingGram, window6CoarseGrainingAdjoint,
    window6CoarseGrainingMatrix, window6FiberGramKernel, Matrix.mul_apply]

/-- Finite operator core of
`thm:xi-time-part55d-window6-coarse-graining-three-singular-values`.

The advertised singular-value multiplicities remain an explicit downstream
goal; this theorem proves the exact fiber Gram kernel from which they must be
derived.
-/
theorem paper_xi_time_part55d_window6_coarse_graining_three_singular_values :
    ∀ n m : Fin 64,
      window6CoarseGrainingGram n m = window6FiberGramKernel n m := by
  intro n m
  exact window6CoarseGrainingGram_entry n m

end Omega.Zeta
