import Mathlib

namespace InfoGeometry.Canonical.AtiyahSingerWittenIndexBridge

open Matrix

/-!
# Finite Atiyah-Singer/Witten Index Bridge

This module owns only the finite algebraic corridor:

* the doubled `4 + 4` boundary truncation has a chirality/parity matrix;
* its bosonic and fermionic diagonal multiplicities cancel;
* therefore the beta-zero finite graded supertrace is `0`;
* any topological index identified with this finite analytic readout is also
  `0`, but only under an explicit equality premise.

No theorem below proves the continuum Atiyah-Singer theorem, a heat-kernel
limit, an analytic Fredholm index, an A-hat genus formula, C*-completion,
or spontaneous supersymmetry breaking/non-breaking.

#### BUCKET 1: CLOSED FINITE THEOREMS
`witten_index_zero`, `grading_operator_trace_zero`, and the diagonal readouts
are closed finite matrix facts over `ℝ`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
`topological_index_zero_of_identification` depends on the explicit premise that
the chosen topological index value is equal to the finite Witten index.

#### BUCKET 3: OPEN CLOSURE DEBT
Continuum geometry, Atiyah-Singer heat-kernel analysis, genuine A-hat genus
identification, and physical supersymmetry-breaking claims.
-/

/--
The finite grading operator `(-1)^F` on the doubled space.

The first four coordinates are assigned parity `+1`; the last four are assigned
parity `-1`. In the bridge dictionary this is a finite chirality matrix.
-/
def grading_operator : Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j => if i = j then if (i : Nat) < 4 then 1 else -1 else 0

/-- The beta-zero finite Witten index: `Tr((-1)^F)`. -/
def witten_index : ℝ :=
  grading_operator.trace

/-- Explicit expansion of a sum over `Fin 8`. -/
lemma sum_fin_8 (f : Fin 8 → ℝ) :
  ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  have h_eq : (Finset.univ : Finset (Fin 8)) = {0, 1, 2, 3, 4, 5, 6, 7} := rfl
  rw [h_eq]
  simp
  ring

/-- The finite chirality matrix has four `+1` diagonal entries. -/
theorem grading_operator_diag_physical
    (i : Fin 8) (hi : (i : Nat) < 4) :
    grading_operator i i = 1 := by
  simp [grading_operator, hi]

/-- The finite chirality matrix has four `-1` diagonal entries. -/
theorem grading_operator_diag_ghost
    (i : Fin 8) (hi : 4 ≤ (i : Nat)) :
    grading_operator i i = -1 := by
  have hnot : ¬ (i : Nat) < 4 := Nat.not_lt.mpr hi
  simp [grading_operator, hnot]

/-- The finite grading/chirality trace vanishes by `4 - 4` cancellation. -/
theorem grading_operator_trace_zero :
    grading_operator.trace = 0 := by
  dsimp [grading_operator, Matrix.trace, Matrix.diag]
  rw [sum_fin_8]
  norm_num

/--
The finite beta-zero Witten index of the doubled Cantor-boundary truncation is
exactly zero.
-/
theorem witten_index_zero : witten_index = 0 := by
  simpa [witten_index] using grading_operator_trace_zero

/--
Conditional finite Atiyah-Singer readout.

If a separately supplied topological index value has been identified with the
finite analytic Witten index in this model, then that supplied topological
index value is zero.
-/
theorem topological_index_zero_of_identification
    (topologicalIndex : ℝ)
    (hidentification : topologicalIndex = witten_index) :
    topologicalIndex = 0 := by
  rw [hidentification, witten_index_zero]

end InfoGeometry.Canonical.AtiyahSingerWittenIndexBridge
