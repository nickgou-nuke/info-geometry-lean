import Mathlib

/-!
# Sandbox: replacing `by decide` over `ℚ`

Triage for the `Tactic `decide` failed` errors in the canonical build.

Confirmed: `by decide` can never close an equality of rational matrices, because
reduction gets stuck at `instDecidableEqRat` inside `Matrix.decidableEq`.  The
site is therefore not false mathematics, it is a proof written with a tactic that
cannot run on `ℚ`.

Working replacement: unfold the product entrywise, unfold the literal matrices,
then normalize with `ring`.

Cost note: unfolding an 8x8 `!!` literal once per entry costs 64 unfoldings and
exceeds the default 200000 heartbeats, so the repair needs a scoped
`maxHeartbeats`.
-/

namespace DecideProbe

abbrev Mat8 := Matrix (Fin 8) (Fin 8) ℚ

def chiralToStandard : Mat8 :=
  !![
    1 / 2,  0,      0,     0,     1 / 2,  0,     0,     0;
    1 / 2,  0,      0,     0,    -1 / 2,  0,     0,     0;
    0,     -1 / 2,  0,     0,     0,     1 / 2,  0,     0;
    0,      1 / 2,  0,     0,     0,     1 / 2,  0,     0;
    0,      0,     -1 / 2,  0,     0,     0,     1 / 2,  0;
    0,      0,      1 / 2,  0,     0,     0,     1 / 2,  0;
    0,      0,      0,    -1 / 2,  0,     0,     0,     1 / 2;
    0,      0,      0,     1 / 2,  0,     0,     0,     1 / 2
  ]

def standardToChiral : Mat8 :=
  !![
    1,  1,  0,  0,  0,  0,  0,  0;
    0,  0, -1,  1,  0,  0,  0,  0;
    0,  0,  0,  0, -1,  1,  0,  0;
    0,  0,  0,  0,  0,  0, -1,  1;
    1, -1,  0,  0,  0,  0,  0,  0;
    0,  0,  1,  1,  0,  0,  0,  0;
    0,  0,  0,  0,  1,  1,  0,  0;
    0,  0,  0,  0,  0,  0,  1,  1
  ]

set_option maxHeartbeats 1000000 in
theorem via_simp_ring : chiralToStandard * standardToChiral = (1 : Mat8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, chiralToStandard, standardToChiral] <;> ring

set_option maxHeartbeats 1000000 in
theorem via_simp_ring_rev : standardToChiral * chiralToStandard = (1 : Mat8) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, chiralToStandard, standardToChiral] <;> ring

#print axioms via_simp_ring
#print axioms via_simp_ring_rev

end DecideProbe
