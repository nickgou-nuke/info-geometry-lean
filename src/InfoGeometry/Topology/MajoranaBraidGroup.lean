import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Majorana braid group finite computation

This file strengthens the braid/Clifford lane with a nondegenerate finite
Majorana representation of the adjacent Artin relation.  Unlike the uniform
`cliffordBraidGate` in `BraidCliffordIntegration`, the two generators below are
distinct 8×8 integer matrices obtained from real Pauli/Jordan--Wigner atoms.

The checked scope is finite and algebraic only: square-one Majoranas,
anticommutation, bivector square-minus-one, the unnormalised braid gates
`1 + γᵢγᵢ₊₁`, and their projective inverses.  No analytic, topological, or
classification claim is made here.
-/

open Matrix


namespace InfoGeometry.GrandUnification.MajoranaBraidGroup

abbrev M8Z := InfoGeometry.Algebra.FiniteSpin.Mat8Z

def gamma1 : M8Z := !![0, 0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 0, 1;
  1, 0, 0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0, 0]

def gamma2 : M8Z := !![1, 0, 0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0, 0;
  0, 0, 0, 0, -1, 0, 0, 0;
  0, 0, 0, 0, 0, -1, 0, 0;
  0, 0, 0, 0, 0, 0, -1, 0;
  0, 0, 0, 0, 0, 0, 0, -1]

def gamma3 : M8Z := !![0, 0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 0, 1;
  0, 0, 0, 0, -1, 0, 0, 0;
  0, 0, 0, 0, 0, -1, 0, 0;
  0, 0, -1, 0, 0, 0, 0, 0;
  0, 0, 0, -1, 0, 0, 0, 0;
  1, 0, 0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0, 0]

def bivector12 : M8Z := !![0, 0, 0, 0, -1, 0, 0, 0;
  0, 0, 0, 0, 0, -1, 0, 0;
  0, 0, 0, 0, 0, 0, -1, 0;
  0, 0, 0, 0, 0, 0, 0, -1;
  1, 0, 0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0, 0]

def bivector23 : M8Z := !![0, 0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 0, 1;
  0, 0, 0, 0, -1, 0, 0, 0;
  0, 0, 0, 0, 0, -1, 0, 0;
  0, 0, 1, 0, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0, 0;
  -1, 0, 0, 0, 0, 0, 0, 0;
  0, -1, 0, 0, 0, 0, 0, 0]

def braid12 : M8Z := !![1, 0, 0, 0, -1, 0, 0, 0;
  0, 1, 0, 0, 0, -1, 0, 0;
  0, 0, 1, 0, 0, 0, -1, 0;
  0, 0, 0, 1, 0, 0, 0, -1;
  1, 0, 0, 0, 1, 0, 0, 0;
  0, 1, 0, 0, 0, 1, 0, 0;
  0, 0, 1, 0, 0, 0, 1, 0;
  0, 0, 0, 1, 0, 0, 0, 1]

def braid23 : M8Z := !![1, 0, 0, 0, 0, 0, 1, 0;
  0, 1, 0, 0, 0, 0, 0, 1;
  0, 0, 1, 0, -1, 0, 0, 0;
  0, 0, 0, 1, 0, -1, 0, 0;
  0, 0, 1, 0, 1, 0, 0, 0;
  0, 0, 0, 1, 0, 1, 0, 0;
  -1, 0, 0, 0, 0, 0, 1, 0;
  0, -1, 0, 0, 0, 0, 0, 1]

def braid12InvNumerator : M8Z := !![1, 0, 0, 0, 1, 0, 0, 0;
  0, 1, 0, 0, 0, 1, 0, 0;
  0, 0, 1, 0, 0, 0, 1, 0;
  0, 0, 0, 1, 0, 0, 0, 1;
  -1, 0, 0, 0, 1, 0, 0, 0;
  0, -1, 0, 0, 0, 1, 0, 0;
  0, 0, -1, 0, 0, 0, 1, 0;
  0, 0, 0, -1, 0, 0, 0, 1]

def braid23InvNumerator : M8Z := !![1, 0, 0, 0, 0, 0, -1, 0;
  0, 1, 0, 0, 0, 0, 0, -1;
  0, 0, 1, 0, 1, 0, 0, 0;
  0, 0, 0, 1, 0, 1, 0, 0;
  0, 0, -1, 0, 1, 0, 0, 0;
  0, 0, 0, -1, 0, 1, 0, 0;
  1, 0, 0, 0, 0, 0, 1, 0;
  0, 1, 0, 0, 0, 0, 0, 1]

/-- The three finite Majorana atoms square to the identity. -/
theorem majorana_squares :
    gamma1 * gamma1 = (1 : M8Z) ∧
    gamma2 * gamma2 = (1 : M8Z) ∧
    gamma3 * gamma3 = (1 : M8Z) := by
  decide

/-- The finite Majorana atoms pairwise anticommute. -/
theorem majorana_anticommutators :
    gamma1 * gamma2 + gamma2 * gamma1 = (0 : M8Z) ∧
    gamma2 * gamma3 + gamma3 * gamma2 = (0 : M8Z) ∧
    gamma1 * gamma3 + gamma3 * gamma1 = (0 : M8Z) := by
  decide

/-- Adjacent Majorana bivectors square to `-1`, the algebraic source of braid rotations. -/
theorem majorana_bivector_squares :
    bivector12 * bivector12 = -(1 : M8Z) ∧
    bivector23 * bivector23 = -(1 : M8Z) := by
  decide

/-- The two nondegenerate Majorana braid generators satisfy the adjacent Artin relation. -/
theorem majorana_adjacent_artin :
    braid12 * braid23 * braid12 = braid23 * braid12 * braid23 := by
  decide

/-- The inverse numerators give projective invertibility: `(1+B)(1-B)=2`. -/
theorem majorana_projective_inverses :
    braid12 * braid12InvNumerator = (2 : ℤ) • (1 : M8Z) ∧
    braid23 * braid23InvNumerator = (2 : ℤ) • (1 : M8Z) := by
  decide

/-- Consolidated finite identities for the nondegenerate Majorana braid lane. -/
theorem majorana_braid_group_identities :
    (gamma1 * gamma1 = (1 : M8Z) ∧ gamma2 * gamma2 = (1 : M8Z) ∧ gamma3 * gamma3 = (1 : M8Z)) ∧
    (gamma1 * gamma2 + gamma2 * gamma1 = (0 : M8Z) ∧
      gamma2 * gamma3 + gamma3 * gamma2 = (0 : M8Z) ∧
      gamma1 * gamma3 + gamma3 * gamma1 = (0 : M8Z)) ∧
    (bivector12 * bivector12 = -(1 : M8Z) ∧ bivector23 * bivector23 = -(1 : M8Z)) ∧
    braid12 * braid23 * braid12 = braid23 * braid12 * braid23 ∧
    (braid12 * braid12InvNumerator = (2 : ℤ) • (1 : M8Z) ∧
      braid23 * braid23InvNumerator = (2 : ℤ) • (1 : M8Z)) := by
  exact ⟨majorana_squares, majorana_anticommutators, majorana_bivector_squares,
    majorana_adjacent_artin, majorana_projective_inverses⟩

end InfoGeometry.GrandUnification.MajoranaBraidGroup
