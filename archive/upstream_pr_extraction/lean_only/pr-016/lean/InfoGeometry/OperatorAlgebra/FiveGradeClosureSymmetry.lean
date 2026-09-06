/-
InfoGeometry/OperatorAlgebra/FiveGradeClosureSymmetry.lean

Five-grade closure symmetry.

This module connects a closure involution to a five-grade ledger without
collapsing setwise stability into pointwise fixedness.

The key distinction is:

  `theta(g₀) ⊆ g₀`

means grade zero survives as a sector.  It does not mean every grade-zero
element is fixed.  Pointwise survival still requires `theta x = x`.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.ClosureInvolution

noncomputable section

namespace InfoGeometry.OperatorAlgebra

open InfoGeometry.OperatorAlgebra.ClosureInvolution

/--
A closure symmetry compatible with a five-grading.

The grades are represented as submodules so that setwise stability and
membership transport are explicit Lean propositions.
-/
structure FiveGradeClosureSymmetry
    (L : Type*) [AddCommGroup L] [Module ℝ L] where
  /-- Closure involution, morally `g₋k ↔ g₊k`. -/
  closure : LinearClosureInvolution L

  gNegTwo : Submodule ℝ L
  gNegOne : Submodule ℝ L
  gZero : Submodule ℝ L
  gPosOne : Submodule ℝ L
  gPosTwo : Submodule ℝ L

  maps_negTwo_to_posTwo :
    ∀ x : L, x ∈ gNegTwo → closure.theta x ∈ gPosTwo

  maps_posTwo_to_negTwo :
    ∀ x : L, x ∈ gPosTwo → closure.theta x ∈ gNegTwo

  maps_negOne_to_posOne :
    ∀ x : L, x ∈ gNegOne → closure.theta x ∈ gPosOne

  maps_posOne_to_negOne :
    ∀ x : L, x ∈ gPosOne → closure.theta x ∈ gNegOne

  maps_zero_to_zero :
    ∀ x : L, x ∈ gZero → closure.theta x ∈ gZero

namespace FiveGradeClosureSymmetry

variable
    {L : Type*} [AddCommGroup L] [Module ℝ L]

variable (G : FiveGradeClosureSymmetry L)

/-- Grade zero survives setwise under closure. -/
theorem zero_setwise_stable :
    G.closure.SetwiseStable G.gZero :=
  G.maps_zero_to_zero

/--
A fixed grade-zero element is a pointwise survivor.

The fixedness hypothesis is essential: setwise stability alone only says the
closure image remains in grade zero.
-/
theorem fixed_zero_mem_and_fixed
    {x : L}
    (hx : x ∈ G.gZero)
    (hfix : x ∈ G.closure.Fixed) :
    x ∈ G.gZero ∧ G.closure.theta x = x :=
  G.closure.fixed_mem_of_stable G.zero_setwise_stable hx hfix

/-- A fixed grade `-1` element also lies in grade `+1`. -/
theorem fixed_negOne_mem_posOne
    {x : L}
    (hx : x ∈ G.gNegOne)
    (hfix : x ∈ G.closure.Fixed) :
    x ∈ G.gPosOne := by
  have hθ : G.closure.theta x ∈ G.gPosOne :=
    G.maps_negOne_to_posOne x hx
  rw [hfix] at hθ
  exact hθ

/-- A fixed grade `+1` element also lies in grade `-1`. -/
theorem fixed_posOne_mem_negOne
    {x : L}
    (hx : x ∈ G.gPosOne)
    (hfix : x ∈ G.closure.Fixed) :
    x ∈ G.gNegOne := by
  have hθ : G.closure.theta x ∈ G.gNegOne :=
    G.maps_posOne_to_negOne x hx
  rw [hfix] at hθ
  exact hθ

/-- A fixed grade `-2` element also lies in grade `+2`. -/
theorem fixed_negTwo_mem_posTwo
    {x : L}
    (hx : x ∈ G.gNegTwo)
    (hfix : x ∈ G.closure.Fixed) :
    x ∈ G.gPosTwo := by
  have hθ : G.closure.theta x ∈ G.gPosTwo :=
    G.maps_negTwo_to_posTwo x hx
  rw [hfix] at hθ
  exact hθ

/-- A fixed grade `+2` element also lies in grade `-2`. -/
theorem fixed_posTwo_mem_negTwo
    {x : L}
    (hx : x ∈ G.gPosTwo)
    (hfix : x ∈ G.closure.Fixed) :
    x ∈ G.gNegTwo := by
  have hθ : G.closure.theta x ∈ G.gNegTwo :=
    G.maps_posTwo_to_negTwo x hx
  rw [hfix] at hθ
  exact hθ

end FiveGradeClosureSymmetry

/--
Disjointness data for opposite grades.

When supplied, it turns the grade-swap law into an obstruction to a single
one-sided grade element being pointwise fixed.
-/
structure FiveGradeDisjointness
    {L : Type*} [AddCommGroup L] [Module ℝ L]
    (G : FiveGradeClosureSymmetry L) where
  negOne_posOne_disjoint :
    ∀ x : L, x ∈ G.gNegOne → x ∈ G.gPosOne → False

  negTwo_posTwo_disjoint :
    ∀ x : L, x ∈ G.gNegTwo → x ∈ G.gPosTwo → False

namespace FiveGradeDisjointness

variable
    {L : Type*} [AddCommGroup L] [Module ℝ L]
    {G : FiveGradeClosureSymmetry L}

/-- No grade `-1` element is pointwise fixed when grades `-1` and `+1` are disjoint. -/
theorem no_fixed_negOne
    (D : FiveGradeDisjointness G)
    {x : L}
    (hx : x ∈ G.gNegOne)
    (hfix : x ∈ G.closure.Fixed) :
    False :=
  D.negOne_posOne_disjoint x hx
    (G.fixed_negOne_mem_posOne hx hfix)

/-- No grade `+1` element is pointwise fixed when grades `-1` and `+1` are disjoint. -/
theorem no_fixed_posOne
    (D : FiveGradeDisjointness G)
    {x : L}
    (hx : x ∈ G.gPosOne)
    (hfix : x ∈ G.closure.Fixed) :
    False :=
  D.negOne_posOne_disjoint x
    (G.fixed_posOne_mem_negOne hx hfix)
    hx

/-- No grade `-2` element is pointwise fixed when grades `-2` and `+2` are disjoint. -/
theorem no_fixed_negTwo
    (D : FiveGradeDisjointness G)
    {x : L}
    (hx : x ∈ G.gNegTwo)
    (hfix : x ∈ G.closure.Fixed) :
    False :=
  D.negTwo_posTwo_disjoint x hx
    (G.fixed_negTwo_mem_posTwo hx hfix)

/-- No grade `+2` element is pointwise fixed when grades `-2` and `+2` are disjoint. -/
theorem no_fixed_posTwo
    (D : FiveGradeDisjointness G)
    {x : L}
    (hx : x ∈ G.gPosTwo)
    (hfix : x ∈ G.closure.Fixed) :
    False :=
  D.negTwo_posTwo_disjoint x
    (G.fixed_posTwo_mem_negTwo hx hfix)
    hx

end FiveGradeDisjointness

end InfoGeometry.OperatorAlgebra
