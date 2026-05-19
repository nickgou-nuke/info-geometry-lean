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

/--
The Cartan/fixed component of a grade-zero element remains in grade zero.

This is the native link between five-graded closure and Cartan decomposition:
setwise stability of `g₀` is strong enough to keep the closure-fixed projection
inside `g₀`.
-/
theorem zero_fixedPart_mem
    {x : L}
    (hx : x ∈ G.gZero) :
    G.closure.fixedPart x ∈ G.gZero := by
  unfold ClosureInvolution.LinearClosureInvolution.fixedPart
  exact G.gZero.smul_mem (1 / 2 : ℝ)
    (G.gZero.add_mem hx (G.maps_zero_to_zero x hx))

/--
The Cartan/anti-fixed component of a grade-zero element remains in grade zero.

Together with `zero_fixedPart_mem`, this says the internal Cartan split of the
closure involution does not leak out of the five-grading's middle sector.
-/
theorem zero_antiPart_mem
    {x : L}
    (hx : x ∈ G.gZero) :
    G.closure.antiPart x ∈ G.gZero := by
  unfold ClosureInvolution.LinearClosureInvolution.antiPart
  exact G.gZero.smul_mem (1 / 2 : ℝ)
    (G.gZero.sub_mem hx (G.maps_zero_to_zero x hx))

/--
Grade-zero Cartan decomposition.

Every `g₀` element splits into a closure-fixed component and a closure-anti-fixed
component, and both components still lie in `g₀`.
-/
theorem zero_cartan_decomposition
    {x : L}
    (hx : x ∈ G.gZero) :
    G.closure.fixedPart x ∈ G.gZero ∧
      G.closure.antiPart x ∈ G.gZero ∧
        G.closure.fixedPart x + G.closure.antiPart x = x :=
  ⟨G.zero_fixedPart_mem hx, G.zero_antiPart_mem hx, G.closure.fixed_add_anti_decomposition x⟩

/-- The span of the opposite grade-one sectors `g₋₁ ⊔ g₊₁`. -/
def gradeOnePair : Submodule ℝ L :=
  G.gNegOne ⊔ G.gPosOne

/-- The span of the opposite grade-two sectors `g₋₂ ⊔ g₊₂`. -/
def gradeTwoPair : Submodule ℝ L :=
  G.gNegTwo ⊔ G.gPosTwo

/-- The opposite grade-one pair is stable under closure. -/
theorem gradeOnePair_setwise_stable :
    G.closure.SetwiseStable G.gradeOnePair := by
  intro x hx
  rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
  simpa [map_add] using (G.gradeOnePair).add_mem
    (Submodule.mem_sup_right (S := G.gNegOne) (T := G.gPosOne)
      (G.maps_negOne_to_posOne y hy))
    (Submodule.mem_sup_left (S := G.gNegOne) (T := G.gPosOne)
      (G.maps_posOne_to_negOne z hz))

/-- The opposite grade-two pair is stable under closure. -/
theorem gradeTwoPair_setwise_stable :
    G.closure.SetwiseStable G.gradeTwoPair := by
  intro x hx
  rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
  simpa [map_add] using (G.gradeTwoPair).add_mem
    (Submodule.mem_sup_right (S := G.gNegTwo) (T := G.gPosTwo)
      (G.maps_negTwo_to_posTwo y hy))
    (Submodule.mem_sup_left (S := G.gNegTwo) (T := G.gPosTwo)
      (G.maps_posTwo_to_negTwo z hz))

/--
The Cartan/fixed component of a grade `-1` element lies in the opposite
grade-one pair.
-/
theorem negOne_fixedPart_mem_gradeOnePair
    {x : L}
    (hx : x ∈ G.gNegOne) :
    G.closure.fixedPart x ∈ G.gradeOnePair := by
  unfold ClosureInvolution.LinearClosureInvolution.fixedPart gradeOnePair
  exact (G.gNegOne ⊔ G.gPosOne).smul_mem (1 / 2 : ℝ)
    ((G.gNegOne ⊔ G.gPosOne).add_mem
      ((show G.gNegOne ≤ G.gNegOne ⊔ G.gPosOne from le_sup_left) hx)
      ((show G.gPosOne ≤ G.gNegOne ⊔ G.gPosOne from le_sup_right)
        (G.maps_negOne_to_posOne x hx)))

/--
The Cartan/anti-fixed component of a grade `-1` element lies in the opposite
grade-one pair.
-/
theorem negOne_antiPart_mem_gradeOnePair
    {x : L}
    (hx : x ∈ G.gNegOne) :
    G.closure.antiPart x ∈ G.gradeOnePair := by
  unfold ClosureInvolution.LinearClosureInvolution.antiPart gradeOnePair
  exact (G.gNegOne ⊔ G.gPosOne).smul_mem (1 / 2 : ℝ)
    ((G.gNegOne ⊔ G.gPosOne).sub_mem
      ((show G.gNegOne ≤ G.gNegOne ⊔ G.gPosOne from le_sup_left) hx)
      ((show G.gPosOne ≤ G.gNegOne ⊔ G.gPosOne from le_sup_right)
        (G.maps_negOne_to_posOne x hx)))

/-- Grade `-1` Cartan decomposition inside `g₋₁ ⊔ g₊₁`. -/
theorem negOne_cartan_decomposition
    {x : L}
    (hx : x ∈ G.gNegOne) :
    G.closure.fixedPart x ∈ G.gradeOnePair ∧
      G.closure.antiPart x ∈ G.gradeOnePair ∧
        G.closure.fixedPart x + G.closure.antiPart x = x :=
  ⟨G.negOne_fixedPart_mem_gradeOnePair hx, G.negOne_antiPart_mem_gradeOnePair hx,
    G.closure.fixed_add_anti_decomposition x⟩

/-- The Cartan/fixed component of a grade `+1` element lies in `g₋₁ ⊔ g₊₁`. -/
theorem posOne_fixedPart_mem_gradeOnePair
    {x : L}
    (hx : x ∈ G.gPosOne) :
    G.closure.fixedPart x ∈ G.gradeOnePair := by
  unfold ClosureInvolution.LinearClosureInvolution.fixedPart gradeOnePair
  exact (G.gNegOne ⊔ G.gPosOne).smul_mem (1 / 2 : ℝ)
    ((G.gNegOne ⊔ G.gPosOne).add_mem
      ((show G.gPosOne ≤ G.gNegOne ⊔ G.gPosOne from le_sup_right) hx)
      ((show G.gNegOne ≤ G.gNegOne ⊔ G.gPosOne from le_sup_left)
        (G.maps_posOne_to_negOne x hx)))

/-- The Cartan/anti-fixed component of a grade `+1` element lies in `g₋₁ ⊔ g₊₁`. -/
theorem posOne_antiPart_mem_gradeOnePair
    {x : L}
    (hx : x ∈ G.gPosOne) :
    G.closure.antiPart x ∈ G.gradeOnePair := by
  unfold ClosureInvolution.LinearClosureInvolution.antiPart gradeOnePair
  exact (G.gNegOne ⊔ G.gPosOne).smul_mem (1 / 2 : ℝ)
    ((G.gNegOne ⊔ G.gPosOne).sub_mem
      ((show G.gPosOne ≤ G.gNegOne ⊔ G.gPosOne from le_sup_right) hx)
      ((show G.gNegOne ≤ G.gNegOne ⊔ G.gPosOne from le_sup_left)
        (G.maps_posOne_to_negOne x hx)))

/-- Grade `+1` Cartan decomposition inside `g₋₁ ⊔ g₊₁`. -/
theorem posOne_cartan_decomposition
    {x : L}
    (hx : x ∈ G.gPosOne) :
    G.closure.fixedPart x ∈ G.gradeOnePair ∧
      G.closure.antiPart x ∈ G.gradeOnePair ∧
        G.closure.fixedPart x + G.closure.antiPart x = x :=
  ⟨G.posOne_fixedPart_mem_gradeOnePair hx, G.posOne_antiPart_mem_gradeOnePair hx,
    G.closure.fixed_add_anti_decomposition x⟩

/-- The Cartan/fixed component of a grade `-2` element lies in `g₋₂ ⊔ g₊₂`. -/
theorem negTwo_fixedPart_mem_gradeTwoPair
    {x : L}
    (hx : x ∈ G.gNegTwo) :
    G.closure.fixedPart x ∈ G.gradeTwoPair := by
  unfold ClosureInvolution.LinearClosureInvolution.fixedPart gradeTwoPair
  exact (G.gNegTwo ⊔ G.gPosTwo).smul_mem (1 / 2 : ℝ)
    ((G.gNegTwo ⊔ G.gPosTwo).add_mem
      ((show G.gNegTwo ≤ G.gNegTwo ⊔ G.gPosTwo from le_sup_left) hx)
      ((show G.gPosTwo ≤ G.gNegTwo ⊔ G.gPosTwo from le_sup_right)
        (G.maps_negTwo_to_posTwo x hx)))

/-- The Cartan/anti-fixed component of a grade `-2` element lies in `g₋₂ ⊔ g₊₂`. -/
theorem negTwo_antiPart_mem_gradeTwoPair
    {x : L}
    (hx : x ∈ G.gNegTwo) :
    G.closure.antiPart x ∈ G.gradeTwoPair := by
  unfold ClosureInvolution.LinearClosureInvolution.antiPart gradeTwoPair
  exact (G.gNegTwo ⊔ G.gPosTwo).smul_mem (1 / 2 : ℝ)
    ((G.gNegTwo ⊔ G.gPosTwo).sub_mem
      ((show G.gNegTwo ≤ G.gNegTwo ⊔ G.gPosTwo from le_sup_left) hx)
      ((show G.gPosTwo ≤ G.gNegTwo ⊔ G.gPosTwo from le_sup_right)
        (G.maps_negTwo_to_posTwo x hx)))

/-- Grade `-2` Cartan decomposition inside `g₋₂ ⊔ g₊₂`. -/
theorem negTwo_cartan_decomposition
    {x : L}
    (hx : x ∈ G.gNegTwo) :
    G.closure.fixedPart x ∈ G.gradeTwoPair ∧
      G.closure.antiPart x ∈ G.gradeTwoPair ∧
        G.closure.fixedPart x + G.closure.antiPart x = x :=
  ⟨G.negTwo_fixedPart_mem_gradeTwoPair hx, G.negTwo_antiPart_mem_gradeTwoPair hx,
    G.closure.fixed_add_anti_decomposition x⟩

/-- The Cartan/fixed component of a grade `+2` element lies in `g₋₂ ⊔ g₊₂`. -/
theorem posTwo_fixedPart_mem_gradeTwoPair
    {x : L}
    (hx : x ∈ G.gPosTwo) :
    G.closure.fixedPart x ∈ G.gradeTwoPair := by
  unfold ClosureInvolution.LinearClosureInvolution.fixedPart gradeTwoPair
  exact (G.gNegTwo ⊔ G.gPosTwo).smul_mem (1 / 2 : ℝ)
    ((G.gNegTwo ⊔ G.gPosTwo).add_mem
      ((show G.gPosTwo ≤ G.gNegTwo ⊔ G.gPosTwo from le_sup_right) hx)
      ((show G.gNegTwo ≤ G.gNegTwo ⊔ G.gPosTwo from le_sup_left)
        (G.maps_posTwo_to_negTwo x hx)))

/-- The Cartan/anti-fixed component of a grade `+2` element lies in `g₋₂ ⊔ g₊₂`. -/
theorem posTwo_antiPart_mem_gradeTwoPair
    {x : L}
    (hx : x ∈ G.gPosTwo) :
    G.closure.antiPart x ∈ G.gradeTwoPair := by
  unfold ClosureInvolution.LinearClosureInvolution.antiPart gradeTwoPair
  exact (G.gNegTwo ⊔ G.gPosTwo).smul_mem (1 / 2 : ℝ)
    ((G.gNegTwo ⊔ G.gPosTwo).sub_mem
      ((show G.gPosTwo ≤ G.gNegTwo ⊔ G.gPosTwo from le_sup_right) hx)
      ((show G.gNegTwo ≤ G.gNegTwo ⊔ G.gPosTwo from le_sup_left)
        (G.maps_posTwo_to_negTwo x hx)))

/-- Grade `+2` Cartan decomposition inside `g₋₂ ⊔ g₊₂`. -/
theorem posTwo_cartan_decomposition
    {x : L}
    (hx : x ∈ G.gPosTwo) :
    G.closure.fixedPart x ∈ G.gradeTwoPair ∧
      G.closure.antiPart x ∈ G.gradeTwoPair ∧
        G.closure.fixedPart x + G.closure.antiPart x = x :=
  ⟨G.posTwo_fixedPart_mem_gradeTwoPair hx, G.posTwo_antiPart_mem_gradeTwoPair hx,
    G.closure.fixed_add_anti_decomposition x⟩

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
