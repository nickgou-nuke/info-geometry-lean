import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite spin anyon braid operators
-/

noncomputable section

namespace InfoGeometry.Algebra.AnyonFiniteSpinBraid

/-- A finite `N`-site spin configuration carrier. -/
abbrev SpinSpace (N : ℕ) := Fin N → Fin 2

/-- Endomorphisms of the finite spin configuration carrier. -/
abbrev SpinOperator (N : ℕ) := SpinSpace N → SpinSpace N

/-- Number of adjacent Artin generators for `B_N`, using zero when `N = 0`. -/
def braidGeneratorCount (N : ℕ) : ℕ :=
  N - 1

/-- Generator index type for the adjacent Artin generators `σᵢ` of `B_N`. -/
abbrev ArtinGenerator (N : ℕ) := Fin (braidGeneratorCount N)

/-- The index of an Artin generator is always bounded by `N - 1`. -/
theorem artin_generator_index {N : ℕ} (i : ArtinGenerator N) :
    (i : ℕ) < braidGeneratorCount N :=
  i.isLt

/--
A finite operator-level Artin braid representation on the `N`-site spin carrier.
The braid laws are fields: concrete model files must provide them explicitly.
-/
structure ArtinBraidOperators (N : ℕ) where
  sigma : ArtinGenerator N → SpinOperator N
  braid_adjacent :
    ∀ i j : ArtinGenerator N,
      (i : ℕ) + 1 = j →
        sigma i ∘ sigma j ∘ sigma i = sigma j ∘ sigma i ∘ sigma j
  braid_far_comm :
    ∀ i j : ArtinGenerator N,
      (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i →
        sigma i ∘ sigma j = sigma j ∘ sigma i

namespace ArtinBraidOperators

variable {N : ℕ} (ops : ArtinBraidOperators N)

/-- Read back an Artin generator as a non-local spin-space operator. -/
def generatorOperator (i : ArtinGenerator N) : SpinOperator N :=
  ops.sigma i

/-- Adjacent generators satisfy the Artin braid relation by representation data. -/
theorem adjacent_relation (i j : ArtinGenerator N) (hij : (i : ℕ) + 1 = j) :
    ops.generatorOperator i ∘ ops.generatorOperator j ∘ ops.generatorOperator i =
      ops.generatorOperator j ∘ ops.generatorOperator i ∘ ops.generatorOperator j :=
  ops.braid_adjacent i j hij

/-- Far generators commute by representation data. -/
theorem far_commutation (i j : ArtinGenerator N)
    (hfar : (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i) :
    ops.generatorOperator i ∘ ops.generatorOperator j =
      ops.generatorOperator j ∘ ops.generatorOperator i :=
  ops.braid_far_comm i j hfar

end ArtinBraidOperators

end InfoGeometry.Algebra.AnyonFiniteSpinBraid

end noncomputable section
