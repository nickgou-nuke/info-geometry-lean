/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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

end ArtinBraidOperators

end InfoGeometry.Algebra.AnyonFiniteSpinBraid

end noncomputable section
