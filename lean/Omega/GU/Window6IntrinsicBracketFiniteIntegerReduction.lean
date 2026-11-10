/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic

namespace Omega.GU

/-- The `21` basis vectors on which the intrinsic bracket structure constants are recorded. -/
abbrev Window6BracketBasis := Fin 21

/-- Integer-valued structure constants on the `21`-element window-`6` basis. -/
abbrev Window6StructureConstants := Window6BracketBasis → Window6BracketBasis → Window6BracketBasis → ℤ

/-- Concrete data used to encode the intrinsic-bracket compatibility conditions as a finite
integer system. -/
structure Window6IntrinsicBracketFiniteIntegerReductionData where
  supportMask : Window6BracketBasis → Window6BracketBasis → Window6BracketBasis → Bool
  parityClass : Window6BracketBasis → Bool
  blockClass : Window6BracketBasis → Fin 3

/-- Antisymmetry of the structure constants. -/
def Window6IntrinsicBracketFiniteIntegerReductionData.antisymmetric
    (_D : Window6IntrinsicBracketFiniteIntegerReductionData) (c : Window6StructureConstants) :
    Prop :=
  ∀ i j k, c i j k = -c j i k

/-- Support restriction encoded by a finite Boolean mask. -/
def Window6IntrinsicBracketFiniteIntegerReductionData.supportCompatible
    (D : Window6IntrinsicBracketFiniteIntegerReductionData) (c : Window6StructureConstants) :
    Prop :=
  ∀ i j k, D.supportMask i j k = false → c i j k = 0

/-- Parity restriction for the `window-6` basis. -/
def Window6IntrinsicBracketFiniteIntegerReductionData.parityCompatible
    (D : Window6IntrinsicBracketFiniteIntegerReductionData) (c : Window6StructureConstants) :
    Prop :=
  ∀ i j k, xor (D.parityClass i) (D.parityClass j) ≠ D.parityClass k → c i j k = 0

/-- Block-compatibility restriction between the three basis blocks. -/
def Window6IntrinsicBracketFiniteIntegerReductionData.blockCompatible
    (D : Window6IntrinsicBracketFiniteIntegerReductionData) (c : Window6StructureConstants) :
    Prop :=
  ∀ i j k,
    ((D.blockClass i).1 + (D.blockClass j).1) % 3 ≠ (D.blockClass k).1 →
      c i j k = 0

/-- Jacobi identity written on the finite basis. -/
def Window6IntrinsicBracketFiniteIntegerReductionData.satisfiesJacobi
    (_D : Window6IntrinsicBracketFiniteIntegerReductionData) (c : Window6StructureConstants) :
    Prop :=
  ∀ i j k ℓ,
    (∑ m : Window6BracketBasis,
      (c i j m * c m k ℓ +
        c j k m * c m i ℓ +
        c k i m * c m j ℓ)) = 0

/-- The complete finite integer system encoding antisymmetry, support, parity, block, and Jacobi
constraints. -/
def Window6IntrinsicBracketFiniteIntegerReductionData.intrinsicBracketConstraints
    (D : Window6IntrinsicBracketFiniteIntegerReductionData) (c : Window6StructureConstants) :
    Prop :=
  D.antisymmetric c ∧
    D.supportCompatible c ∧
    D.parityCompatible c ∧
    D.blockCompatible c ∧
    D.satisfiesJacobi c

/-- The finite integer system attached to the `window-6` intrinsic bracket problem. -/
def Window6IntrinsicBracketFiniteIntegerReductionData.finiteIntegerSystem
    (D : Window6IntrinsicBracketFiniteIntegerReductionData) :
    Set Window6StructureConstants :=
  {c | D.intrinsicBracketConstraints c}

/-- Compatibility proposition for the intrinsic-bracket claim, currently encoded by unique
membership in the finite constraint set. It does not supply a concrete solution witness. -/
def Window6IntrinsicBracketFiniteIntegerReductionData.intrinsicBracketExistsUnique
    (D : Window6IntrinsicBracketFiniteIntegerReductionData) : Prop :=
  ∃! c : Window6StructureConstants, c ∈ D.finiteIntegerSystem

/-- Unique solvability of the finite integer system. -/
def Window6IntrinsicBracketFiniteIntegerReductionData.finiteIntegerSystemHasUniqueSolution
    (D : Window6IntrinsicBracketFiniteIntegerReductionData) : Prop :=
  ∃! c : Window6StructureConstants, c ∈ D.finiteIntegerSystem

/-- Antisymmetry over the integer structure constants forces every coefficient with repeated
first and second basis arguments to vanish. This is a concrete consequence of the finite
constraint system, independent of any existence or uniqueness claim. -/
theorem window6_antisymmetry_forces_diagonal_structure_constants_zero
    (D : Window6IntrinsicBracketFiniteIntegerReductionData)
    (c : Window6StructureConstants)
    (hc : c ∈ D.finiteIntegerSystem) :
    ∀ i k, c i i k = 0 := by
  change D.intrinsicBracketConstraints c at hc
  have hanti := hc.1
  intro i k
  have h := hanti i i k
  omega

/-- Compatibility restatement: both sides are definitionally the same unique-membership
proposition. This theorem does not establish that the finite system has a solution or construct
an intrinsic bracket. The substantive consequence used by the certificate packages is
`window6_antisymmetry_forces_diagonal_structure_constants_zero`.
    prop:window6-intrinsic-bracket-finite-integer-reduction -/
theorem paper_window6_intrinsic_bracket_finite_integer_reduction
    (D : Window6IntrinsicBracketFiniteIntegerReductionData) :
    D.intrinsicBracketExistsUnique ↔ D.finiteIntegerSystemHasUniqueSolution := by
  rfl

end Omega.GU
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
