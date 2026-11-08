/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-! # Explicit dependency order of the boundary compilation

This finite partial order specifies sufficient theorem stages, not an extracted
Lean declaration graph or physical time. Nilpotence makes a differential complex;
the metric adjoint supplies positive energy. Those are separate prerequisites
for the combined complex-with-adjoint stage, although the energy formula alone
does not require nilpotence.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceBoundaryOrder

inductive Stage
  | associative | lieJordan | peirce | compositions | differential | adjoint | hodge | tests
  deriving DecidableEq

open Stage

instance : Fintype Stage where
  elems := {associative, lieJordan, Stage.peirce, compositions, differential,
    adjoint, hodge, tests}
  complete s := by cases s <;> simp

def prerequisites : Stage → Finset Stage
  | .associative => {associative}
  | .lieJordan => {associative, lieJordan}
  | .peirce => {associative, Stage.peirce}
  | .compositions => {associative, lieJordan, compositions}
  | .differential => {associative, lieJordan, Stage.peirce, differential}
  | .adjoint => {associative, lieJordan, Stage.peirce, adjoint}
  | .hodge => {associative, lieJordan, Stage.peirce, differential, adjoint, hodge}
  | .tests => Finset.univ

theorem prerequisites_injective : Function.Injective prerequisites := by
  intro a b h
  have ha : a ∈ prerequisites b := by
    rw [← h]
    cases a <;> simp [prerequisites]
  have hb : b ∈ prerequisites a := by
    rw [h]
    cases b <;> simp [prerequisites]
  clear h
  cases a <;> cases b <;> simp_all [prerequisites]

instance : PartialOrder Stage where
  le a b := prerequisites a ⊆ prerequisites b
  le_refl _ := fun _ hx => hx
  le_trans _ _ _ hab hbc := fun _ hx => hbc (hab hx)
  le_antisymm _ _ hab hba := prerequisites_injective (Finset.Subset.antisymm hab hba)

instance : DecidableLE Stage := fun a b =>
  inferInstanceAs (Decidable (prerequisites a ⊆ prerequisites b))

theorem boundary_metric_incomparable :
    ¬ differential ≤ adjoint ∧ ¬ adjoint ≤ differential := by
  change ¬ prerequisites differential ⊆ prerequisites adjoint ∧
    ¬ prerequisites adjoint ⊆ prerequisites differential
  simp [prerequisites, Finset.subset_iff]

theorem hodge_requires_both : differential ≤ hodge ∧ adjoint ≤ hodge := by
  change prerequisites differential ⊆ prerequisites hodge ∧
    prerequisites adjoint ⊆ prerequisites hodge
  simp [prerequisites, Finset.subset_iff]

theorem mixed_and_boundary_incomparable :
    ¬ compositions ≤ differential ∧ ¬ differential ≤ compositions := by
  change ¬ prerequisites compositions ⊆ prerequisites differential ∧
    ¬ prerequisites differential ⊆ prerequisites compositions
  simp [prerequisites, Finset.subset_iff]

theorem witnesses_cover_all (s : Stage) : s ≤ tests := by
  change prerequisites s ⊆ Finset.univ
  exact Finset.subset_univ _

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Stage 1 (`associative`):**
Universal associative product reconstruction from the symmetric Jordan anticommutator
and skew-symmetric Lie commutator over `[Ring B]`. -/
theorem stage_associative_product_splitting (X Y : B) :
    anticomm X Y + comm X Y = (2 : ℤ) • (X * Y) ∧
    anticomm X Y - comm X Y = (2 : ℤ) • (Y * X) := by
  refine ⟨?_, ?_⟩ <;>
    (dsimp only [PeirceSpine.comm, PeirceSpine.anticomm]; noncomm_ring)

/-- **Stage 2 (`lieJordan`):**
Universal Poisson–Leibniz compatibility of `comm` as a derivation of `anticomm`. -/
theorem stage_lieJordan_poisson_leibniz (X Y Z : B) :
    comm X (anticomm Y Z) = anticomm (comm X Y) Z + anticomm Y (comm X Z) ∧
    comm X (comm Y Z) = comm (comm X Y) Z + comm Y (comm X Z) := by
  refine ⟨?_, ?_⟩ <;>
    (dsimp only [PeirceSpine.comm, PeirceSpine.anticomm]; noncomm_ring)

/-- **Stage 3 (`peirce`):**
Peirce four-block partition `evenGrade P X + oddGrade P X = X` and corner square-zero laws. -/
theorem stage_peirce_corner_partition
    {P : B} (hP : P * P = P) (A C X : B) :
    evenGrade P X + oddGrade P X = X ∧
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [evenGrade, oddGrade]; peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

/-- **Stage 4 (`compositions`):**
Associator composition identity relating iterated Jordan anticommutators to iterated
Lie commutators: `{X, {Y, Z}} - {Y, {X, Z}} = [[X, Y], Z]`. -/
theorem stage_compositions_jordan_associator (X Y Z : B) :
    anticomm X (anticomm Y Z) - anticomm Y (anticomm X Z) = comm (comm X Y) Z := by
  dsimp only [PeirceSpine.comm, PeirceSpine.anticomm]
  noncomm_ring

/-- **Stage 5 (`differential`):**
Upper boundary derivation `d_+(X) = [N_+, X]` is nilpotent of order 2 on `evenGrade P X` and
on same-corner elements: `[N_+, [N_+, evenGrade P X]] = 0` and `N_+ * evenGrade P X * N_+ = 0`. -/
theorem stage_differential_upper_boundary_nilpotence
    {P : B} (hP : P * P = P) (A X : B) :
    conePlus P A * evenGrade P X * conePlus P A = 0 ∧
    comm (conePlus P A) (comm (conePlus P A) (evenGrade P X)) = 0 := by
  refine ⟨?_, ?_⟩ <;>
    (simp only [evenGrade]; peirce_nf hP)

/-- **Stage 6 (`adjoint`):**
Lower codifferential derivation `d_-(X) = [N_-, X]` is square-zero on `evenGrade P X` and
its commutator with `d_+` generates the axial curvature derivation `ad_Σ`:
`[N_+, [N_-, X]] - [N_-, [N_+, X]] = [Σ, X]`. -/
theorem stage_adjoint_codifferential_curvature
    {P : B} (hP : P * P = P) (A C X : B) :
    coneMinus P C * evenGrade P X * coneMinus P C = 0 ∧
    comm (coneMinus P C) (comm (coneMinus P C) (evenGrade P X)) = 0 ∧
    comm (conePlus P A) (comm (coneMinus P C) X) -
        comm (coneMinus P C) (comm (conePlus P A) X) =
      comm (genSig P A C) X := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [evenGrade]; peirce_nf hP
  · simp only [evenGrade]; peirce_nf hP
  · peirce_nf hP

/-- **Stage 7 (`hodge`):**
Non-commutative Hodge Laplacian identity for the boundary-codifferential pair `(d_+, d_-)`:
`[N_+, [N_-, X]] + [N_-, [N_+, X]] = {V, X} - 2 • sandwichCross P A C X` and
`2 • ([N_+, [N_-, X]] + [N_-, [N_+, X]]) = -(derivSqPhi P A C X + derivSqJ P A C X)`. -/
theorem stage_hodge_laplacian_decomposition
    {P : B} (hP : P * P = P) (A C X : B) :
    comm (conePlus P A) (comm (coneMinus P C) X) +
        comm (coneMinus P C) (comm (conePlus P A) X) =
      anticomm (genV P A C) X - (2 : ℤ) • sandwichCross P A C X ∧
    (2 : ℤ) • (comm (conePlus P A) (comm (coneMinus P C) X) +
        comm (coneMinus P C) (comm (conePlus P A) X)) =
      -(derivSqPhi P A C X + derivSqJ P A C X) := by
  refine ⟨?_, ?_⟩
  · simp only [sandwichCross]; peirce_nf hP
  · simp only [derivSqPhi, derivSqJ]; peirce_nf hP

/-- **Stage 8 (`tests`):**
Master synthesis of `PeirceBoundaryOrder` combining the 8-stage poset reachability with all
seven upstream `[Ring B]` non-commutative boundary-complex theorems. -/
theorem stage_tests_peirce_boundary_master_synthesis
    {P : B} (hP : P * P = P) (A C X Y Z : B) :
    (∀ s : Stage, s ≤ tests) ∧
    (anticomm X Y + comm X Y = (2 : ℤ) • (X * Y)) ∧
    (comm X (anticomm Y Z) = anticomm (comm X Y) Z + anticomm Y (comm X Z)) ∧
    (evenGrade P X + oddGrade P X = X) ∧
    (anticomm X (anticomm Y Z) - anticomm Y (anticomm X Z) = comm (comm X Y) Z) ∧
    (comm (conePlus P A) (comm (conePlus P A) (evenGrade P X)) = 0) ∧
    (comm (conePlus P A) (comm (coneMinus P C) X) -
        comm (coneMinus P C) (comm (conePlus P A) X) = comm (genSig P A C) X) ∧
    ((2 : ℤ) • (comm (conePlus P A) (comm (coneMinus P C) X) +
        comm (coneMinus P C) (comm (conePlus P A) X)) =
      -(derivSqPhi P A C X + derivSqJ P A C X)) := by
  have h1 := stage_associative_product_splitting X Y
  have h2 := stage_lieJordan_poisson_leibniz X Y Z
  have h3 := stage_peirce_corner_partition hP A C X
  have h4 := stage_compositions_jordan_associator X Y Z
  have h5 := stage_differential_upper_boundary_nilpotence hP A X
  have h6 := stage_adjoint_codifferential_curvature hP A C X
  have h7 := stage_hodge_laplacian_decomposition hP A C X
  exact ⟨witnesses_cover_all, h1.1, h2.1, h3.1, h4, h5.2, h6.2.2, h7.2⟩

end NonCommutativeOperatorRealization

end InfoGeometry.OperatorAlgebra.PeirceBoundaryOrder
