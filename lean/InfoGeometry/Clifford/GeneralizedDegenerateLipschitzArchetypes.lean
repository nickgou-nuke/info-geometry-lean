/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.Tactic

/-!
# Archetypes for generalized degenerate Clifford and Lipschitz groups

This file formalizes the common algebraic input of Filimoshina--Shirokov,
arXiv:2505.07106v2, without imposing nondegeneracy on the quadratic form.
The paper's signature-specific centralizer tables, group classifications, and
dimension formulas are not asserted here.

The causal order records prerequisite structure: Clifford carrier, its two
involutions, their joint eigenspaces, centralizers and norm maps, stabilizers,
then group relations, examples, and Lie algebras. Centralizers and norm maps
are deliberately incomparable at their shared level.
-/

namespace InfoGeometry.Clifford.GeneralizedDegenerateLipschitzArchetypes

/-! ## A finite causal poset of mathematical archetypes -/

/-- The dependency strata extracted from Sections 2--6 and Appendix B. -/
inductive Archetype where
  | cliffordCarrier
  | gradeAndReversion
  | jointEigenspaces
  | centralizers
  | normMaps
  | stabilizerGroups
  | groupRelations
  | degenerateExamples
  | lieAlgebras
  deriving DecidableEq, Repr

/-- Rank witnesses that every direct prerequisite edge points forward. -/
def Archetype.rank : Archetype → Nat
  | .cliffordCarrier => 0
  | .gradeAndReversion => 1
  | .jointEigenspaces => 2
  | .centralizers => 3
  | .normMaps => 3
  | .stabilizerGroups => 4
  | .groupRelations => 5
  | .degenerateExamples => 5
  | .lieAlgebras => 5

/-- Direct mathematical prerequisite edges, oriented from prerequisite to use. -/
inductive DirectDependency : Archetype → Archetype → Prop where
  | carrierInvolutions : DirectDependency .cliffordCarrier .gradeAndReversion
  | involutionsJointTypes : DirectDependency .gradeAndReversion .jointEigenspaces
  | jointTypesCentralizers : DirectDependency .jointEigenspaces .centralizers
  | jointTypesNorms : DirectDependency .jointEigenspaces .normMaps
  | centralizersStabilizers : DirectDependency .centralizers .stabilizerGroups
  | normsStabilizers : DirectDependency .normMaps .stabilizerGroups
  | stabilizersRelations : DirectDependency .stabilizerGroups .groupRelations
  | stabilizersExamples : DirectDependency .stabilizerGroups .degenerateExamples
  | stabilizersLieAlgebras : DirectDependency .stabilizerGroups .lieAlgebras

/-- Reflexive-transitive closure of the direct prerequisite relation. -/
def descendants : Archetype → Finset Archetype
  | .cliffordCarrier => {.gradeAndReversion, .jointEigenspaces, .centralizers,
      .normMaps, .stabilizerGroups, .groupRelations, .degenerateExamples,
      .lieAlgebras}
  | .gradeAndReversion => {.jointEigenspaces, .centralizers, .normMaps,
      .stabilizerGroups, .groupRelations, .degenerateExamples, .lieAlgebras}
  | .jointEigenspaces => {.centralizers, .normMaps, .stabilizerGroups,
      .groupRelations, .degenerateExamples, .lieAlgebras}
  | .centralizers => {.stabilizerGroups, .groupRelations, .degenerateExamples,
      .lieAlgebras}
  | .normMaps => {.stabilizerGroups, .groupRelations, .degenerateExamples,
      .lieAlgebras}
  | .stabilizerGroups => {.groupRelations, .degenerateExamples, .lieAlgebras}
  | .groupRelations => ∅
  | .degenerateExamples => ∅
  | .lieAlgebras => ∅

/-- Explicit transitive closure of the prerequisite edges. -/
def CausalLE (a b : Archetype) : Prop := a = b ∨ b ∈ descendants a

/-- The dependency relation is a genuine partial order, not an informal DAG sketch. -/
instance : PartialOrder Archetype where
  le := CausalLE
  le_refl a := Or.inl rfl
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;>
      simp_all [CausalLE, descendants]
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;>
      simp_all [CausalLE, descendants]

theorem centralizers_incomparable_normMaps :
    ¬ CausalLE .centralizers .normMaps ∧ ¬ CausalLE .normMaps .centralizers := by
  constructor <;> intro h <;> simp [CausalLE, descendants] at h

/-! ## Strict algebraic language for the paper's core objects -/

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M)

abbrev GA := CliffordAlgebra Q

/-- Grade-involution sign for the paper's quaternion type indexed by `Fin 4`. -/
def gradeSign (i : Fin 4) : ℝ :=
  if i.val = 1 ∨ i.val = 3 then -1 else 1

/-- Reversion sign for the paper's quaternion type indexed by `Fin 4`. -/
def reversionSign (i : Fin 4) : ℝ :=
  if i.val = 2 ∨ i.val = 3 then -1 else 1

/-- The four joint eigenspaces of grade involution and reversion, as actual
linear subspaces rather than just predicates on elements. Their sign pairs are
`(+,+)`, `(-,+)`, `(+,-)`, and `(-,-)`. -/
def jointTypeSubmodule (i : Fin 4) : Submodule ℝ (GA Q) :=
  LinearMap.ker
      (CliffordAlgebra.involute.toLinearMap - gradeSign i • LinearMap.id) ⊓
    LinearMap.ker
      (CliffordAlgebra.reverse - reversionSign i • LinearMap.id)

/-- Set carrier of the joint eigenspace. -/
def jointType (i : Fin 4) : Set (GA Q) := jointTypeSubmodule Q i

/-- A pair of quaternion types denotes their linear direct-sum carrier. -/
def jointPairSubmodule (i j : Fin 4) : Submodule ℝ (GA Q) :=
  jointTypeSubmodule Q i ⊔ jointTypeSubmodule Q j

theorem mem_jointType_iff (i : Fin 4) (x : GA Q) :
    x ∈ jointTypeSubmodule Q i ↔
      CliffordAlgebra.involute x = gradeSign i • x ∧
        CliffordAlgebra.reverse x = reversionSign i • x := by
  by_cases h1 : i.val = 1 ∨ i.val = 3
  <;> by_cases h2 : i.val = 2 ∨ i.val = 3
  <;> simp [jointTypeSubmodule, gradeSign, reversionSign, LinearMap.mem_ker,
    LinearMap.sub_apply, h1, h2, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- Centralizer of a set, with multiplication order matching the paper. -/
def centralizerSet (S : Set (GA Q)) : Set (GA Q) :=
  {x | ∀ y, y ∈ S → x * y = y * x}

/-- Grade-twisted centralizer: `involute x * y = y * x`. -/
def twistedCentralizerSet (S : Set (GA Q)) : Set (GA Q) :=
  {x | ∀ y, y ∈ S → CliffordAlgebra.involute x * y = y * x}

/-- Reversion norm `reverse(g) * g`, the paper's `ψ(g)`. -/
def reversionNorm (g : (GA Q)ˣ) : GA Q :=
  CliffordAlgebra.reverse (g : GA Q) * (g : GA Q)

/-- Clifford norm `involute(reverse(g)) * g`, the paper's `χ(g)`. -/
def cliffordNorm (g : (GA Q)ˣ) : GA Q :=
  CliffordAlgebra.involute (CliffordAlgebra.reverse (g : GA Q)) * (g : GA Q)

/-- Ordinary adjoint action by a Clifford unit. -/
def adjointAction (g : (GA Q)ˣ) (x : GA Q) : GA Q :=
  (g : GA Q) * x * ((g⁻¹ : (GA Q)ˣ) : GA Q)

/-- Grade-twisted adjoint action used for the generalized Lipschitz lane. -/
def gradeTwistedAdjointAction (g : (GA Q)ˣ) (x : GA Q) : GA Q :=
  CliffordAlgebra.involute (g : GA Q) * x * ((g⁻¹ : (GA Q)ˣ) : GA Q)

/-- Setwise stabilizer predicate for a unit action. -/
def stabilizes (act : (GA Q)ˣ → GA Q → GA Q) (S : Set (GA Q)) :
    Set (GA Q)ˣ :=
  {g | ∀ x, x ∈ S → act g x ∈ S}

@[simp] theorem involute_reversion_commute (x : GA Q) :
    CliffordAlgebra.involute (CliffordAlgebra.reverse x) =
      CliffordAlgebra.reverse (CliffordAlgebra.involute x) :=
  (CliffordAlgebra.reverse_involute x).symm

@[simp] theorem reversionNorm_reverse_fixed (g : (GA Q)ˣ) :
    CliffordAlgebra.reverse (reversionNorm Q g) = reversionNorm Q g := by
  simp [reversionNorm, CliffordAlgebra.reverse.map_mul]

theorem adjointAction_mem_reverseFixed_iff_norm_commutes
    (g : (GA Q)ˣ) (x : GA Q) (hx : CliffordAlgebra.reverse x = x) :
    CliffordAlgebra.reverse (adjointAction Q g x) = adjointAction Q g x ↔
      reversionNorm Q g * x = x * reversionNorm Q g := by
  -- This local equivalence is the reverse-involution mechanism behind the
  -- paper's norm/centralizer characterization.  Its application to the
  -- four joint grade/reversion pieces requires the paper's sign bookkeeping.
  let a : GA Q := (g : GA Q)
  let ai : GA Q := ((g⁻¹ : (GA Q)ˣ) : GA Q)
  let r : GA Q := CliffordAlgebra.reverse a
  let ri : GA Q := CliffordAlgebra.reverse ai
  have hai : a * ai = 1 := by simp [a, ai]
  have hia : ai * a = 1 := by simp [a, ai]
  have hri_r : ri * r = 1 := by
    change CliffordAlgebra.reverse ai * CliffordAlgebra.reverse a = 1
    rw [← CliffordAlgebra.reverse.map_mul, hai]
    simp
  have hr_ri : r * ri = 1 := by
    change CliffordAlgebra.reverse a * CliffordAlgebra.reverse ai = 1
    rw [← CliffordAlgebra.reverse.map_mul, hia]
    simp
  have hrevAction : CliffordAlgebra.reverse (adjointAction Q g x) = ri * x * r := by
    dsimp [adjointAction, r, ri, a, ai]
    rw [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse.map_mul, hx]
    noncomm_ring
  constructor
  · intro h
    have heq : ri * x * r = a * x * ai := by
      rw [hrevAction] at h
      simpa [adjointAction, a, ai] using h
    have hEq : x * r * a = r * a * x := by
      calc
        x * r * a = (r * ri) * x * r * a := by simp [mul_assoc, hr_ri]
        _ = r * (ri * x * r) * a := by noncomm_ring
        _ = r * (a * x * ai) * a := by rw [heq]
        _ = r * a * x := by simp [mul_assoc, hia]
    simpa [reversionNorm, r, a, mul_assoc] using hEq.symm
  · intro h
    have hcentral : r * a * x = x * r * a := by
      simpa [reversionNorm, r, a, mul_assoc] using h
    have heq : ri * x * r = a * x * ai := by
      calc
        ri * x * r = ri * x * r * a * ai := by simp [mul_assoc, hai]
        _ = ri * (x * r * a) * ai := by noncomm_ring
        _ = ri * (r * a * x) * ai := by rw [hcentral]
        _ = a * x * ai := by
          calc
            ri * (r * a * x) * ai = (ri * r) * a * x * ai := by noncomm_ring
            _ = a * x * ai := by rw [hri_r]; simp
    rw [hrevAction, heq]
    rfl

/-- The paper's ordinary stabilizer predicate on the reverse-fixed sector is
exactly a preimage of the corresponding norm centralizer. -/
theorem stabilizes_reverseFixed_iff_reversionNormCentralizes (g : (GA Q)ˣ) :
    g ∈ stabilizes Q (adjointAction Q) {x | CliffordAlgebra.reverse x = x} ↔
      reversionNorm Q g ∈ centralizerSet Q {x | CliffordAlgebra.reverse x = x} := by
  constructor
  · intro hg x hx
    exact (adjointAction_mem_reverseFixed_iff_norm_commutes Q g x hx).mp (hg x hx)
  · intro hg x hx
    exact (adjointAction_mem_reverseFixed_iff_norm_commutes Q g x hx).mpr
      (hg x hx)

end InfoGeometry.Clifford.GeneralizedDegenerateLipschitzArchetypes
