/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# A coordinate `A₂` root subsystem inside `D₅`

The six oriented differences `eᵢ - eⱼ`, for distinct `i,j < 3`, are
realized inside the standard `D₅` roots `±eᵢ ± eⱼ` in `ℤ⁵`.  Coordinate
permutation by `S₃ = Equiv.Perm (Fin 3)` acts faithfully on these six roots.

This owner proves the finite root-theoretic embedding only.  It does not yet
identify these six roots equivariantly with the repository's sheet--colour
eigenvectors.

BUCKET 1: The finite cardinality, root membership, injectivity, Gram formula,
and Weyl-invariance statements below are proved in this owner.
BUCKET 2: No conditional extension is asserted.
BUCKET 3: Equivariance with the sheet--colour eigenvectors and any infinite
root-system completion remain outside this finite `Fin 3`/`Fin 5` result.
-/

noncomputable section
namespace InfoGeometry.Canonical.A2InsideD5RootSubsystem

/-- The `i`th standard basis vector of the integral rank-five lattice. -/
def coordinate (i : Fin 5) : InfoGeometry.Algebra.FiniteSpin.Vec5Z := fun j => if j = i then 1 else 0

/-- The subset of `ℤ⁵` consisting of the standard coordinate roots
`±eᵢ ± eⱼ` of type `D₅`. -/
def d5RootSet : Set InfoGeometry.Algebra.FiniteSpin.Vec5Z := {v |
  ∃ i j : Fin 5, i ≠ j ∧
    ∃ s t : ℤ, s ^ 2 = 1 ∧ t ^ 2 = 1 ∧
      v = s • coordinate i + t • coordinate j}

/-- The six roots of `A₂`, represented as ordered pairs of distinct indices. -/
abbrev A2Root := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}

/-- Include the first three simple coordinates into the rank-five lattice. -/
def embed3 (i : Fin 3) : Fin 5 := ⟨i, by omega⟩

/-- The ordered `A₂` root `eᵢ-eⱼ` embedded in `ℤ⁵`. -/
def a2RootVector (r : A2Root) : InfoGeometry.Algebra.FiniteSpin.Vec5Z :=
  coordinate (embed3 r.1.1) - coordinate (embed3 r.1.2)

/-- The coordinate inclusion is injective. -/
theorem embed3_injective : Function.Injective embed3 := by
  intro i j h
  exact Fin.ext (Fin.mk.inj h)

/-- Every one of the six `A₂` roots is literally a standard `D₅` root. -/
theorem a2RootVector_isD5Root (r : A2Root) :
    a2RootVector r ∈ d5RootSet := by
  refine ⟨embed3 r.1.1, embed3 r.1.2,
    fun h => r.property (embed3_injective h), 1, -1, by norm_num,
    by norm_num, ?_⟩
  simp [a2RootVector, sub_eq_add_neg]

/-- There are six ordered pairs of distinct indices in `Fin 3`. -/
@[simp] theorem card_a2Root : Fintype.card A2Root = 6 := by
  decide

/-- Coordinate permutation realizes the Weyl `S₃` action on the six roots. -/
def weylAction (σ : Equiv.Perm (Fin 3)) : Equiv.Perm A2Root where
  toFun r := ⟨(σ r.1.1, σ r.1.2), fun h => r.property (σ.injective h)⟩
  invFun r :=
    ⟨(σ.symm r.1.1, σ.symm r.1.2), fun h => r.property (σ.symm.injective h)⟩
  left_inv r := by ext <;> simp
  right_inv r := by ext <;> simp

/-- A coordinate permutation transports both ordered root coordinates and
preserves their distinctness, so the image remains an `A₂` root. -/
theorem weylAction_preserves_root_data (σ : Equiv.Perm (Fin 3)) (r : A2Root) :
    (weylAction σ r).1 = (σ r.1.1, σ r.1.2) ∧
      σ r.1.1 ≠ σ r.1.2 := by
  constructor
  · rfl
  · intro h
    exact r.property (σ.injective h)

/-- The faithful action homomorphism from coordinate permutations to roots. -/
def weylRepresentation : Equiv.Perm (Fin 3) →* Equiv.Perm A2Root where
  toFun := weylAction
  map_one' := by ext r <;> rfl
  map_mul' σ τ := by ext r <;> rfl

/-- The cyclic permutation `0 ↦ 1 ↦ 2 ↦ 0`. -/
def next3 : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

@[simp] theorem next3_ne (i : Fin 3) : i ≠ next3 i := by
  fin_cases i <;> decide

/-- Select the forward-oriented root starting at index `i`. -/
def rootFromIndex (i : Fin 3) : A2Root := ⟨(i, next3 i), next3_ne i⟩

/-- The coordinate Weyl action is faithful; its image is a genuine copy of `S₃`. -/
theorem weylRepresentation_injective : Function.Injective weylRepresentation := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have hi := DFunLike.congr_fun h (rootFromIndex i)
  exact congrArg (fun r : A2Root => r.1.1) hi

/-- The first simple root `e₁-e₂` in the chosen ordered basis. -/
def alpha1 : InfoGeometry.Algebra.FiniteSpin.Vec5Z := a2RootVector ⟨(0, 1), by decide⟩
/-- The second simple root `e₂-e₃` in the chosen ordered basis. -/
def alpha2 : InfoGeometry.Algebra.FiniteSpin.Vec5Z := a2RootVector ⟨(1, 2), by decide⟩

/-- The standard integral inner product on the embedded rank-five lattice. -/
def dot (x y : InfoGeometry.Algebra.FiniteSpin.Vec5Z) : ℤ := ∑ i, x i * y i

@[simp] theorem dot_alpha1_alpha1 : dot alpha1 alpha1 = 2 := by
  decide

@[simp] theorem dot_alpha2_alpha2 : dot alpha2 alpha2 = 2 := by
  decide

@[simp] theorem dot_alpha1_alpha2 : dot alpha1 alpha2 = -1 := by
  decide

/-- Every embedded `A₂` root has squared length two. -/
theorem a2RootVector_norm (r : A2Root) :
    dot (a2RootVector r) (a2RootVector r) = 2 := by
  revert r
  decide

/--
Exact pairwise metric of the embedded `A₂` root system. The Gram form is the
signed incidence formula on ordered pairs:
`⟨eᵢ-eⱼ,eₖ-eₗ⟩ = [i=k]-[i=l]-[j=k]+[j=l]`.
-/
theorem a2_inside_d5_root_gram_law (r s : A2Root) :
    dot (a2RootVector r) (a2RootVector s) =
      (if r.1.1 = s.1.1 then 1 else 0) -
      (if r.1.1 = s.1.2 then 1 else 0) -
      (if r.1.2 = s.1.1 then 1 else 0) +
      (if r.1.2 = s.1.2 then 1 else 0) := by
  revert s r
  decide

/-- Embedded roots have inner product two exactly when they coincide. -/
theorem a2RootVector_dot_eq_two_iff (r s : A2Root) :
    dot (a2RootVector r) (a2RootVector s) = 2 ↔ r = s := by
  revert s r
  decide

/-- The six ordered `A₂` roots remain distinct after embedding into `D₅`. -/
theorem a2RootVector_injective : Function.Injective a2RootVector := by
  intro r s h
  have hdot : dot (a2RootVector r) (a2RootVector s) = 2 := by
    rw [h]
    exact a2RootVector_norm s
  exact (a2RootVector_dot_eq_two_iff r s).mp hdot

/-- The inner product is minus two exactly for opposite ordered roots. -/
theorem a2RootVector_dot_eq_neg_two_iff (r s : A2Root) :
    dot (a2RootVector r) (a2RootVector s) = -2 ↔
      r.1.1 = s.1.2 ∧ r.1.2 = s.1.1 := by
  revert s r
  decide

/-- The pairwise inner products belong to the four values occurring in `A₂`. -/
theorem a2RootVector_dot_gram_values (r s : A2Root) :
    dot (a2RootVector r) (a2RootVector s) = -2 ∨
      dot (a2RootVector r) (a2RootVector s) = -1 ∨
      dot (a2RootVector r) (a2RootVector s) = 1 ∨
      dot (a2RootVector r) (a2RootVector s) = 2 := by
  revert s r
  decide

/-- An ordered root and its reverse have inner product `-2`. -/
theorem a2RootVector_dot_opposite
    (i j : Fin 3) (hij : i ≠ j) :
    dot (a2RootVector ⟨(i, j), hij⟩)
        (a2RootVector ⟨(j, i), hij.symm⟩) = -2 := by
  revert hij
  revert j i
  decide

/-- The coordinate Weyl action preserves the embedded root inner product. -/
theorem a2RootVector_weyl_dot_invariant
    (σ : Equiv.Perm (Fin 3)) (r s : A2Root) :
    dot (a2RootVector (weylAction σ r))
        (a2RootVector (weylAction σ s)) =
      dot (a2RootVector r) (a2RootVector s) := by
  revert s r σ
  decide

end InfoGeometry.Canonical.A2InsideD5RootSubsystem
end noncomputable section
