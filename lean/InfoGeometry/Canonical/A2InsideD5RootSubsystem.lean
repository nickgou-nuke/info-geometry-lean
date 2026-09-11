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
-/

noncomputable section
namespace InfoGeometry.Canonical.A2InsideD5RootSubsystem

abbrev D5Space := InfoGeometry.Algebra.FiniteSpin.Vec5Z

def coordinate (i : Fin 5) : D5Space := fun j => if j = i then 1 else 0

/-- The standard coordinate description of roots of type `D₅`. -/
def IsD5Root (v : D5Space) : Prop :=
  ∃ i j : Fin 5, i ≠ j ∧
    ∃ s t : ℤ, s ^ 2 = 1 ∧ t ^ 2 = 1 ∧
      v = s • coordinate i + t • coordinate j

/-- The six roots of `A₂`, represented as ordered pairs of distinct indices. -/
abbrev A2Root := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}

def embed3 (i : Fin 3) : Fin 5 := ⟨i, by omega⟩

def a2RootVector (r : A2Root) : D5Space :=
  coordinate (embed3 r.1.1) - coordinate (embed3 r.1.2)

theorem embed3_injective : Function.Injective embed3 := by
  intro i j h
  exact Fin.ext (Fin.mk.inj h)

/-- Every one of the six `A₂` roots is literally a standard `D₅` root. -/
theorem a2RootVector_isD5Root (r : A2Root) :
    IsD5Root (a2RootVector r) := by
  refine ⟨embed3 r.1.1, embed3 r.1.2,
    fun h => r.property (embed3_injective h), 1, -1, by norm_num,
    by norm_num, ?_⟩
  simp [a2RootVector, sub_eq_add_neg]

@[simp] theorem card_a2Root : Fintype.card A2Root = 6 := by
  native_decide

theorem a2RootVector_injective : Function.Injective a2RootVector := by
  decide

/-- Coordinate permutation realizes the Weyl `S₃` action on the six roots. -/
def weylAction (σ : Equiv.Perm (Fin 3)) : Equiv.Perm A2Root where
  toFun r := ⟨(σ r.1.1, σ r.1.2), fun h => r.property (σ.injective h)⟩
  invFun r :=
    ⟨(σ.symm r.1.1, σ.symm r.1.2), fun h => r.property (σ.symm.injective h)⟩
  left_inv r := by ext <;> simp
  right_inv r := by ext <;> simp

@[simp] theorem weylAction_apply_fst (σ : Equiv.Perm (Fin 3)) (r : A2Root) :
    (weylAction σ r).1.1 = σ r.1.1 := rfl

@[simp] theorem weylAction_apply_snd (σ : Equiv.Perm (Fin 3)) (r : A2Root) :
    (weylAction σ r).1.2 = σ r.1.2 := rfl

def weylRepresentation : Equiv.Perm (Fin 3) →* Equiv.Perm A2Root where
  toFun := weylAction
  map_one' := by ext r <;> rfl
  map_mul' σ τ := by ext r <;> rfl

def next3 : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

@[simp] theorem next3_ne (i : Fin 3) : i ≠ next3 i := by
  fin_cases i <;> decide

def rootFromIndex (i : Fin 3) : A2Root := ⟨(i, next3 i), next3_ne i⟩

/-- The coordinate Weyl action is faithful; its image is a genuine copy of `S₃`. -/
theorem weylRepresentation_injective : Function.Injective weylRepresentation := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have hi := DFunLike.congr_fun h (rootFromIndex i)
  exact congrArg (fun r : A2Root => r.1.1) hi

/-- The two standard simple roots inside the subsystem. -/
def alpha1 : D5Space := a2RootVector ⟨(0, 1), by decide⟩
def alpha2 : D5Space := a2RootVector ⟨(1, 2), by decide⟩

def dot (x y : D5Space) : ℤ := ∑ i, x i * y i

@[simp] theorem dot_alpha1_alpha1 : dot alpha1 alpha1 = 2 := by
  native_decide

@[simp] theorem dot_alpha2_alpha2 : dot alpha2 alpha2 = 2 := by
  native_decide

@[simp] theorem dot_alpha1_alpha2 : dot alpha1 alpha2 = -1 := by
  native_decide

theorem a2RootVector_norm (r : A2Root) :
    dot (a2RootVector r) (a2RootVector r) = 2 := by
  revert r
  native_decide

theorem a2RootVector_dot_eq_two_iff (r s : A2Root) :
    dot (a2RootVector r) (a2RootVector s) = 2 ↔ r = s := by
  revert s r
  native_decide

theorem a2RootVector_dot_eq_neg_two_iff (r s : A2Root) :
    dot (a2RootVector r) (a2RootVector s) = -2 ↔
      r.1.1 = s.1.2 ∧ r.1.2 = s.1.1 := by
  revert s r
  native_decide

theorem a2RootVector_dot_gram_values (r s : A2Root) :
    dot (a2RootVector r) (a2RootVector s) = -2 ∨
      dot (a2RootVector r) (a2RootVector s) = -1 ∨
      dot (a2RootVector r) (a2RootVector s) = 1 ∨
      dot (a2RootVector r) (a2RootVector s) = 2 := by
  revert s r
  native_decide

theorem a2RootVector_dot_opposite
    (i j : Fin 3) (hij : i ≠ j) :
    dot (a2RootVector ⟨(i, j), hij⟩)
        (a2RootVector ⟨(j, i), hij.symm⟩) = -2 := by
  revert hij
  revert j i
  native_decide

theorem a2RootVector_weyl_dot_invariant
    (σ : Equiv.Perm (Fin 3)) (r s : A2Root) :
    dot (a2RootVector (weylAction σ r))
        (a2RootVector (weylAction σ s)) =
      dot (a2RootVector r) (a2RootVector s) := by
  revert s r σ
  native_decide

theorem a2_inside_d5_packet :
    Fintype.card A2Root = 6 ∧
    (∀ r : A2Root, IsD5Root (a2RootVector r)) ∧
    Function.Injective a2RootVector ∧
    Function.Injective weylRepresentation ∧
    dot alpha1 alpha1 = 2 ∧ dot alpha2 alpha2 = 2 ∧
      dot alpha1 alpha2 = -1 :=
  ⟨card_a2Root, a2RootVector_isD5Root, a2RootVector_injective,
    weylRepresentation_injective, dot_alpha1_alpha1,
    dot_alpha2_alpha2, dot_alpha1_alpha2⟩

end InfoGeometry.Canonical.A2InsideD5RootSubsystem
end noncomputable section
