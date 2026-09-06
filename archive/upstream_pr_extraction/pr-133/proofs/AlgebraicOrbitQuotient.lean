import Mathlib

/-!
# Algebraic orbit quotients from genuine group actions

This owner replaces universal relations of the form `∃ g, True` by the actual
orbit relation induced by a homomorphism into permutations.  It is purely
set-theoretic/algebraic: no topology, bundle atlas, or local-system theorem is
asserted here.
-/

namespace AlgebraicOrbitQuotient

variable {G X : Type*} [Group G]

abbrev PermAction (G X : Type*) [Group G] := G →* Equiv.Perm X

def orbitRel (action : PermAction G X) (x y : X) : Prop :=
  ∃ g : G, action g x = y

theorem orbitRel_refl (action : PermAction G X) (x : X) : orbitRel action x x := by
  exact ⟨1, by simp⟩

theorem orbitRel_symm (action : PermAction G X) {x y : X}
    (hxy : orbitRel action x y) : orbitRel action y x := by
  rcases hxy with ⟨g, rfl⟩
  exact ⟨g⁻¹, by simp⟩

theorem orbitRel_trans (action : PermAction G X) {x y z : X}
    (hxy : orbitRel action x y) (hyz : orbitRel action y z) :
    orbitRel action x z := by
  rcases hxy with ⟨g, rfl⟩
  rcases hyz with ⟨h, rfl⟩
  exact ⟨h * g, by simp [map_mul]⟩

def orbitSetoid (action : PermAction G X) : Setoid X where
  r := orbitRel action
  iseqv := {
    refl := orbitRel_refl action
    symm := orbitRel_symm action
    trans := orbitRel_trans action
  }

abbrev OrbitQuotient (action : PermAction G X) := Quotient (orbitSetoid action)

def orbitProjection (action : PermAction G X) : X → OrbitQuotient action :=
  Quotient.mk''

theorem orbitProjection_eq (action : PermAction G X) {x y : X} :
    orbitProjection action x = orbitProjection action y ↔
      orbitRel action x y := by
  exact Quotient.eq'

/-- Every group element acts trivially on the orbit quotient. -/
theorem orbitProjection_action (action : PermAction G X) (g : G) (x : X) :
    orbitProjection action (action g x) = orbitProjection action x := by
  apply (orbitProjection_eq action).2
  exact ⟨g⁻¹, by simp⟩

end AlgebraicOrbitQuotient
