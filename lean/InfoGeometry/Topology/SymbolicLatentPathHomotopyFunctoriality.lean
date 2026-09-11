import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathHomotopyComposition
import InfoGeometry.Topology.SymbolicLatentPathHomotopyRelation

namespace InfoGeometry.Topology

/-!
# Functoriality of symbolic-latent path homotopies

Continuous maps transport the endpoint-preserving homotopy structure.  This
is the topological composition law needed by chart and observation bridges.
-/

def mapSymbolicLatentPathHomotopy
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (f : C(X, Y)) (H : SymbolicLatentPathHomotopy γ₀ γ₁) :
    SymbolicLatentPathHomotopy
      (f.comp γ₀) (f.comp γ₁) where
  map := f.comp H.map
  at_start := by
    intro t
    change f (H.map (0, t)) = f (γ₀ t)
    rw [H.at_start]
  at_finish := by
    intro t
    change f (H.map (1, t)) = f (γ₁ t)
    rw [H.at_finish]
  fixed_start := by
    intro s
    change f (H.map (s, 0)) = f γ₀.start
    rw [H.fixed_start]
  fixed_finish := by
    intro s
    change f (H.map (s, 1)) = f γ₀.finish
    rw [H.fixed_finish]

@[simp] theorem mapSymbolicLatentPathHomotopy_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (f : C(X, Y)) (H : SymbolicLatentPathHomotopy γ₀ γ₁)
    (s t : SymbolicPathDomain) :
    (mapSymbolicLatentPathHomotopy f H).map (s, t) = f (H.map (s, t)) :=
  rfl

theorem mapSymbolicLatentPathHomotopy_refl
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (γ : SymbolicLatentPath X) :
    mapSymbolicLatentPathHomotopy f (constantSymbolicLatentPathHomotopy γ) =
      constantSymbolicLatentPathHomotopy (f.comp γ) := by
  apply SymbolicLatentPathHomotopy.ext
  ext s t
  cases f
  rfl

theorem mapSymbolicLatentPathHomotopy_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (f : C(X, Y)) (g : C(Y, Z))
    (H : SymbolicLatentPathHomotopy γ₀ γ₁) :
    mapSymbolicLatentPathHomotopy g (mapSymbolicLatentPathHomotopy f H) =
      mapSymbolicLatentPathHomotopy (g.comp f) H := by
  apply SymbolicLatentPathHomotopy.ext
  ext s t
  cases f
  cases g
  rfl

theorem mapSymbolicLatentPathHomotopy_comp_apply
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (f : C(X, Y)) (g : C(Y, Z))
    (H : SymbolicLatentPathHomotopy γ₀ γ₁)
    (s t : SymbolicPathDomain) :
    (mapSymbolicLatentPathHomotopy g
        (mapSymbolicLatentPathHomotopy f H)).map (s, t) =
      (mapSymbolicLatentPathHomotopy (g.comp f) H).map (s, t) := by
  exact congrArg (fun h => h.map (s, t))
    (mapSymbolicLatentPathHomotopy_comp (f := f) (g := g) (H := H))

theorem mapSymbolicLatentPathHomotopic
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (f : C(X, Y))
    (h : SymbolicLatentPathHomotopic γ₀ γ₁) :
    SymbolicLatentPathHomotopic (f.comp γ₀) (f.comp γ₁) := by
  rcases h with ⟨H⟩
  exact ⟨mapSymbolicLatentPathHomotopy f H⟩

end InfoGeometry.Topology
