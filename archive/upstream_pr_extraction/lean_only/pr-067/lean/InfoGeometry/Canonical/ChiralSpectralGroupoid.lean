import Mathlib

/-!
# Chiral spectral actions

The base is kept abstract as a spectrum-like topological carrier.  A chiral
normalizer is represented by a group action through homeomorphisms; projective
and observable descent are recorded as equivariance contracts rather than
asserted without a concrete quotient construction.
-/

namespace InfoGeometry.Canonical.ChiralSpectralGroupoid

structure System (X G : Type*) [Group G] [TopologicalSpace X] where
  action : G → Homeomorph X X
  map_one : action 1 = Homeomorph.refl X
  map_mul : ∀ g h, action (g * h) = (action g).trans (action h)

def transform {X G : Type*} [Group G] [TopologicalSpace X]
    (S : System X G) (g : G) : X → X := S.action g

theorem transform_one {X G : Type*} [Group G] [TopologicalSpace X]
    (S : System X G) : transform S 1 = id := by
  funext x
  exact congrArg (fun h : Homeomorph X X => h x) S.map_one

theorem transform_mul {X G : Type*} [Group G] [TopologicalSpace X]
    (S : System X G) (g h : G) :
    transform S (g * h) = transform S h ∘ transform S g := by
  funext x
  have hx := congrArg (fun q : Homeomorph X X => q x) (S.map_mul g h)
  simpa [transform, Function.comp_def] using hx

/-- Arrows of the transformation groupoid `X ⋊ G`. -/
structure Arrow {X G : Type*} [Group G] [TopologicalSpace X]
    (S : System X G) where
  source : X
  label : G
  target : X
  equation : transform S label source = target

/-- Equivariance is the exact hypothesis needed for a map to respect the
transformation groupoid. -/
def Equivariant {X Y G : Type*} [Group G]
    [TopologicalSpace X] [TopologicalSpace Y]
    (S : System X G) (T : System Y G) (f : X → Y) : Prop :=
  ∀ g x, f (transform S g x) = transform T g (f x)

theorem equivariant_identity {X G : Type*} [Group G] [TopologicalSpace X]
    (S : System X G) : Equivariant S S id := by
  intro g x
  rfl

theorem equivariant_comp {X Y Z G : Type*} [Group G]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (S : System X G) (T : System Y G) (R : System Z G)
    (f : X → Y) (k : Y → Z)
    (hf : Equivariant S T f) (hk : Equivariant T R k) :
    Equivariant S R (k ∘ f) := by
  intro g x
  simp only [Equivariant, Function.comp_apply] at *
  rw [hf, hk]

end InfoGeometry.Canonical.ChiralSpectralGroupoid
