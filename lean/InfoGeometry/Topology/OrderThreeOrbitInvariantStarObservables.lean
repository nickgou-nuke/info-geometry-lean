import InfoGeometry.Topology.OrderThreeOrbitObservable
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Star-valued observables on an order-three orbit quotient

This owner lifts the generic quotient descent to pointwise algebraic
operations.  The codomain remains an arbitrary topological carrier equipped
with the requested operations; no commutativity, completion, or physical
interpretation is introduced.
-/

noncomputable section

namespace InfoGeometry.Topology.OrderThreeOrbitInvariantStarObservables

open OrderThreeHomeomorphOrbitQuotient
open OrderThreeOrbitObservable

variable {X A : Type*} [TopologicalSpace X] [TopologicalSpace A]
variable {h : X ≃ₜ X}
variable {hcube : ∀ x, h (h (h x)) = x}

theorem invariant_add
    [Add A]
    {f g : X → A}
    (hf : IsInvariant h f)
    (hg : IsInvariant h g) :
    IsInvariant h (fun x => f x + g x) := by
  intro x
  dsimp
  rw [hf x, hg x]

theorem invariant_mul
    [Mul A]
    {f g : X → A}
    (hf : IsInvariant h f)
    (hg : IsInvariant h g) :
    IsInvariant h (fun x => f x * g x) := by
  intro x
  dsimp
  rw [hf x, hg x]

theorem invariant_star
    [Star A]
    {f : X → A}
    (hf : IsInvariant h f) :
    IsInvariant h (fun x => star (f x)) := by
  intro x
  change star (f (h x)) = star (f x)
  exact congrArg star (hf x)

theorem invariant_zero [Zero A] :
    IsInvariant h (fun _ : X => (0 : A)) := by
  intro x
  rfl

theorem invariant_one [One A] :
    IsInvariant h (fun _ : X => (1 : A)) := by
  intro x
  rfl

@[simp] theorem orbitObservable_zero
    (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x)
    [Zero A] :
    orbitObservable h hcube (fun _ : X => (0 : A))
        (invariant_zero (h := h)) =
      (fun _ : OrbitSpace h hcube => (0 : A)) := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  rfl

@[simp] theorem orbitObservable_one
    (h : X ≃ₜ X)
    (hcube : ∀ x, h (h (h x)) = x)
    [One A] :
    orbitObservable h hcube (fun _ : X => (1 : A))
        (invariant_one (h := h)) =
      (fun _ : OrbitSpace h hcube => (1 : A)) := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  rfl

theorem orbitObservable_add
    [Add A]
    {f g : X → A}
    (hf : IsInvariant h f)
    (hg : IsInvariant h g) :
    orbitObservable h hcube (fun x => f x + g x)
        (invariant_add hf hg) =
      (fun q => orbitObservable h hcube f hf q +
        orbitObservable h hcube g hg q) := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change f x + g x = f x + g x
  rfl

theorem orbitObservable_mul
    [Mul A]
    {f g : X → A}
    (hf : IsInvariant h f)
    (hg : IsInvariant h g) :
    orbitObservable h hcube (fun x => f x * g x)
        (invariant_mul hf hg) =
      (fun q => orbitObservable h hcube f hf q *
        orbitObservable h hcube g hg q) := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change f x * g x = f x * g x
  rfl

theorem orbitObservable_star
    [Star A]
    {f : X → A}
    (hf : IsInvariant h f) :
    orbitObservable h hcube (fun x => star (f x))
        (invariant_star hf) =
      (fun q => star (orbitObservable h hcube f hf q)) := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change star (f x) = star (f x)
  rfl

end InfoGeometry.Topology.OrderThreeOrbitInvariantStarObservables
