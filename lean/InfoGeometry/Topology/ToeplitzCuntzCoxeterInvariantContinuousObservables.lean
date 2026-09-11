import InfoGeometry.Topology.OrderThreeOrbitObservable
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ToeplitzCuntzThreeCoxeterBoundaryOrbitQuotient

/-!
# Coxeter-invariant continuous observables

This owner records the universal quotient descent for observables on the
concrete ternary Coxeter boundary.  The codomain is deliberately arbitrary:
it may be a scalar space, a topological algebra, or an operator-valued
carrier.  No decoherence, KMS, metric, or `G₂` statement is inferred.
-/

noncomputable section

namespace InfoGeometry.Topology.ToeplitzCuntzCoxeterInvariantContinuousObservables

open InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterBoundaryAction
open InfoGeometry.Topology.ToeplitzCuntzThreeCoxeterBoundaryOrbitQuotient
open InfoGeometry.Topology.ToeplitzCuntzThreeTriality
open InfoGeometry.Topology.OrderThreeHomeomorphOrbitQuotient

variable {Y : Type*} [TopologicalSpace Y]

def IsCoxeterInvariant (obs : TernaryBoundary → Y) : Prop :=
  ∀ x, obs (coxeterBoundaryHomeomorph x) = obs x

def orbitObservable
    (obs : TernaryBoundary → Y)
    (hinv : IsCoxeterInvariant obs) :
    CoxeterBoundaryOrbitSpace → Y :=
  Quotient.lift obs (by
    intro a b hab
    rcases hab with rfl | rfl | rfl
    · rfl
    · exact (hinv a).symm
    · exact ((hinv (coxeterBoundaryHomeomorph a)).trans
        (hinv a)).symm)

def coxeterInvariantObservable
    (obs : TernaryBoundary → Y)
    (hinv : IsCoxeterInvariant obs) :
    CoxeterBoundaryOrbitSpace → Y :=
  orbitObservable obs hinv

def orbifoldObservable
    (obs : TernaryBoundary → Y)
    (hinv : IsCoxeterInvariant obs) :
    CoxeterBoundaryOrbitSpace → Y :=
  orbitObservable obs hinv

omit [TopologicalSpace Y] in
@[simp] theorem orbitObservable_projection
    (obs : TernaryBoundary → Y)
    (hinv : IsCoxeterInvariant obs)
    (x : TernaryBoundary) :
    orbitObservable obs hinv
        (coxeterOrbitProjection x) = obs x := by
  rfl

omit [TopologicalSpace Y] in
@[simp] theorem orbifoldObservable_projection
    (obs : TernaryBoundary → Y)
    (hinv : IsCoxeterInvariant obs)
    (x : TernaryBoundary) :
    orbifoldObservable obs hinv
        (coxeterOrbitProjection x) = obs x := by
  simp [orbifoldObservable, orbitObservable_projection]

theorem orbitObservable_continuous
    (obs : TernaryBoundary → Y)
    (hinv : IsCoxeterInvariant obs)
    (hobs : Continuous obs) :
    Continuous (orbitObservable obs hinv) := by
  unfold orbitObservable
  exact Continuous.quotient_lift hobs (by
    intro a b h_rel
    rcases h_rel with rfl | h1 | h2
    · rfl
    · subst b
      exact (hinv a).symm
    · subst b
      calc
        obs a = obs (coxeterBoundaryHomeomorph a) := (hinv a).symm
        _ = obs (coxeterBoundaryHomeomorph (coxeterBoundaryHomeomorph a)) :=
          (hinv (coxeterBoundaryHomeomorph a)).symm)

theorem orbifoldObservable_continuous
    (obs : TernaryBoundary → Y)
    (hinv : IsCoxeterInvariant obs)
    (hobs : Continuous obs) :
    Continuous (orbifoldObservable obs hinv) := by
  simpa [orbifoldObservable] using orbitObservable_continuous obs hinv hobs

omit [TopologicalSpace Y] in
theorem orbitObservable_unique
    (obs : TernaryBoundary → Y)
    (hinv : IsCoxeterInvariant obs)
    (F : CoxeterBoundaryOrbitSpace → Y)
    (hF : ∀ x, F (coxeterOrbitProjection x) = obs x) :
    F = orbitObservable obs hinv := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  exact (hF x).trans (orbitObservable_projection obs hinv x).symm

omit [TopologicalSpace Y] in
theorem orbifoldObservable_unique
    (obs : TernaryBoundary → Y)
    (hinv : IsCoxeterInvariant obs)
    (F : CoxeterBoundaryOrbitSpace → Y)
    (hF : ∀ x, F (coxeterOrbitProjection x) = obs x) :
    F = orbifoldObservable obs hinv := by
  simpa [orbifoldObservable] using orbitObservable_unique obs hinv F hF

section PointwiseAlgebra

variable {A : Type*} [TopologicalSpace A]

omit [TopologicalSpace A] in
theorem orbitObservable_zero
    [Zero A] :
    orbitObservable (Y := A) (fun _ => 0) (fun _ => rfl) = fun _ => 0 := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change 0 = 0
  rfl

omit [TopologicalSpace A] in
theorem orbitObservable_add
    [Add A]
    (f g : TernaryBoundary → A)
    (hf : IsCoxeterInvariant f)
    (hg : IsCoxeterInvariant g) :
    orbitObservable (Y := A) (fun x => f x + g x)
        (fun x => by dsimp; rw [hf x, hg x]) =
      fun q => orbitObservable (Y := A) f hf q + orbitObservable (Y := A) g hg q := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change f x + g x = f x + g x
  rfl

omit [TopologicalSpace A] in
theorem orbitObservable_one
    [One A] :
    orbitObservable (Y := A) (fun _ => 1) (fun _ => rfl) = fun _ => 1 := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change 1 = 1
  rfl

omit [TopologicalSpace A] in
theorem orbitObservable_mul
    [Mul A]
    (f g : TernaryBoundary → A)
    (hf : IsCoxeterInvariant f)
    (hg : IsCoxeterInvariant g) :
    orbitObservable (Y := A) (fun x => f x * g x)
        (fun x => by dsimp; rw [hf x, hg x]) =
      fun q => orbitObservable (Y := A) f hf q * orbitObservable (Y := A) g hg q := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change f x * g x = f x * g x
  rfl

omit [TopologicalSpace A] in
theorem orbitObservable_star
    [Star A]
    (f : TernaryBoundary → A)
    (hf : IsCoxeterInvariant f) :
    orbitObservable (Y := A) (fun x => star (f x))
        (fun x => by
          change star (f (coxeterBoundaryHomeomorph x)) = star (f x)
          exact congrArg star (hf x)) =
      fun q => star (orbitObservable (Y := A) f hf q) := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  change star (f x) = star (f x)
  rfl

end PointwiseAlgebra

end InfoGeometry.Topology.ToeplitzCuntzCoxeterInvariantContinuousObservables
