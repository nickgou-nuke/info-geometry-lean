import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology

/-!
Topological modular-flow data for symbolic latent spaces.

This is deliberately weaker than a Tomita--Takesaki or
Bisognano--Wichmann theorem: it records only a continuous involution and its
time-reversal relation with a continuous real flow.  KMS states, Hilbert
spaces, operator algebras, and modular Hamiltonians require separate data.
-/

structure SymbolicLatentInvolution (X : Type*) [TopologicalSpace X] where
  toFun : X → X
  continuous_toFun : Continuous toFun
  involutive : ∀ x, toFun (toFun x) = x

instance {X : Type*} [TopologicalSpace X] :
    CoeFun (SymbolicLatentInvolution X) (fun _ => X → X) :=
  ⟨SymbolicLatentInvolution.toFun⟩

theorem SymbolicLatentInvolution.continuous
    {X : Type*} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) :
    Continuous J :=
  J.continuous_toFun

theorem SymbolicLatentInvolution.left_inverse
    {X : Type*} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) :
    Function.LeftInverse J J := by
  intro x
  exact J.involutive x

theorem SymbolicLatentInvolution.right_inverse
    {X : Type*} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) :
    Function.RightInverse J J := by
  intro x
  exact J.involutive x

/-- A continuous involution is a homeomorphism with itself as inverse. -/
noncomputable def SymbolicLatentInvolution.homeomorph
    {X : Type*} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) : X ≃ₜ X where
  toFun := J
  invFun := J
  left_inv := J.left_inverse
  right_inv := J.right_inverse
  continuous_toFun := J.continuous
  continuous_invFun := J.continuous

@[simp] theorem SymbolicLatentInvolution.homeomorph_apply
    {X : Type*} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) (x : X) :
    J.homeomorph x = J x :=
  rfl

structure SymbolicLatentModularFlow (X : Type*) [TopologicalSpace X] where
  act : ℝ → X → X
  continuous_act : Continuous (fun p : ℝ × X => act p.1 p.2)
  zero_apply : ∀ x, act 0 x = x
  add_apply : ∀ (s t : ℝ) (x : X), act (s + t) x = act s (act t x)

def SymbolicLatentModularFlow.orbit
    {X : Type*} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) : Set X :=
  Set.range (fun t : ℝ => Φ.act t x)

theorem SymbolicLatentModularFlow.continuous_orbit
    {X : Type*} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    Continuous (fun t : ℝ => Φ.act t x) := by
  exact Φ.continuous_act.comp (continuous_id.prodMk continuous_const)

theorem SymbolicLatentModularFlow.orbit_mem
    {X : Type*} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    x ∈ Φ.orbit x := by
  exact ⟨0, Φ.zero_apply x⟩

structure SymbolicLatentModularReversal
    {X : Type*} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) where
  involution : SymbolicLatentInvolution X
  reverses_flow : ∀ (t : ℝ) (x : X),
    involution (Φ.act t x) = Φ.act (-t) (involution x)

theorem SymbolicLatentModularReversal.twice
    {X : Type*} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    R.involution (R.involution x) = x :=
  R.involution.involutive x

theorem SymbolicLatentModularReversal.zero_preserved
    {X : Type*} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    R.involution (Φ.act 0 x) = Φ.act 0 (R.involution x) := by
  rw [Φ.zero_apply, Φ.zero_apply]

theorem SymbolicLatentModularReversal.orbit_image
    {X : Type*} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (x : X) :
    R.involution '' Φ.orbit x ⊆ Φ.orbit (R.involution x) := by
  rintro y ⟨z, ⟨t, rfl⟩, rfl⟩
  exact ⟨-t, by simpa using (R.reverses_flow t x).symm⟩

end InfoGeometry.Topology
