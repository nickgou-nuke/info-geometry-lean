/-
InfoGeometry/OperatorAlgebra/ConstructiveConnesCocycle.lean
-/

import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ConstructiveConnesCocycle

open InfoGeometry.OperatorAlgebra.OperatorThermodynamics

/-! The modular automorphism group is the repository-native `OperatorFlow`.
    This file owns only cocycle data and its algebraic composition laws. -/

structure ConnesCocycleData (A : Type*) [Monoid A]
    (flow_phi flow_omega : OperatorFlow A) where
  u : ℝ → A

def IsConnesCocycle
    {A : Type*} [Monoid A]
    {flow_phi flow_omega : OperatorFlow A}
    (C : ConnesCocycleData A flow_phi flow_omega) : Prop :=
  ∀ s t : ℝ,
    C.u (s + t) = C.u s * flow_omega.flow s (C.u t)

def Intertwines
    {A : Type*} [Monoid A]
    {flow_phi flow_omega : OperatorFlow A}
    (C : ConnesCocycleData A flow_phi flow_omega) : Prop :=
  ∀ (t : ℝ) (x : A),
    flow_phi.flow t x * C.u t = C.u t * flow_omega.flow t x

def chain_cocycles
    {A : Type*} [Monoid A]
    {flow_phi flow_omega flow_psi : OperatorFlow A}
    (u : ConnesCocycleData A flow_phi flow_omega)
    (v : ConnesCocycleData A flow_omega flow_psi) :
    ConnesCocycleData A flow_phi flow_psi where
  u := fun t => u.u t * v.u t

theorem chain_cocycles_isConnesCocycle
    {A : Type*} [Monoid A]
    {flow_phi flow_omega flow_psi : OperatorFlow A}
    (u : ConnesCocycleData A flow_phi flow_omega)
    (v : ConnesCocycleData A flow_omega flow_psi)
    (hu : IsConnesCocycle u)
    (hv : IsConnesCocycle v)
    (hvIntertwines : Intertwines v) :
    IsConnesCocycle (chain_cocycles u v) := by
  intro s t
  change u.u (s + t) * v.u (s + t) =
    (u.u s * v.u s) * flow_psi.flow s (u.u t * v.u t)
  calc
    u.u (s + t) * v.u (s + t) =
        (u.u s * flow_omega.flow s (u.u t)) *
          (v.u s * flow_psi.flow s (v.u t)) := by
      rw [hu s t, hv s t]
    _ = u.u s *
        (flow_omega.flow s (u.u t) * v.u s) *
          flow_psi.flow s (v.u t) := by
      simp only [mul_assoc]
    _ = u.u s *
        (v.u s * flow_psi.flow s (u.u t)) *
          flow_psi.flow s (v.u t) := by
      rw [hvIntertwines s (u.u t)]
    _ = (u.u s * v.u s) *
        (flow_psi.flow s (u.u t) * flow_psi.flow s (v.u t)) := by
      simp only [mul_assoc]
    _ = (u.u s * v.u s) * flow_psi.flow s (u.u t * v.u t) := by
      rw [(flow_psi.flow s).map_mul]

theorem chain_cocycles_intertwines
    {A : Type*} [Monoid A]
    {flow_phi flow_omega flow_psi : OperatorFlow A}
    (u : ConnesCocycleData A flow_phi flow_omega)
    (v : ConnesCocycleData A flow_omega flow_psi)
    (huIntertwines : Intertwines u)
    (hvIntertwines : Intertwines v) :
    Intertwines (chain_cocycles u v) := by
  intro t x
  change flow_phi.flow t x * (u.u t * v.u t) =
    (u.u t * v.u t) * flow_psi.flow t x
  calc
    flow_phi.flow t x * (u.u t * v.u t) =
        (flow_phi.flow t x * u.u t) * v.u t := by
      rw [mul_assoc]
    _ = (u.u t * flow_omega.flow t x) * v.u t := by
      rw [huIntertwines t x]
    _ = u.u t * (flow_omega.flow t x * v.u t) := by
      rw [mul_assoc]
    _ = u.u t * (v.u t * flow_psi.flow t x) := by
      rw [hvIntertwines t x]
    _ = (u.u t * v.u t) * flow_psi.flow t x := by
      rw [mul_assoc]

end InfoGeometry.OperatorAlgebra.ConstructiveConnesCocycle
