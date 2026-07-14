import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Int.Basic
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.SplitCliffordSourceCarrier

noncomputable section

namespace SplitCliffordSourceWittFock

open Filter

structure WittGenerators
    (𝕜 V : Type*) [Field 𝕜]
    [AddCommGroup V] [Module 𝕜 V] where
  create : Int → V →ₗ[𝕜] V
  annihilate : Int → V →ₗ[𝕜] V
  car_annihilate_create :
    ∀ i j : Int,
      (annihilate i).comp (create j) +
        (create j).comp (annihilate i) =
          if i = j then (1 : V →ₗ[𝕜] V) else 0
  car_annihilate_annihilate :
    ∀ i j : Int,
      (annihilate i).comp (annihilate j) +
        (annihilate j).comp (annihilate i) = 0
  car_create_create :
    ∀ i j : Int,
      (create i).comp (create j) +
        (create j).comp (create i) = 0

namespace WittGenerators

variable {𝕜 V : Type*} [Field 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

structure DiracPolarization where
  occupied : Int → Prop
  decidable_occupied : DecidablePred occupied

attribute [instance] DiracPolarization.decidable_occupied

def standardDiracPolarization : DiracPolarization where
  occupied := fun j => j ≤ 0
  decidable_occupied := inferInstance

def normalOrderedBilinear
    (W : WittGenerators 𝕜 V)
    (P : DiracPolarization)
    (i j : Int) : V →ₗ[𝕜] V :=
  if P.occupied j then
    (W.create i).comp (W.annihilate j) -
      (if i = j then (1 : V →ₗ[𝕜] V) else 0)
  else
    (W.create i).comp (W.annihilate j)

def IsFinitelySupportedCurrentAction
    (W : WittGenerators 𝕜 V)
    (P : DiracPolarization)
    (n : Int) (v : V) : Prop :=
  ∃ s : Finset Int,
    ∀ k : Int,
      k ∉ s → normalOrderedBilinear W P k (k + n) v = 0

structure NormalOrderedCurrentDatum
    (W : WittGenerators 𝕜 V)
    (P : DiracPolarization) where
  Jlift : Int → V →ₗ[𝕜] V
  finite_action :
    ∀ n : Int, ∀ v : V,
      IsFinitelySupportedCurrentAction W P n v
  eval_eq_sum :
    ∀ n : Int, ∀ v : V, ∀ s : Finset Int,
      (∀ k : Int, k ∉ s → normalOrderedBilinear W P k (k + n) v = 0) →
      Jlift n v = s.sum (fun k => normalOrderedBilinear W P k (k + n) v)

def CurrentTruncation
    {W : WittGenerators 𝕜 V}
    {P : DiracPolarization}
    (J : NormalOrderedCurrentDatum W P) : Prop :=
  ∀ v : V, ∀ᶠ n : Int in atTop, J.Jlift n v = 0

def CurrentWickLaw
    {W : WittGenerators 𝕜 V}
    {P : DiracPolarization}
    (J : NormalOrderedCurrentDatum W P) : Prop :=
  ∀ m n : Int,
    (J.Jlift m).commutator (J.Jlift n) =
      if m + n = 0 then (m : 𝕜) • (1 : V →ₗ[𝕜] V) else 0

end WittGenerators

end SplitCliffordSourceWittFock
