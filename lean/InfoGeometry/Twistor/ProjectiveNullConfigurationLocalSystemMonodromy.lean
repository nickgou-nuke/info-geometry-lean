import Mathlib.Algebra.Category.ModuleCat.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import InfoGeometry.Twistor.ProjectiveNullPositiveArtinFundamentalGroupoidEquivalence

/-!
# Local-system monodromy on projective-null configuration space

A local system in this owner is the native categorical datum: a functor from
the fundamental groupoid of unordered projective-null configurations to
`ModuleCat`.  Applying `Functor.mapEnd` at a basepoint gives its monodromy
representation of the based fundamental group.

The positive Artin configuration homeomorphisms act on such local systems by
pullback.  The final theorem identifies the pulled-back monodromy with the
original monodromy after the already constructed map of fundamental groups.

No local system is asserted to arise from conformal blocks, no geometric
exchange loops are selected, and no anyon or fusion interpretation is made.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationLocalSystemMonodromy

open CategoryTheory
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinFundamentalGroupoid
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinFundamentalGroupoidEquivalence
open InfoGeometry.Twistor.ProjectiveNullPositiveArtinMonoid
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {R K V : Type*} [Ring R] [Field K] [AddCommGroup V] [Module K V]

/-- The faithful projection from categorical endomorphisms of a `ModuleCat`
object to linear endomorphisms of its underlying module. -/
def moduleCatEndToLinearEnd (M : ModuleCat R) :
    End M →* Module.End R M where
  toFun f := f.hom
  map_one' := by
    apply LinearMap.ext
    intro x
    exact ModuleCat.id_apply M x
  map_mul' f g := by
    apply LinearMap.ext
    intro x
    rfl

@[simp] theorem moduleCatEndToLinearEnd_apply
    (M : ModuleCat R) (f : End M) :
    moduleCatEndToLinearEnd M f = f.hom := rfl

/-- A module-valued local system on unordered projective-null configurations. -/
abbrev ConfigurationLocalSystem
    [TopologicalSpace V] (R : Type*) [Ring R]
    (Q : QuadraticForm K V) (n : ℕ) :=
  let _inst : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  FundamentalGroupoid (Unordered Q n) ⥤ ModuleCat R

/-- The monodromy representation of a configuration local system at a
basepoint.  Its codomain is the native endomorphism monoid of the fiber. -/
def localSystemMonodromy
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (L : ConfigurationLocalSystem R Q n) (p : Unordered Q n) :
    let _inst : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
    FundamentalGroup (Unordered Q n) p →*
      End (L.obj (FundamentalGroupoid.mk p)) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact L.mapEnd (FundamentalGroupoid.mk p)

@[simp] theorem localSystemMonodromy_one
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (L : ConfigurationLocalSystem R Q n) (p : Unordered Q n) :
    let _inst : TopologicalSpace (Unordered Q n) :=
      unorderedConfigurationTopology Q n
    localSystemMonodromy Q n L p 1 =
      (1 : End (L.obj (FundamentalGroupoid.mk p))) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact map_one (localSystemMonodromy Q n L p)

@[simp] theorem localSystemMonodromy_apply
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (L : ConfigurationLocalSystem R Q n) (p : Unordered Q n)
    (γ : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) p) :
    let _inst : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
    localSystemMonodromy Q n L p γ = L.map γ := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  rfl

/-- Since the source is a group, local-system monodromy canonically lands in
the units of the fiber endomorphism monoid. -/
def localSystemMonodromyUnits
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (L : ConfigurationLocalSystem R Q n) (p : Unordered Q n) :
    let _inst : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
    FundamentalGroup (Unordered Q n) p →*
      (End (L.obj (FundamentalGroupoid.mk p)))ˣ :=
  (localSystemMonodromy Q n L p).toHomUnits

/-- The literal general-linear representation carried by a module-valued
local system at a basepoint. -/
def localSystemLinearMonodromy
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (L : ConfigurationLocalSystem R Q n) (p : Unordered Q n) :
    let _inst : TopologicalSpace (Unordered Q n) :=
      unorderedConfigurationTopology Q n
    FundamentalGroup (Unordered Q n) p →*
      LinearMap.GeneralLinearGroup R
        (L.obj (FundamentalGroupoid.mk p)) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact ((moduleCatEndToLinearEnd (L.obj (FundamentalGroupoid.mk p))).comp
    (localSystemMonodromy Q n L p)).toHomUnits

@[simp] theorem localSystemLinearMonodromy_one
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (L : ConfigurationLocalSystem R Q n) (p : Unordered Q n) :
    let _inst : TopologicalSpace (Unordered Q n) :=
      unorderedConfigurationTopology Q n
    localSystemLinearMonodromy Q n L p 1 =
      (1 : LinearMap.GeneralLinearGroup R
        (L.obj (FundamentalGroupoid.mk p))) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  exact map_one (localSystemLinearMonodromy Q n L p)

/-- On vectors, the GL-valued monodromy is exactly the underlying linear map
of the categorical local-system transport. -/
@[simp] theorem localSystemLinearMonodromy_apply
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (L : ConfigurationLocalSystem R Q n) (p : Unordered Q n)
    (γ : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) p)
    (x : let _inst : TopologicalSpace (Unordered Q n) :=
      unorderedConfigurationTopology Q n
      L.obj (FundamentalGroupoid.mk p)) :
    let _inst : TopologicalSpace (Unordered Q n) :=
      unorderedConfigurationTopology Q n
    (localSystemLinearMonodromy Q n L p γ :
      Module.End R (L.obj (FundamentalGroupoid.mk p))) x =
      (L.map γ).hom x := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  rfl

/-- Pull back a module-valued local system along the fundamental-groupoid
autoequivalence induced by a positive Artin configuration homeomorphism. -/
def positiveArtinPullbackLocalSystem
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (hComm : ∀ {i j : ℕ}, i + 1 < j →
      (ρ i).toLinearMap.comp (ρ j).toLinearMap =
        (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V)))
    (n : ℕ) (a : PositiveArtinMonoid)
    (L : ConfigurationLocalSystem R Q n) : ConfigurationLocalSystem R Q n :=
  by
    letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
    exact (positiveArtinFundamentalGroupoidEquivalence Q ρ hQ hArtin hComm
      hcont hcont_inv n a).functor ⋙ L

/-- Pullback along the identity positive-Artin element leaves a local system
unchanged. -/
theorem positiveArtinPullbackLocalSystem_one
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (hComm : ∀ {i j : ℕ}, i + 1 < j →
      (ρ i).toLinearMap.comp (ρ j).toLinearMap =
        (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V)))
    (n : ℕ) (L : ConfigurationLocalSystem R Q n) :
    let _inst : TopologicalSpace (Unordered Q n) :=
      unorderedConfigurationTopology Q n
    positiveArtinPullbackLocalSystem Q ρ hQ hArtin hComm
      hcont hcont_inv n 1 L = L := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  unfold positiveArtinPullbackLocalSystem
  rw [positiveArtinFundamentalGroupoidEquivalence_functor_one]
  rfl

/-- Pullback of local systems composes contravariantly with the positive
Artin monoid action. -/
theorem positiveArtinPullbackLocalSystem_mul
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (hComm : ∀ {i j : ℕ}, i + 1 < j →
      (ρ i).toLinearMap.comp (ρ j).toLinearMap =
        (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V)))
    (n : ℕ) (a b : PositiveArtinMonoid)
    (L : ConfigurationLocalSystem R Q n) :
    let _inst : TopologicalSpace (Unordered Q n) :=
      unorderedConfigurationTopology Q n
    positiveArtinPullbackLocalSystem Q ρ hQ hArtin hComm
        hcont hcont_inv n (a * b) L =
      positiveArtinPullbackLocalSystem Q ρ hQ hArtin hComm
        hcont hcont_inv n b
        (positiveArtinPullbackLocalSystem Q ρ hQ hArtin hComm
          hcont hcont_inv n a L) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  unfold positiveArtinPullbackLocalSystem
  rw [positiveArtinFundamentalGroupoidEquivalence_functor_mul]
  rfl

/-- Pullback monodromy is the original local-system monodromy evaluated after
the positive Artin map of the fundamental group. -/
theorem positiveArtinPullbackLocalSystem_monodromy
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (hComm : ∀ {i j : ℕ}, i + 1 < j →
      (ρ i).toLinearMap.comp (ρ j).toLinearMap =
        (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V)))
    (n : ℕ) (a : PositiveArtinMonoid)
    (L : ConfigurationLocalSystem R Q n) (p : Unordered Q n)
    (γ : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) p) :
    let _inst : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
    localSystemMonodromy Q n
        (positiveArtinPullbackLocalSystem Q ρ hQ hArtin hComm
          hcont hcont_inv n a L) p γ =
      localSystemMonodromy Q n L
        (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a p)
        ((positiveArtinFundamentalGroupoidMap Q ρ hQ hArtin hComm hcont n a).map γ) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  change L.map
      ((positiveArtinFundamentalGroupoidEquivalence Q ρ hQ hArtin hComm
        hcont hcont_inv n a).functor.map γ) =
    L.map ((positiveArtinFundamentalGroupoidMap Q ρ hQ hArtin hComm hcont n a).map γ)
  have hfunctor := positiveArtinFundamentalGroupoidEquivalence_functor
    Q ρ hQ hArtin hComm hcont hcont_inv n a
  cases hfunctor
  rfl

/-- The GL-valued monodromy of the pulled-back local system is the original
GL-valued monodromy evaluated after the positive Artin map of fundamental
groups.  This is the linear representation-level form of
`positiveArtinPullbackLocalSystem_monodromy`. -/
theorem positiveArtinPullbackLocalSystem_linearMonodromy
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (hComm : ∀ {i j : ℕ}, i + 1 < j →
      (ρ i).toLinearMap.comp (ρ j).toLinearMap =
        (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (hcont : ∀ i, Continuous ((ρ i : V → V)))
    (hcont_inv : ∀ i, Continuous (((ρ i).symm : V → V)))
    (n : ℕ) (a : PositiveArtinMonoid)
    (L : ConfigurationLocalSystem R Q n) (p : Unordered Q n)
    (γ : @FundamentalGroup (Unordered Q n)
      (unorderedConfigurationTopology Q n) p) :
    let _inst : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
    localSystemLinearMonodromy Q n
        (positiveArtinPullbackLocalSystem Q ρ hQ hArtin hComm
          hcont hcont_inv n a L) p γ =
      localSystemLinearMonodromy Q n L
        (positiveArtinConfigurationAction Q ρ hQ hArtin hComm n a p)
        ((positiveArtinFundamentalGroupoidMap Q ρ hQ hArtin hComm hcont n a).map γ) := by
  letI : TopologicalSpace (Unordered Q n) := unorderedConfigurationTopology Q n
  apply Units.ext
  apply LinearMap.ext
  intro x
  change L.map
      ((positiveArtinFundamentalGroupoidEquivalence Q ρ hQ hArtin hComm
        hcont hcont_inv n a).functor.map γ) x =
    L.map ((positiveArtinFundamentalGroupoidMap Q ρ hQ hArtin hComm hcont n a).map γ) x
  have hfunctor := positiveArtinFundamentalGroupoidEquivalence_functor
    Q ρ hQ hArtin hComm hcont hcont_inv n a
  cases hfunctor
  rfl

end InfoGeometry.Twistor.ProjectiveNullConfigurationLocalSystemMonodromy
