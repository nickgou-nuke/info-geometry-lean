import InfoGeometry.Canonical.KleinOrientationCharacterBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Centrality readback for the presented Klein group

The native semidirect-product owner proves the exact center classification.
This file transports both the central witness and the classification back to
the presented group using the native presentation equivalence.  No topological
fundamental-group or crossed-product claim is made.
-/

namespace InfoGeometry.Canonical.KleinPresentedCenterBridge

open InfoGeometry.Canonical.KleinNativeSemidirectProductBridge
open InfoGeometry.Canonical.KleinOrientationCharacterBridge
open InfoGeometry.Canonical.KleinPresentedGroup

theorem presented_glide_square_commutes (x : KleinGroup) :
    (toKlein genA) ^ 2 * x = x * (toKlein genA) ^ 2 := by
  apply nativeKleinPresentationRep_injective
  rw [map_mul, map_mul, map_pow,
    (nativeKleinPresentationRep_generators).1]
  exact nativeKlein_glide_square_central
    (nativeKleinPresentationRep x)

theorem presented_glide_square_mem_center :
    (toKlein genA) ^ 2 ∈ Subgroup.center KleinGroup := by
  rw [Subgroup.mem_center_iff]
  intro x
  exact (presented_glide_square_commutes x).symm

theorem presented_mem_center_iff_glide_square_zpow
    (x : KleinGroup) :
    x ∈ Subgroup.center KleinGroup ↔
      ∃ k : ℤ, x = (toKlein genA ^ 2) ^ k := by
  have center_map_iff :
      x ∈ Subgroup.center KleinGroup ↔
        nativeKleinPresentationEquiv x ∈
          Subgroup.center NativeKleinSemidirect := by
    constructor
    · intro hx
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      rcases nativeKleinPresentationEquiv.surjective y with ⟨z, rfl⟩
      simpa using congrArg nativeKleinPresentationEquiv (hx z)
    · intro hx
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      apply nativeKleinPresentationEquiv.injective
      simpa using hx (nativeKleinPresentationEquiv y)
  rw [center_map_iff]
  have hA : nativeKleinPresentationEquiv (toKlein genA) = nativeKleinGlide :=
    nativeKleinPresentationRep_generators.1
  constructor
  · intro hx
    rcases (nativeKlein_mem_center_iff_glide_square_zpow
      (nativeKleinPresentationEquiv x)).mp hx with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply nativeKleinPresentationEquiv.injective
    have hpow : nativeKleinPresentationEquiv ((toKlein genA ^ 2) ^ k) =
        (nativeKleinPresentationEquiv (toKlein genA ^ 2)) ^ k :=
      map_zpow nativeKleinPresentationEquiv.toMonoidHom (toKlein genA ^ 2) k
    have hpow2 : nativeKleinPresentationEquiv (toKlein genA ^ 2) =
        nativeKleinPresentationEquiv (toKlein genA) ^ 2 :=
      map_pow nativeKleinPresentationEquiv.toMonoidHom (toKlein genA) 2
    rw [hpow, hpow2, hA]
    exact hk
  · rintro ⟨k, rfl⟩
    have hpow : nativeKleinPresentationEquiv ((toKlein genA ^ 2) ^ k) =
        (nativeKleinPresentationEquiv (toKlein genA ^ 2)) ^ k :=
      map_zpow nativeKleinPresentationEquiv.toMonoidHom (toKlein genA ^ 2) k
    have hpow2 : nativeKleinPresentationEquiv (toKlein genA ^ 2) =
        nativeKleinPresentationEquiv (toKlein genA) ^ 2 :=
      map_pow nativeKleinPresentationEquiv.toMonoidHom (toKlein genA) 2
    rw [hpow, hpow2, hA]
    exact (nativeKlein_mem_center_iff_glide_square_zpow _).mpr ⟨k, rfl⟩

end InfoGeometry.Canonical.KleinPresentedCenterBridge
