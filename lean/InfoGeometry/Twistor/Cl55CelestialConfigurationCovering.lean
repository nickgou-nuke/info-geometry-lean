import InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.Cl55MinkowskiCelestialSliceTopology
import InfoGeometry.Twistor.ProjectiveNullConfigurationCovering

/-!
# Covering quotient for concrete celestial configurations

The normalized celestial sphere is a compact Hausdorff carrier.  Its ordered
distinct configurations therefore carry the finite permutation covering whose
quotient is the concrete unordered celestial configuration.  This owner does
not identify a fundamental group or a braid generator; it only supplies the
covering-space input for those later constructions.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialConfigurationCovering

open InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
open InfoGeometry.Twistor.Cl55MinkowskiCelestialSliceTopology
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationCovering
open Topology

noncomputable instance celestialPermutationMulAction (n : ℕ) :
    MulAction (Equiv.Perm (Fin n)) (CelestialOrderedConfiguration n) where
  smul σ p := celestialPermute n σ.symm p
  one_smul p := by
    apply Subtype.ext
    funext j
    rfl
  mul_smul σ τ p := by
    apply Subtype.ext
    funext j
    rfl

instance celestialPermutationIsCancelSMul (n : ℕ) :
    IsCancelSMul (Equiv.Perm (Fin n)) (CelestialOrderedConfiguration n) where
  right_cancel' σ τ p h := by
    have hsymm : σ.symm = τ.symm := by
      apply Equiv.ext
      intro j
      by_contra hne
      have hp : p.1 (σ.symm j) = p.1 (τ.symm j) :=
        congrArg (fun q : CelestialOrderedConfiguration n => q.1 j) h
      apply p.2 _ _
      · intro he
        apply hne
        simpa [he]
      · exact hp
    simpa using congrArg Equiv.symm hsymm

theorem celestialConfigurationProjection_eq_iff_mem_orbit
    (n : ℕ) (p q : CelestialOrderedConfiguration n) :
    (@Quotient.mk' (CelestialOrderedConfiguration n)
      (celestialReindexSetoid n) p =
        @Quotient.mk' (CelestialOrderedConfiguration n)
          (celestialReindexSetoid n) q) ↔
      p ∈ MulAction.orbit (Equiv.Perm (Fin n)) q := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · intro hpq
    obtain ⟨σ, hσ⟩ := Quotient.exact hpq
    refine ⟨σ, ?_⟩
    dsimp [HSMul.hSMul, SMul.smul, celestialPermutationMulAction]
    apply celestialOrderedConfigurationMap_injective n
    calc
      celestialOrderedConfigurationMap n (celestialPermute n σ.symm q) =
          permute Q55 n σ.symm (celestialOrderedConfigurationMap n q) :=
        celestialOrderedConfigurationMap_respects_permute n σ.symm q
      _ = permute Q55 n σ.symm
          (permute Q55 n σ (celestialOrderedConfigurationMap n p)) := by
        rw [hσ]
      _ = celestialOrderedConfigurationMap n p := by
        rw [permute_comp]
        simp
  · rintro ⟨σ, hσ⟩
    apply Quotient.sound
    have hq : q = celestialPermute n σ p := by
      apply Subtype.ext
      funext j
      have h' := congrArg
        (fun r : CelestialOrderedConfiguration n => r.1 (σ j)) hσ
      simpa [HSMul.hSMul, SMul.smul, celestialPermutationMulAction,
        celestialPermute] using h'
    exact (celestialReindexSetoid_iff n p q).2 ⟨σ, hq⟩

theorem celestialOrderedConfiguration_locallyCompactSpace (n : ℕ) :
    @LocallyCompactSpace (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n) := by
  letI : CompactSpace CelestialSphere := celestialSphere_compactSpace
  letI : LocallyCompactSpace CelestialSphere := inferInstance
  letI : T2Space CelestialSphere := inferInstance
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  exact (pairwiseDistinct_isOpen n).locallyCompactSpace

theorem celestialOrderedConfiguration_t2Space (n : ℕ) :
    @T2Space (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n) := by
  letI : T2Space CelestialSphere := inferInstance
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  exact Topology.IsEmbedding.subtypeVal.t2Space

theorem celestialUnorderedProjection_isQuotientCoveringMap (n : ℕ) :
    let _ := celestialOrderedConfigurationTopology n
    let _ := celestialUnorderedConfigurationTopology n
    IsQuotientCoveringMap
      (@Quotient.mk' (CelestialOrderedConfiguration n)
        (celestialReindexSetoid n))
      (Equiv.Perm (Fin n)) := by
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  letI : CompactSpace CelestialSphere := celestialSphere_compactSpace
  letI : LocallyCompactSpace CelestialSphere := inferInstance
  letI : T2Space CelestialSphere := inferInstance
  letI : LocallyCompactSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfiguration_locallyCompactSpace n
  letI : T2Space (CelestialOrderedConfiguration n) :=
    celestialOrderedConfiguration_t2Space n
  letI : ContinuousConstSMul (Equiv.Perm (Fin n))
      (CelestialOrderedConfiguration n) := by
    constructor
    intro σ
    dsimp [HSMul.hSMul, SMul.smul, celestialPermutationMulAction]
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact (continuous_apply (σ.symm j)).comp continuous_subtype_val
  exact isQuotientMap_quotient_mk'.isQuotientCoveringMap_of_properlyDiscontinuousSMul
    (fun {p q} => celestialConfigurationProjection_eq_iff_mem_orbit n p q)

end InfoGeometry.Twistor.Cl55CelestialConfigurationCovering
