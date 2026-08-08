import InfoGeometry.Analytic.HKColimitStructures
import InfoGeometry.Spectral.Cohomology.MayerVietoris

/-!
# Locality on the critical strip

The continuum property in this module is a compatible filtered inductive
Hestenes-Krein family.  No analytic continuation or epsilon-limit principle
is postulated.  De Rham locality is supplied by explicit local complexes and
additive cohomology equivalences.
-/

noncomputable section

namespace InfoGeometry.Spectral.Cohomology.Locality

open InfoGeometry.Carrier
open InfoGeometry.Spectral.Cohomology.deRham

universe u

/-- The open critical strip. -/
def criticalStrip : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 1}

/-- The de Rham locality owner from the canonical de Rham module. -/
abbrev LocalityPrinciple
    (V : Type u) [AddCommGroup V] [Module ℝ V]
    [SmoothManifold ℂ] [DifferentialForms ℂ V]
    (C : deRhamComplex ℂ V) :=
  deRham.LocalityPrinciple V C

/-- Extract the explicit local complex and all degreewise cohomology
equivalences from a de Rham locality owner. -/
theorem localToGlobal
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    [SmoothManifold ℂ] [DifferentialForms ℂ V]
    {C : deRhamComplex ℂ V}
    (P : LocalityPrinciple V C)
    (s : criticalStrip) :
    ∃ (U : Set ℂ) (_hU : IsOpen U) (_hs : (s : ℂ) ∈ U)
      (_smoothU : SmoothManifold U) (_formsU : DifferentialForms U V)
      (CU : deRhamComplex U V),
      ∀ k, Nonempty (deRhamComplex.deRhamCohomology C k ≃+
        deRhamComplex.deRhamCohomology CU k) :=
  P.localToGlobal s

/-- Local Hestenes-Krein analyticity owned by one compatible filtered
inductive family. -/
structure HKLocalityPrinciple
    (f : ℂ → ℂ) [HestenesKreinSpace ℂ] where
  filtered : FilteredInductiveHKAnalytic f
  localWitness : ∀ s : criticalStrip,
    ∃ U : Set ℂ, IsOpen U ∧ (s : ℂ) ∈ U ∧
      HKColimitOn (inferInstance : HestenesKreinSpace ℂ)
        (inferInstance : HestenesKreinSpace ℂ) f U

/-- Extract local HK-colimit analyticity from its filtered-inductive owner. -/
theorem hkLocalToGlobal
    {f : ℂ → ℂ} [HestenesKreinSpace ℂ]
    (P : HKLocalityPrinciple f)
    (s : criticalStrip) :
    ∃ U : Set ℂ, IsOpen U ∧ (s : ℂ) ∈ U ∧
      HKColimitOn (inferInstance : HestenesKreinSpace ℂ)
        (inferInstance : HestenesKreinSpace ℂ) f U :=
  P.localWitness s

/-- The filtered-inductive family remains explicitly available from every
locality property. -/
def filtered_owner
    {f : ℂ → ℂ} [HestenesKreinSpace ℂ]
    (P : HKLocalityPrinciple f) :
    FilteredInductiveHKAnalytic f :=
  P.filtered

end InfoGeometry.Spectral.Cohomology.Locality

namespace InfoGeometry.Spectral.Cohomology

open InfoGeometry.Carrier
open InfoGeometry.Spectral.Cohomology.deRham

universe u

/-- Public extraction of the HK locality property. -/
theorem HKLocalityPrinciple
    {f : ℂ → ℂ} [HestenesKreinSpace ℂ]
    (P : Locality.HKLocalityPrinciple f)
    (s : Locality.criticalStrip) :
    ∃ U : Set ℂ, IsOpen U ∧ (s : ℂ) ∈ U ∧
      HKColimitOn (inferInstance : HestenesKreinSpace ℂ)
        (inferInstance : HestenesKreinSpace ℂ) f U :=
  P.localWitness s

/-- Public extraction of the de Rham locality property. -/
theorem deRhamLocalityPrinciple
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    [SmoothManifold ℂ] [DifferentialForms ℂ V]
    {C : deRhamComplex ℂ V}
    (P : Locality.LocalityPrinciple V C)
    (s : Locality.criticalStrip) :
    ∃ (U : Set ℂ) (_hU : IsOpen U) (_hs : (s : ℂ) ∈ U)
      (_smoothU : SmoothManifold U) (_formsU : DifferentialForms U V)
      (CU : deRhamComplex U V),
      ∀ k, Nonempty (deRhamComplex.deRhamCohomology C k ≃+
        deRhamComplex.deRhamCohomology CU k) :=
  P.localToGlobal s

/-- Owner for local HK-colimit analyticity together with its global compatible
filtered-inductive family. -/
structure HKStokesAnalyticBridgeData
    (f : ℂ → ℂ) [HestenesKreinSpace ℂ]
    (s : Locality.criticalStrip) where
  localWitness : ∃ U : Set ℂ, IsOpen U ∧ (s : ℂ) ∈ U ∧
    HKColimitOn (inferInstance : HestenesKreinSpace ℂ)
      (inferInstance : HestenesKreinSpace ℂ) f U
  filtered : FilteredInductiveHKAnalytic f

/-- Construct the HK-Stokes bridge data from its locality owner. -/
def HKStokesToAnalyticBridge
    {f : ℂ → ℂ} [HestenesKreinSpace ℂ]
    (P : Locality.HKLocalityPrinciple f)
    (s : Locality.criticalStrip) :
    HKStokesAnalyticBridgeData f s :=
  ⟨P.localWitness s, P.filtered⟩

end InfoGeometry.Spectral.Cohomology
