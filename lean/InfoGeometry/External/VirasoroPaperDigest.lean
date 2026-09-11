import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Virasoro.Sugawara
import InfoGeometry.External.Virasoro.AffineKacMoody
import InfoGeometry.External.Virasoro.WittAlgebraCohomology
import InfoGeometry.External.Virasoro.FockSpaceSugawara
import InfoGeometry.External.Virasoro.VirasoroAlgebra

/-!
The `external/FrogBird` mirror is an external theorem-search corpus only.
It is used for retrieval and theorem discovery, not proof authority.
-/

/-!
# InfoGeometry.External.VirasoroPaperDigest

Lean-native digest of the main formalized results in arXiv:2510.21741v1.

This file does not introduce new wrapper structures. It only re-exports the
paper-facing theorem shapes already present in the Virasoro project files.

The paper's core formalized results are:

* the 2-cohomology of the Witt algebra is one-dimensional;
* the basic bosonic Sugawara construction produces a Virasoro representation
  from a locally truncated Heisenberg representation;
* the charged Fock-space Verma highest-weight vector maps to the vacuum.
-/

noncomputable section

universe u

namespace InfoGeometry.External.VirasoroPaperDigest

open LieAlgebra.LoopAlgebra
open VirasoroProject
open HeisenbergAlgebra
open Filter

/-- The affine Kac-Moody cocycle underlying the root affine extension. -/
def affineKacMoodyCocycle
    {𝕜 : Type u} [CommRing 𝕜] [IsAddTorsionFree 𝕜]
    {𝓰 : Type u} [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
    (Φ : LinearMap.BilinForm 𝕜 𝓰)
    (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm) :
    LieTwoCocycle 𝕜 (LieAlgebra.loopAlgebra 𝕜 ℤ 𝓰) 𝕜 :=
  VirasoroProject.affineKacMoodyCocycle 𝕜 𝓰 Φ hΦ hΦs

/-- The untwisted affine Kac-Moody algebra. -/
abbrev AffineKacMoody
    {𝕜 : Type u} [CommRing 𝕜] [IsAddTorsionFree 𝕜]
    {𝓰 : Type u} [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
    (Φ : LinearMap.BilinForm 𝕜 𝓰)
    (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm) :=
  VirasoroProject.AffineKacMoody 𝕜 𝓰 Φ hΦ hΦs

/-- The Witt algebra 2-cohomology is one-dimensional. -/
theorem wittCohomologyRankOne
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] :
    Module.rank 𝕜 (LieTwoCohomology 𝕜 (WittAlgebra 𝕜) 𝕜) = 1 :=
  VirasoroProject.WittAlgebra.rank_lieTwoCohomology_eq_one 𝕜

/-- The basic bosonic Sugawara construction on a locally truncated Heisenberg representation. -/
def basicBosonicSugawaraRepresentation
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (α : LieAlgebra.Representation 𝕜 𝕜 (HeisenbergAlgebra 𝕜) V)
    (hα : ∀ v, ∀ᶠ k in atTop, α (HeisenbergAlgebra.jgen 𝕜 k) v = 0)
    (hαc : α (HeisenbergAlgebra.kgen 𝕜) = 1) :
    LieAlgebra.Representation 𝕜 𝕜 (VirasoroAlgebra 𝕜) V :=
  VirasoroProject.sugawaraRepresentation_of_representation_heisenbergAlgebra
    α hα hαc

/-- The charged Fock-space Verma highest-weight vector maps to the vacuum. -/
theorem virasoroVermaToChargedFockSpace_hwVec
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (α : 𝕜) :
    VirasoroProject.ChargedFockSpace.virasoroVermaToChargedFockSpace 𝕜 α
      (.hwVec 𝕜 _ _) = VirasoroProject.ChargedFockSpace.vacuum 𝕜 α :=
  VirasoroProject.ChargedFockSpace.virasoroVermaToChargedFockSpace_hwVec 𝕜 α

end InfoGeometry.External.VirasoroPaperDigest
