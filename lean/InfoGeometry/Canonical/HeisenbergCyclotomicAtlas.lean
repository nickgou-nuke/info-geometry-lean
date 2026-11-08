import InfoGeometry.Canonical.HeisenbergBoundaryAtlas
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornSixthRootCubicChargeBridge

/-!
# Heisenberg cyclotomic atlas

This owner is packaging only.

It records the coexistence of two already-verified surfaces:

* the Heisenberg finite-mode boundary atlas;
* the sixth-root/cubic-charge Zorn package.

It does **not** identify the Heisenberg current corridor with the Zorn
cyclotomic symmetry lane.
-/

namespace InfoGeometry.Canonical.HeisenbergCyclotomicAtlas

open CategoryTheory
open CategoryTheory.Limits
open VirasoroProject
open ZornMatrix

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Combined boundary packet for the verified Heisenberg and cyclotomic lanes. -/
structure Atlas (α : 𝕜) where
  /-- The Heisenberg finite-mode boundary atlas. -/
  heisenberg :
    InfoGeometry.Canonical.HeisenbergBoundaryAtlas.Atlas (𝕜 := 𝕜) α
  /-- A sixth-root Zorn scaling parameter. -/
  sixthRoot : ℂˣ
  /-- The chosen scaling is a genuine sixth root of unity. -/
  sixthRoot_pow :
    (sixthRoot : ℂ) ^ 6 = 1

/-- The combined atlas is built from the existing Heisenberg atlas and a root
parameter. -/
noncomputable def canonicalAtlas (α : 𝕜) (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    Atlas (𝕜 := 𝕜) α where
  heisenberg := InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas
      (𝕜 := 𝕜) α
  sixthRoot := p
  sixthRoot_pow := hp

@[simp] theorem canonicalAtlas_heisenberg (α : 𝕜) (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    (canonicalAtlas (𝕜 := 𝕜) α p hp).heisenberg =
      InfoGeometry.Canonical.HeisenbergBoundaryAtlas.canonicalAtlas (𝕜 := 𝕜) α :=
  rfl

@[simp] theorem canonicalAtlas_sixthRoot (α : 𝕜) (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    (canonicalAtlas (𝕜 := 𝕜) α p hp).sixthRoot = p :=
  rfl

@[simp] theorem canonicalAtlas_sixthRoot_pow (α : 𝕜) (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    (canonicalAtlas (𝕜 := 𝕜) α p hp).sixthRoot_pow = hp :=
  rfl

/-- The Heisenberg finite-mode boundary readout is available inside the
combined atlas. -/
theorem canonicalAtlas_heisenbergFiniteMode_boundaryReadout
    (α : 𝕜) (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) (X : HeisenbergAlgebra 𝕜) :
    ∃ s : Finset (Option ℤ),
      ∃ x : heisenbergFiniteModeStage (𝕜 := 𝕜) s,
        (canonicalAtlas (𝕜 := 𝕜) α p hp).heisenberg.finiteModeMap.hom
            ((colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x) = X := by
  simpa [canonicalAtlas] using
    HeisenbergBoundaryAtlas.canonicalAtlas_finiteMode_boundaryReadout
      (𝕜 := 𝕜) α X

/-- The Sugawara current boundary readout is preserved in the combined atlas. -/
theorem canonicalAtlas_currentSugawara_central
    (α : 𝕜) (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    (canonicalAtlas (𝕜 := 𝕜) α p hp).heisenberg.currentRep.currentSugawaraRepresentation
        (VirasoroAlgebra.cgen 𝕜) =
      (1 : VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜] VirasoroProject.ChargedFockSpace 𝕜 α) :=
  HeisenbergBoundaryAtlas.canonicalAtlas_currentSugawara_central (𝕜 := 𝕜) α

/-- The sixth-root parameter induces the effective cube-root action used by the
Zorn cyclotomic charge package. -/
theorem canonicalAtlas_effectiveCubeRoot
    (α : 𝕜) (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1) :
    ((p : ℂ) ^ 2) ^ 3 = 1 :=
  zornSixthRoot_effectiveCubeRoot p hp

/-- The combined atlas still exposes the three cyclic projectors. -/
theorem canonicalAtlas_cubicProjectors_sum
    (α : 𝕜) (p : ℂˣ) (hp : (p : ℂ) ^ 6 = 1)
    (Z : ZornMatrix ℂ) :
    cubicProjectorZero Z + cubicProjectorPlus Z + cubicProjectorMinus Z = Z :=
  cubicProjectors_sum_of_sixthRoot Z

end InfoGeometry.Canonical.HeisenbergCyclotomicAtlas
