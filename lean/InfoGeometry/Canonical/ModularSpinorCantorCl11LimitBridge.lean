import InfoGeometry.Canonical.ModularSpinorCl11SequentialColimitBridge
import InfoGeometry.Canonical.CantorCl11Limit

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.CantorCl11Limit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit

noncomputable section

universe u

/-!
# Modular-spinor / Cantor-Cl(1,1) limit bridge

This file adds the next honest node after
`ModularSpinorCl11SequentialColimitBridge`. The repository already owns:

* a modular-spinor / Cl(1,1) sequential-colimit bridge;
* a Cantor-boundary / `Cl(1,1)` direct-limit bridge.

What it does not own is a theorem identifying the modular-spinor sheaf/spectrum
lane with the Cantor-boundary coding or proving exchange/KMS compatibility with
that coding. Accordingly, this file only packages the existing owner surfaces
and re-exports the native facts already proved in each.
-/

variable {E Sections BoundarySections Gr Open : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
variable [TopologicalSpace Gr] [Category Open]
variable {J : Type u} [Category.{u, u} J]

/-- A joint owner for the modular-spinor/Cl(1,1) sequential-colimit bridge and
 the Cantor-prefix direct-limit bridge. -/
abbrev ModularSpinorCantorCl11LimitBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  (F : J ⥤ TopCat.{u}) :=
  ModularSpinorCl11SequentialColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F

namespace ModularSpinorCantorCl11LimitBridge

/-- Compatibility projection for the former one-field wrapper. -/
abbrev sequentialBridge
  {E Sections BoundarySections Gr Open : Type*}
  [AddCommGroup Sections] [Module ℝ Sections]
  [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
  [TopologicalSpace Gr] [Category Open]
  {J : Type u} [Category.{u, u} J]
  {F : J ⥤ TopCat.{u}}
  (B : ModularSpinorCantorCl11LimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) := B

end ModularSpinorCantorCl11LimitBridge

/-- The sheaf cover condition remains available inside the Cantor/Cl(1,1)
limit bridge. -/
theorem modularSpinor_CantorCl11Limit_monogenicSheaf_isSheafFor
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorCl11LimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    Presieve.IsSheafFor
      B.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections
      B.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.cover :=
  modularSpinor_Cl11SequentialColimit_monogenicSheaf_isSheafFor F B.sequentialBridge

/-- Monogenic section membership remains available inside the Cantor/Cl(1,1)
limit bridge. -/
theorem modularSpinor_CantorCl11Limit_monogenicSection_mem
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorCl11LimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (U : Open)
  (s : B.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U) :
    (s : B.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.sections.obj (Opposite.op U))
      ∈ B.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.sheafData.monogenicSections U :=
  modularSpinor_Cl11SequentialColimit_monogenicSection_mem F B.sequentialBridge U s

/-- The DN-kernel identity remains available inside the Cantor/Cl(1,1) limit
bridge. -/
theorem modularSpinor_CantorCl11Limit_boundary_kernel_eq_traceMonogenic
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorCl11LimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    LinearMap.ker
      B.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.boundaryData :=
  modularSpinor_Cl11SequentialColimit_boundary_kernel_eq_traceMonogenic F B.sequentialBridge

/-- Gelfand-spectrum descent remains available inside the Cantor/Cl(1,1) limit
bridge. -/
noncomputable def modularSpinor_CantorCl11Limit_gelfandSpectrumDescend
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorCl11LimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  modularSpinor_Cl11SequentialColimit_gelfandSpectrumDescend F B.sequentialBridge

@[reassoc (attr := simp)]
theorem modularSpinor_CantorCl11Limit_gelfandSpectrum_stage
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorCl11LimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    colimit.ι F j ≫
      modularSpinor_CantorCl11Limit_gelfandSpectrumDescend F B =
      colimit.ι F j := by
  dsimp only [modularSpinor_CantorCl11Limit_gelfandSpectrumDescend] at *
  exact modularSpinor_Cl11SequentialColimit_gelfandSpectrum_stage F B.sequentialBridge j

/-- Modular-spinor transport still preserves the canonical three-form inside the
full Cantor/Cl(1,1) limit bridge. -/
theorem modularSpinor_CantorCl11Limit_transport_preserves_threeForm
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorCantorCl11LimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        ((modularSpinorTransport
          B.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) x)
        ((modularSpinorTransport
          B.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) y)
        ((modularSpinorTransport
          B.sequentialBridge.starBridge.cyclicBridge.colimitBridge.complexificationBridge.exchangeBridge.topologicalRepresentationBridge.topologicalIsoBridge.cuntzStageColimitBridge.filteredColimitBridge.spectrumBridge.boundaryBridge.connection path) z) =
      canonicalSplitG2ThreeFormValue x y z := by
  have h := modularSpinor_Cl11SequentialColimit_transport_preserves_threeForm F B.sequentialBridge path x y z
  simp_all [modularSpinorTransport]
  <;> exact h

/-- Prefix-compatible stage families remain constant in the direct limit. -/
theorem cantorCl11_prefix_family_constant_in_limit
  (Fstage : ∀ n : ℕ, Prefix n → InfoGeometry.Canonical.CantorCl11Limit.Stage n)
  (ξ : InfiniteBinaryWordSpace)
  (hF : ∀ n : ℕ,
    stageEmbed n (Fstage n (prefixAt n ξ)) = Fstage (n + 1) (prefixAt (n + 1) ξ)) :
  ∀ n : ℕ,
    ofStage n (Fstage n (prefixAt n ξ)) = ofStage 0 (Fstage 0 []) :=
  prefix_family_constant_in_limit Fstage ξ hF

/-- Stage-zero square-zero data remain square-zero along prefix-compatible
families. -/
theorem cantorCl11_prefix_family_square_zero_in_limit
  (Fstage : ∀ n : ℕ, Prefix n → InfoGeometry.Canonical.CantorCl11Limit.Stage n)
  (ξ : InfiniteBinaryWordSpace)
  (hF : ∀ n : ℕ,
    stageEmbed n (Fstage n (prefixAt n ξ)) = Fstage (n + 1) (prefixAt (n + 1) ξ))
  (h0 : Fstage 0 [] * Fstage 0 [] = 0) :
  ∀ n : ℕ,
    ofStage n (Fstage n (prefixAt n ξ)) * ofStage n (Fstage n (prefixAt n ξ)) = 0 :=
  prefix_family_square_zero_in_limit Fstage ξ hF h0

/-- Stage-zero idempotent data remain idempotent along prefix-compatible
families. -/
theorem cantorCl11_prefix_family_idempotent_in_limit
  (Fstage : ∀ n : ℕ, Prefix n → InfoGeometry.Canonical.CantorCl11Limit.Stage n)
  (ξ : InfiniteBinaryWordSpace)
  (hF : ∀ n : ℕ,
    stageEmbed n (Fstage n (prefixAt n ξ)) = Fstage (n + 1) (prefixAt (n + 1) ξ))
  (h0 : Fstage 0 [] * Fstage 0 [] = Fstage 0 []) :
  ∀ n : ℕ,
    ofStage n (Fstage n (prefixAt n ξ)) * ofStage n (Fstage n (prefixAt n ξ)) =
      ofStage n (Fstage n (prefixAt n ξ)) :=
  prefix_family_idempotent_in_limit Fstage ξ hF h0

/-- Stage-zero involutive data remain involutive along prefix-compatible
families. -/
theorem cantorCl11_prefix_family_involution_in_limit
  (Fstage : ∀ n : ℕ, Prefix n → InfoGeometry.Canonical.CantorCl11Limit.Stage n)
  (ξ : InfiniteBinaryWordSpace)
  (hF : ∀ n : ℕ,
    stageEmbed n (Fstage n (prefixAt n ξ)) = Fstage (n + 1) (prefixAt (n + 1) ξ))
  (h0 : Fstage 0 [] * Fstage 0 [] = 1) :
  ∀ n : ℕ,
    ofStage n (Fstage n (prefixAt n ξ)) * ofStage n (Fstage n (prefixAt n ξ)) = 1 :=
  prefix_family_involution_in_limit Fstage ξ hF h0

end

end InfoGeometry.Canonical
