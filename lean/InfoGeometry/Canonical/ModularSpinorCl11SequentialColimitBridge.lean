import InfoGeometry.Canonical.ModularSpinorCl11CuntzTopologicalStarBridge
import InfoGeometry.Canonical.Cl11ConcreteSequentialColimitConsequences

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological
open InfoGeometry.Canonical.InductiveColimitBridge
open InfoGeometry.Canonical.Cl11SequentialStageSystemBridge
open InfoGeometry.Canonical.Cl11ConcreteSequentialColimitConsequences
open InfoGeometry.Clifford.Cl11InfiniteCarrier
open InfoGeometry.Clifford.Cl11TensorTowerLimit

noncomputable section

universe u

/-!
# Modular-spinor / Cl(1,1) sequential colimit bridge

This file adds the next honest node after
`ModularSpinorCl11CuntzTopologicalStarBridge`. The repository already owns:

* a modular-spinor / Cl(1,1)-Cuntz topological star bridge;
* a genuine Cl(1,1) sequential colimit system with concrete consequences.

What it does not own is a theorem identifying the modular-spinor sheaf/spectrum
lane with the sequential colimit carrier or proving exchange/KMS
compatibility with that limit. Accordingly, this file only packages the
existing owner surfaces together and re-exports the native facts already proved
in each.
-/

variable {E Sections BoundarySections Gr Open : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
variable [TopologicalSpace Gr] [Category Open]
variable {J : Type u} [Category.{u, u} J]

/-- The sheaf cover condition remains available inside the sequential colimit
bridge. -/
theorem modularSpinor_Cl11SequentialColimit_monogenicSheaf_isSheafFor
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    Presieve.IsSheafFor
      B.spectrumBridge.sheafData.sections
      B.spectrumBridge.sheafData.cover :=
  modularSpinor_filteredColimit_monogenicSheaf_isSheafFor F B

/-- Monogenic section membership remains available inside the sequential colimit
bridge. -/
theorem modularSpinor_Cl11SequentialColimit_monogenicSection_mem
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (U : Open)
  (s : B.spectrumBridge.sheafData.monogenicSections U) :
    (s : B.spectrumBridge.sheafData.sections.obj (Opposite.op U))
      ∈ B.spectrumBridge.sheafData.monogenicSections U :=
  modularSpinor_filteredColimit_monogenicSection_mem F B U s

/-- The DN-kernel identity remains available inside the sequential colimit
bridge. -/
theorem modularSpinor_Cl11SequentialColimit_boundary_kernel_eq_traceMonogenic
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    LinearMap.ker
      B.spectrumBridge.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.spectrumBridge.boundaryBridge.boundaryData :=
  modularSpinor_filteredColimit_boundary_kernel_eq_traceMonogenic F B

/-- Gelfand-spectrum descent remains available inside the sequential colimit
bridge. -/
noncomputable def modularSpinor_Cl11SequentialColimit_gelfandSpectrumDescend
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  modularSpinor_filteredColimit_gelfandSpectrumDescend F B

@[reassoc (attr := simp)]
theorem modularSpinor_Cl11SequentialColimit_gelfandSpectrum_stage
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    colimit.ι F j ≫
      modularSpinor_Cl11SequentialColimit_gelfandSpectrumDescend F B =
      colimit.ι F j := by
  dsimp only [modularSpinor_Cl11SequentialColimit_gelfandSpectrumDescend] at *
  exact modularSpinor_filteredColimit_gelfandSpectrum_stage F B j

/-- Modular-spinor transport still preserves the canonical three-form inside the
full sequential colimit bridge. -/
theorem modularSpinor_Cl11SequentialColimit_transport_preserves_threeForm
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (path : List E) (x y z : ModularSpinorCarrier) :
    canonicalSplitG2ThreeFormValue
        ((modularSpinorTransport
          B.spectrumBridge.boundaryBridge.connection path) x)
        ((modularSpinorTransport
          B.spectrumBridge.boundaryBridge.connection path) y)
        ((modularSpinorTransport
          B.spectrumBridge.boundaryBridge.connection path) z) =
      canonicalSplitG2ThreeFormValue x y z := by
  have h := modularSpinor_filteredColimit_transport_preserves_threeForm F B path x y z
  simp_all [modularSpinorTransport]
  <;> exact h

/-- The concrete phase axis image remains available inside the joint bridge. -/
def cl11_sequentialColimit_phaseAxisImage : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit :=
  phaseAxisImage

/-- The phase axis image is the global phase axis. -/
theorem cl11_sequentialColimit_phaseAxisImage_eq_globalPhaseAxis :
    cl11_sequentialColimit_phaseAxisImage = globalPhaseAxis :=
  phaseAxisImage_eq_globalPhaseAxis

/-- The phase axis image squares to -1 in the limit carrier. -/
theorem cl11_sequentialColimit_phaseAxisImage_sq :
    cl11_sequentialColimit_phaseAxisImage * cl11_sequentialColimit_phaseAxisImage =
      -(1 : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit) :=
  phaseAxisImage_sq

/-- Every finite advance of the phase axis has the same carrier image. -/
theorem cl11_sequentialColimit_phaseAxisImage_finiteAdvance (k : ℕ) :
    ofStage (1 + k) (finiteAdvance 1 k phaseAxisStage) = cl11_sequentialColimit_phaseAxisImage :=
  phaseAxisImage_finiteAdvance k

/-- The phase element induces the inner derivation law on the limit carrier. -/
theorem cl11_sequentialColimit_phaseAxisImage_commutator_derivation
  (X Y : InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit) :
    (cl11_sequentialColimit_phaseAxisImage * (X * Y) - (X * Y) * cl11_sequentialColimit_phaseAxisImage) =
      (cl11_sequentialColimit_phaseAxisImage * X - X * cl11_sequentialColimit_phaseAxisImage) * Y +
        X * (cl11_sequentialColimit_phaseAxisImage * Y - Y * cl11_sequentialColimit_phaseAxisImage) :=
  phaseAxisImage_commutator_derivation X Y

/-- The sequential colimit cocone readout is invariant under finite bonding steps. -/
theorem cl11_sequentialColimit_toLimit_bondSeq
  (n m : ℕ) (x : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n) :
    cl11System.toLimit (n + m) (cl11System.bondSeq n m x) = cl11System.toLimit n x :=
  cl11_toLimit_bondSeq n m x

/-- A finite-stage property compatible with transitions lifts along the bonding sequence. -/
theorem cl11_sequentialColimit_compatibleProperty_bondSeq
  (P : ∀ n : ℕ, InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n → Prop)
  (hP : cl11System.CompatibleProperty P)
  (n m : ℕ) (x : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n) (hx : P n x) :
    P (n + m) (cl11System.bondSeq n m x) := by
  exact SequentialStageSystem.compatibleProperty_bondSeq cl11System P hP n m x hx

end

end InfoGeometry.Canonical
