import InfoGeometry.Canonical.ModularSpinorCuntzStageExchangeTopologicalBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Canonical.Cl11CuntzStageComplexificationTopologicalBridge
import InfoGeometry.Clifford.Cl11TensorTower

namespace InfoGeometry.Canonical

open CategoryTheory
open CategoryTheory.Limits
open FilteredColimit.Native.Topological
open scoped Kronecker
open InfoGeometry.Canonical.Cl11CuntzStageComplexificationTopologicalBridge
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalGNSBridge

noncomputable section

universe u

/-!
# Modular-spinor / Cl(1,1)-to-Cuntz stage complexification bridge

This file adds the next honest node after
`ModularSpinorCuntzStageExchangeTopologicalBridge`. The current repository
already owns:

* a modular-spinor / Cuntz-stage exchange topological bridge;
* a genuine finite-stage Cl(1,1)-to-Cuntz complexification bridge with
  normalized-trace readout compatibility.

What it does not own is a theorem identifying the modular-spinor sheaf/spectrum
lane with the Cl(1,1) tensor tower or proving exchange/KMS compatibility with
that complexification. Accordingly, this file only packages the two owner
surfaces together and re-exports the native theorems already proved in each.
-/

variable {E Sections BoundarySections Gr Open : Type*}
variable [AddCommGroup Sections] [Module ℝ Sections]
variable [AddCommGroup BoundarySections] [Module ℝ BoundarySections]
variable [TopologicalSpace Gr] [Category Open]
variable {J : Type u} [Category.{u, u} J]

/-- The sheaf cover condition remains available inside the complexification bridge. -/
theorem modularSpinor_Cl11CuntzStageComplexification_monogenicSheaf_isSheafFor
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    Presieve.IsSheafFor
      B.spectrumBridge.sheafData.sections
      B.spectrumBridge.sheafData.cover :=
  modularSpinor_CuntzStageExchangeTopological_monogenicSheaf_isSheafFor F B

/-- The monogenic section membership theorem remains available inside the
complexification bridge. -/
theorem modularSpinor_Cl11CuntzStageComplexification_monogenicSection_mem
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (U : Open)
  (s : B.spectrumBridge.sheafData.monogenicSections U) :
    (s : B.spectrumBridge.sheafData.sections.obj (Opposite.op U))
      ∈ B.spectrumBridge.sheafData.monogenicSections U :=
  modularSpinor_CuntzStageExchangeTopological_monogenicSection_mem F B U s

/-- The DN-kernel identity remains available inside the complexification bridge. -/
theorem modularSpinor_Cl11CuntzStageComplexification_boundary_kernel_eq_traceMonogenic
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    LinearMap.ker
      B.spectrumBridge.boundaryBridge.boundaryData.dirichletToNeumann =
      traceMonogenic B.spectrumBridge.boundaryBridge.boundaryData :=
  modularSpinor_CuntzStageExchangeTopological_boundary_kernel_eq_traceMonogenic F B

/-- The Gelfand-spectrum descent map remains available inside the complexification bridge. -/
noncomputable def modularSpinor_Cl11CuntzStageComplexification_gelfandSpectrumDescend
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F) :
    GelfandSpectrum F ⟶ GelfandSpectrum F :=
  modularSpinor_CuntzStageExchangeTopological_gelfandSpectrumDescend F B

@[reassoc (attr := simp)]
theorem modularSpinor_Cl11CuntzStageComplexification_gelfandSpectrum_stage
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    colimit.ι F j ≫
      modularSpinor_Cl11CuntzStageComplexification_gelfandSpectrumDescend F B =
      colimit.ι F j := by
  dsimp only [modularSpinor_Cl11CuntzStageComplexification_gelfandSpectrumDescend] at *
  exact modularSpinor_CuntzStageExchangeTopological_gelfandSpectrum_stage F B j

/-- The filtered-colimit stage injections remain available inside the
complexification bridge. -/
noncomputable def modularSpinor_Cl11CuntzStageComplexification_stageInjection
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  (j : J) :
    B.stageDiagram.obj j ⟶
      colimit B.stageDiagram :=
  modularSpinor_CuntzStageExchangeTopological_stageInjection F B j

/-- Naturality of the filtered-colimit stage injections remains available inside the
complexification bridge. -/
theorem modularSpinor_Cl11CuntzStageComplexification_stageInjection_naturality
  (F : J ⥤ TopCat.{u})
  (B : ModularSpinorFilteredColimitBridge
    (E := E) (Sections := Sections) (BoundarySections := BoundarySections)
    (Gr := Gr) (Open := Open) F)
  {j j' : J} (f : j ⟶ j') :
    B.stageDiagram.map f ≫
      modularSpinor_Cl11CuntzStageComplexification_stageInjection F B j' =
      modularSpinor_Cl11CuntzStageComplexification_stageInjection F B j := by
  dsimp only [modularSpinor_Cl11CuntzStageComplexification_stageInjection] at *
  exact modularSpinor_CuntzStageExchangeTopological_stageInjection_naturality F B f

/-- Modular-spinor transport still preserves the canonical three-form inside the
full complexification bridge. -/
theorem modularSpinor_Cl11CuntzStageComplexification_transport_preserves_threeForm
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
  have h := modularSpinor_CuntzStageExchangeTopological_transport_preserves_threeForm F B path x y z
  simp_all [modularSpinorTransport]
  <;> exact h

/-- The finite-stage complexification commutes with the tensor successor. -/
theorem cl11CuntzStage_complexify_transition
  (n : ℕ)
  (A : ClStage n) :
    complexifyClTensorStage (Nat.succ n) (matStageEmbed n A) =
      (complexifyClTensorStage n A) ⊗ₖ
        (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  complexifyClTensorStage_transition n A

/-- Under the explicit index-coherence property, the finite-stage Cl(1,1)
complexification agrees with the concrete Cuntz step. -/
theorem cl11CuntzStage_complexify_concreteStep_of_indexCoherence
  (n : ℕ)
  (A : ClStage n)
  (hcoh : FinReindexCoherence n) :
    complexifyClStage (Nat.succ n) (stageEmbed n A) =
      concreteStep n (complexifyClStage n A) :=
  complexifyClStage_concreteStep_of_indexCoherence n A hcoh

/-- The finite-stage trace compatibility remains available inside the joint bridge. -/
theorem cl11CuntzStage_complexify_trace
  (n : ℕ)
  (A : ClStage n) :
    Matrix.trace (complexifyClStage n A) =
      Complex.ofReal (Matrix.trace A) :=
  complexifyClStage_trace n A

/-- The finite-stage normalized-trace compatibility remains available inside the
joint bridge. -/
theorem cl11CuntzStage_complexify_normalizedTrace
  (n : ℕ)
  (A : ClStage n) :
    InfoGeometry.Canonical.CuntzMatrixTowerInstantiation.matrixTraceFunctional n (complexifyClStage n A) =
      Complex.ofReal (InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace n A) :=
  complexifyClStage_normalizedTrace n A

/-- The TopCat readout compatibility for the normalized trace remains available
inside the joint bridge. -/
theorem cl11CuntzStage_complexify_normalizedTraceTopCat_readout
  (n : ℕ)
  (A : ClStage n) :
    (TopCat.ofHom (InfoGeometry.Canonical.CuntzMatrixTraceTopologicalGNSBridge.continuousRealTrace n))
        (complexifyClStageTopCatHom n A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace n A :=
  complexifyClStage_normalizedTraceTopCat_readout n A

end

end InfoGeometry.Canonical
