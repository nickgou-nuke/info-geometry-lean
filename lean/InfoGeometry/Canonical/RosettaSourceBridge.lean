import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.ConformalAlgebra
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.WeylAnomalySource
import InfoGeometry.Quantum.ModularAnomaly

/-!
# Research.RosettaSourceBridge

Lower Rosetta ownership for the source-tension and modular-commutator lane.
This file keeps the checked scalar, operator, and modular source identifications
in the `InfoGeometry.Canonical.Rosetta` namespace without using the umbrella
facade as the owner.
-/

namespace InfoGeometry.Canonical.Rosetta

section ModularCPTRosetta

open InfoGeometry.Canonical.ConformalAlgebra
open InfoGeometry.Quantum.ModularAnomaly

variable {E : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Xc" => (InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E)

noncomputable local instance : NormedAddCommGroup Xc := by
  change NormedAddCommGroup (InfoGeometry.Krein.DoubledSpace E)
  infer_instance

noncomputable local instance : NormedSpace ℝ Xc := by
  change NormedSpace ℝ (InfoGeometry.Krein.DoubledSpace E)
  infer_instance

noncomputable local instance : CompleteSpace Xc := by
  change CompleteSpace (InfoGeometry.Krein.DoubledSpace E)
  infer_instance

/--
In the concrete real-Majorana doubled model, the legacy modular axis
`modularComplexI` is exactly the internal split-Clifford axis `K = J ∘ ε`.
-/
@[simp] theorem modularComplexI_toLinearMap_eq_realMajoranaKAxis :
    (InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := E)).toLinearMap =
      (InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E).K := by
  rfl

/--
Owner-name form of the same real-Majorana phase-axis bridge.
-/
@[simp] theorem complex_i_toLinearMap_eq_realMajoranaKAxis :
    (InfoGeometry.Krein.complex_i (E := E)).toLinearMap =
      (InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E).K := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i] using
    modularComplexI_toLinearMap_eq_realMajoranaKAxis (E := E)

/--
Scalar bridge: the conformal source tension is presented as the transported
Einstein residual under the explicit Ricci transport interface.
-/
theorem sourceTension_eq_transportedEinsteinResidual
    (CBA : ConformalBeliefAlgebra E)
    (R : InfoGeometry.Canonical.RicciMongeAmpere.RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection K x V)
    (hSource :
      InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CBA.CI.chiralScale) :
    CBA.CI.chiralScale =
      InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ := by
  simpa [eq_comm] using hSource

/--
Operator-source bridge: the transported Einstein residual is exactly the scalar
chemical-potential source used in the Bogoliubov/Fock layer.
-/
@[simp] theorem transportedEinsteinResidual_eq_einsteinInducedChemicalPotential
    (R : InfoGeometry.Canonical.RicciMongeAmpere.RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection K x V) :
    InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) V Γ =
      InfoGeometry.Canonical.BogoliubovFockSuper.einsteinInducedChemicalPotential R K x scalar Λ V Γ := by
  rfl

/--
The Einstein-induced chemical potential lifts to the Fock layer as the scalar
identity deformation operator.
-/
@[simp] theorem einsteinInducedChemicalPotential_lift_eq_einsteinFockDeformationOperator
    (R : InfoGeometry.Canonical.RicciMongeAmpere.RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection K x V) :
    InfoGeometry.Canonical.BogoliubovFockSuper.einsteinFockDeformationOperator R K x scalar Λ V Γ =
      InfoGeometry.Canonical.BogoliubovFockSuper.einsteinInducedChemicalPotential R K x scalar Λ V Γ
        • ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) := by
  rfl

/--
Facade theorem packaging the three checked presentations of the same source
surface: scalar transport, chemical-potential lift, and modular commutator
shadow.
-/
private theorem rosetta_source_tension_three_presentations
    [FiniteDimensional ℝ E]
    (CBA : ConformalBeliefAlgebra E)
    (hCartan : CBA.GeneratorCartanDecomposition)
    (R : InfoGeometry.Canonical.RicciMongeAmpere.RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection K x V)
    (hSource :
      InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CBA.CI.chiralScale)
    (hAnom : CBA.CI.chiralAnomalyOperator ≠ 0)
    (M : TopologicalMajoranaShadow Xc)
    (epsCLM : Xc →L[ℝ] Xc)
    (hSigmaMap : ∀ t : ℝ, (M.sigma t : Xc →L[ℝ] Xc) = Cl11Shadow.sigmaMap epsCLM t)
    (U : Xc ≃L[ℝ] Xc) :
    InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := E) = InfoGeometry.Krein.dilationOperator (E := E) ∧
      CBA.IsVolumePreservingPart CBA.M ∧
      CBA.IsWeylDilationPart CBA.D ∧
      CBA.CI.chiralScale =
        InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
          (scalar := scalar) (Λ := Λ) V Γ ∧
      InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ =
          InfoGeometry.Canonical.BogoliubovFockSuper.einsteinInducedChemicalPotential R K x scalar Λ V Γ ∧
      InfoGeometry.Canonical.BogoliubovFockSuper.einsteinFockDeformationOperator R K x scalar Λ V Γ =
        InfoGeometry.Canonical.BogoliubovFockSuper.einsteinInducedChemicalPotential R K x scalar Λ V Γ
          • ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) ∧
      M.modularAnomalyGenerator U =
        (U.symm : Xc →L[ℝ] Xc).comp
          (epsCLM.comp (U : Xc →L[ℝ] Xc) - (U : Xc →L[ℝ] Xc).comp epsCLM) := by
  have hWeyl :
      CBA.IsVolumePreservingPart CBA.M
        ∧ CBA.IsWeylDilationPart CBA.D
        ∧ InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
            (scalar := scalar) (Λ := Λ) V Γ ≠ 0 := by
    refine ⟨CBA.M_in_volumePreserving_of_cartan hCartan,
      CBA.D_in_weylDilation_of_cartan hCartan, ?_⟩
    exact InfoGeometry.Canonical.WeylInformationGauge.nonzeroAnomaly_sources_transportedEinsteinResidual
      (CI := CBA.CI) (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) hSource hAnom
  rcases hWeyl with ⟨hM, hD, _hResidual⟩
  refine ⟨InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_dilationOperator (E := E), hM, hD, ?_, ?_, ?_, ?_⟩
  · exact sourceTension_eq_transportedEinsteinResidual
      (CBA := CBA) (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) hSource
  · exact transportedEinsteinResidual_eq_einsteinInducedChemicalPotential
      (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)
  · exact einsteinInducedChemicalPotential_lift_eq_einsteinFockDeformationOperator
      (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)
  · exact InfoGeometry.Quantum.ModularAnomaly.Cl11Shadow.modularAnomalyGenerator_eq_concrete_commutator_shadow
      (M := M) (epsCLM := epsCLM) (hSigmaMap := hSigmaMap) (U := U)

/--
Compatibility wrapper preserving the earlier Rosetta capstone surface while now
factoring through the explicit helper theorem family above.
-/
private theorem modularCPT_source_rosetta
    [FiniteDimensional ℝ E]
    (CBA : ConformalBeliefAlgebra E)
    (hCartan : CBA.GeneratorCartanDecomposition)
    (R : InfoGeometry.Canonical.RicciMongeAmpere.RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection K x V)
    (hSource :
      InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CBA.CI.chiralScale)
    (hAnom : CBA.CI.chiralAnomalyOperator ≠ 0)
    (M : TopologicalMajoranaShadow Xc)
    (epsCLM : Xc →L[ℝ] Xc)
    (hSigmaMap : ∀ t : ℝ, (M.sigma t : Xc →L[ℝ] Xc) = Cl11Shadow.sigmaMap epsCLM t)
    (U : Xc ≃L[ℝ] Xc) :
    InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := E) = InfoGeometry.Krein.dilationOperator (E := E) ∧
      CBA.IsVolumePreservingPart CBA.M ∧
      CBA.IsWeylDilationPart CBA.D ∧
      InfoGeometry.Canonical.BogoliubovFockSuper.einsteinInducedChemicalPotential R K x scalar Λ V Γ ≠ 0 ∧
      M.modularAnomalyGenerator U =
        (U.symm : Xc →L[ℝ] Xc).comp
          (epsCLM.comp (U : Xc →L[ℝ] Xc) - (U : Xc →L[ℝ] Xc).comp epsCLM) := by
  have hWeyl :
      CBA.IsVolumePreservingPart CBA.M
        ∧ CBA.IsWeylDilationPart CBA.D
        ∧ InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual (R := R) (K := K) (x := x)
            (scalar := scalar) (Λ := Λ) V Γ ≠ 0 := by
    refine ⟨CBA.M_in_volumePreserving_of_cartan hCartan,
      CBA.D_in_weylDilation_of_cartan hCartan, ?_⟩
    exact InfoGeometry.Canonical.WeylInformationGauge.nonzeroAnomaly_sources_transportedEinsteinResidual
      (CI := CBA.CI) (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
      (V := V) (Γ := Γ) hSource hAnom
  rcases hWeyl with ⟨hM, hD, hResidual⟩
  have hPack := rosetta_source_tension_three_presentations
    (CBA := CBA) (hCartan := hCartan) (R := R) (K := K) (x := x)
    (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)
    (hSource := hSource) (hAnom := hAnom)
    (M := M) (epsCLM := epsCLM) (hSigmaMap := hSigmaMap) (U := U)
  rcases hPack with ⟨hKAxis, _hM, _hD, _hSourceEq, hμEq, _hLiftEq, hMod⟩
  refine ⟨hKAxis, hM, hD, ?_, hMod⟩
  simpa [hμEq] using hResidual

end ModularCPTRosetta

end InfoGeometry.Canonical.Rosetta
