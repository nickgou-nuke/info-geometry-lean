import InfoGeometry.Canonical.Rosetta

namespace InfoGeometry.Quantum.RosettaSynthesis

open InfoGeometry.Canonical
open InfoGeometry.Canonical.Rosetta
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
Thin quantum-facing wrapper around the checked Rosetta capstone.
It exposes the four source-tension presentations directly.
-/
theorem rosetta_source_tension_synthesis
    [FiniteDimensional ℝ E]
    (CBA : InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra E)
    (hCartan : CBA.GeneratorCartanDecomposition)
    (R : InfoGeometry.Canonical.RicciMongeAmpere.RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection K x V)
    (hSource :
      InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual
          (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ) V Γ
        = CBA.CI.chiralScale)
    (hAnom : CBA.CI.chiralAnomalyOperator ≠ 0)
    (M : TopologicalMajoranaShadow Xc)
    (epsCLM : Xc →L[ℝ] Xc)
    (hSigmaMap : ∀ t : ℝ, (M.sigma t : Xc →L[ℝ] Xc) = Cl11Shadow.sigmaMap epsCLM t)
    (U : Xc ≃L[ℝ] Xc) :
    CBA.CI.chiralScale =
        InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual
          (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ) V Γ
      ∧ InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual
          (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ) V Γ
          = einsteinInducedChemicalPotential R K x scalar Λ V Γ
      ∧ einsteinFockDeformationOperator R K x scalar Λ V Γ
          = einsteinInducedChemicalPotential R K x scalar Λ V Γ
              • ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)
      ∧ M.modularAnomalyGenerator U =
          (U.symm : Xc →L[ℝ] Xc).comp
            (epsCLM.comp (U : Xc →L[ℝ] Xc) - (U : Xc →L[ℝ] Xc).comp epsCLM) := by
  rcases rosetta_source_tension_three_presentations
      (CBA := CBA) (hCartan := hCartan)
      (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)
      (hSource := hSource) (hAnom := hAnom)
      (M := M) (epsCLM := epsCLM) (hSigmaMap := hSigmaMap) (U := U) with
    ⟨_, _, _, hScale, hChem, hLift, hMod⟩
  exact ⟨hScale, hChem, hLift, hMod⟩

/--
If the transported Einstein residual vanishes, then the chiral scale and
chemical-potential source vanish with it; together with a vanishing modular
generator this gives anomaly-free triality.
-/
theorem rosetta_anomaly_free_triality
    (CBA : InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra E)
    (R : InfoGeometry.Canonical.RicciMongeAmpere.RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E)
    (scalar Λ : ℝ)
    (V : InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein K x)
    (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection K x V)
    (M : TopologicalMajoranaShadow Xc)
    (U : Xc ≃L[ℝ] Xc)
    (hScale :
      CBA.CI.chiralScale =
        InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual
          (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ) V Γ)
    (hChem :
      InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual
          (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ) V Γ
        = einsteinInducedChemicalPotential R K x scalar Λ V Γ)
    (hResidual0 :
      InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual
          (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ) V Γ = 0)
    (hMod0 : M.modularAnomalyGenerator U = 0) :
    CBA.CI.chiralScale = 0
      ∧ einsteinInducedChemicalPotential R K x scalar Λ V Γ = 0
      ∧ M.modularAnomalyGenerator U = 0 := by
  refine ⟨?_, ?_, hMod0⟩
  · calc
      CBA.CI.chiralScale =
          InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual
            (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ) V Γ := hScale
      _ = 0 := hResidual0
  · calc
      einsteinInducedChemicalPotential R K x scalar Λ V Γ =
          InfoGeometry.Canonical.RicciMongeAmpere.transportedEinsteinResidual
            (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ) V Γ := hChem.symm
      _ = 0 := hResidual0

end InfoGeometry.Quantum.RosettaSynthesis
