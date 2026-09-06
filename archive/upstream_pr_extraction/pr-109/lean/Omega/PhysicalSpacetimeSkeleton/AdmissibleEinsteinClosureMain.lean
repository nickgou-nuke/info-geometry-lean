import Omega.PhysicalSpacetimeSkeleton.AdmissibleGlobalEinsteinEquation
import Omega.PhysicalSpacetimeSkeleton.ProceduralGrandChain

namespace Omega.PhysicalSpacetimeSkeleton

universe u

/-- Paper-facing closure theorem packaging the full procedural grand chain together with the
admissible global Einstein equation. -/
theorem paper_physical_spacetime_admissible_einstein_closure_main :
    ∀ (I : Omega.PhysicalSpacetimeSkeleton.InstantiationCriterion.AcceptableInstantiation)
      (localGlobalTrivial :
        ∀ {a : I.Addr}, (I.Fiber a).Nonempty → ¬ I.Obstructed a)
      (localGlobalNull :
        ∀ {a : I.Addr}, I.Fiber a = (∅ : Set I.Obj) → I.NullReadout a)
      (witnessObstructed : I.Obstructed I.witness)
      (hinv : ∀ {x x' y y'}, I.R.r x x' → I.R.r y y' → I.K x y = I.K x' y')
      (hpsd : ∀ {ι : Type} [Fintype ι] (ψ : ι → I.Visible) (a : ι → ℝ),
        0 ≤ Omega.PhysicalSpacetimeSkeleton.KernelizationTemplate.quadraticEnergy I.K ψ a)
      (continuumLimit : Prop)
      (continuumWitness : continuumLimit)
      {ClockC : Type*} [AddGroup ClockC]
      (delta : ClockC → ClockC) (ThetaU dDeltaTau dA OmegaU : ClockC)
      (hTheta : delta ThetaU = dDeltaTau - dA)
      (hDeltaTau : dDeltaTau = 0)
      (hOmega : OmegaU = -dA)
      (hFlat : OmegaU = 0)
      (hExact : delta ThetaU = 0 → ∃ φU : ClockC, delta φU = ThetaU)
      {U : Type} (N : U → Real) (A B : U) (deltaT nuA nuB : Real)
      (hNA : N A != 0) (hNB : N B != 0) (hT : deltaT != 0)
      (hA : nuA = 1 / (N A * deltaT))
      (hB : nuB = 1 / (N B * deltaT))
      (v : Fin 3 → ℝ) (hv : v ≠ 0)
      {ι : Type u} [Fintype ι]
      (F : Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure.CompatibleLorentzFamily ι)
      (metric_compat :
        ∀ {i j} {x : F.Chart i} {y : F.Chart j},
          F.overlapSetoid.r ⟨i, x⟩ ⟨j, y⟩ → F.metric i x = F.metric j y)
      (lorentz : ∀ i x,
        Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure.IsLorentzValue (F.metric i x))
      (D : Omega.PhysicalSpacetimeSkeleton.AdmissibleEinsteinClosure)
      (admissible : Prop) (hAdm : admissible)
      (affineActionEquivalence :
        admissible → ∃ a b divergence : ℝ,
          D.gravitationalScalar = a * D.ricciScalar + b + divergence)
      (normalizeAffinePart :
        admissible →
          ∀ {a b divergence : ℝ},
            D.gravitationalScalar = a * D.ricciScalar + b + divergence →
              a = 1 ∧ b = -2 * D.cosmologicalConstant)
      (eulerLagrange_identity :
        admissible →
          D.einsteinTensor + D.cosmologicalConstant * D.metric =
            D.couplingConstant * D.stressEnergy),
      delta ThetaU = OmegaU ∧
        (∃ φU : ClockC, ThetaU = delta φU) ∧
          nuB / nuA = N A / N B ∧
            Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.auditedSeedMatrix.rank = 3 ∧
              0 <
                dotProduct v
                  ((Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.auditedSeedMatrix.transpose *
                      Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.auditedSeedMatrix).mulVec v) ∧
                (∃ g :
                    Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure.maximalAdmissibleDomain F →
                      ℝ,
                  ∀ i x,
                    g
                        (Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure.pointClass F i x) =
                      F.metric i x) ∧
                  (∃ g :
                      Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure.maximalAdmissibleDomain F →
                        ℝ,
                    ∀ q,
                      Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure.IsLorentzValue (g q)) ∧
                    (∃ a b : ℝ,
                      a = 1 ∧
                        b = -2 * D.cosmologicalConstant ∧
                          a * D.ricciScalar + b =
                            D.ricciScalar - 2 * D.cosmologicalConstant) ∧
                      D.einsteinTensor + D.cosmologicalConstant * D.metric =
                        D.couplingConstant * D.stressEnergy := by
  intro I localGlobalTrivial localGlobalNull witnessObstructed hinv hpsd continuumLimit
    continuumWitness ClockC _ delta ThetaU dDeltaTau dA OmegaU hTheta hDeltaTau hOmega hFlat hExact U N A B
    deltaT nuA nuB hNA hNB hT hA hB v hv ι _ F metric_compat lorentz D admissible hAdm
    affineActionEquivalence normalizeAffinePart eulerLagrange_identity
  obtain ⟨_hInst, hClock, hPotential, hRedshift, hRank, hQuad, hMetric, hValue,
      _hAffine, hEinstein⟩ :=
    paper_physical_spacetime_procedural_grand_chain
      (I := I) (delta := delta) (ThetaU := ThetaU) (dDeltaTau := dDeltaTau) (dA := dA)
      (localGlobalTrivial := localGlobalTrivial) (localGlobalNull := localGlobalNull)
      (witnessObstructed := witnessObstructed) (hinv := hinv) (hpsd := hpsd)
      (continuumLimit := continuumLimit) (continuumWitness := continuumWitness)
      (OmegaU := OmegaU) (hTheta := hTheta) (hDeltaTau := hDeltaTau) (hOmega := hOmega)
      (hFlat := hFlat) (hExact := hExact) (N := N) (A := A) (B := B) (deltaT := deltaT)
      (nuA := nuA) (nuB := nuB) (hNA := hNA) (hNB := hNB) (hT := hT) (hA := hA) (hB := hB)
      (v := v) (hv := hv) (F := F) (metric_compat := metric_compat) (lorentz := lorentz)
      (G := D.toMinimalSecondOrderCovariantClosure)
      admissible hAdm affineActionEquivalence normalizeAffinePart
  have hEquation :
      D.einsteinTensor + D.cosmologicalConstant * D.metric =
        D.couplingConstant * D.stressEnergy :=
    paper_physical_spacetime_admissible_global_einstein_equation D admissible hAdm
      eulerLagrange_identity
  exact ⟨hClock, hPotential, hRedshift, hRank, hQuad, hMetric, hValue, hEinstein, hEquation⟩

end Omega.PhysicalSpacetimeSkeleton
