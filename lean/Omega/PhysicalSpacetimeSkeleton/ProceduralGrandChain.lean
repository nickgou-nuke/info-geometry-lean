import Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree
import Omega.PhysicalSpacetimeSkeleton.ClockTransportEquation
import Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure
import Omega.PhysicalSpacetimeSkeleton.GravitationalScalarUniqueness
import Omega.PhysicalSpacetimeSkeleton.InstantiationCriterion
import Omega.PhysicalSpacetimeSkeleton.LocalClockPotential
import Omega.PhysicalSpacetimeSkeleton.LocalRedshift

namespace Omega.PhysicalSpacetimeSkeleton

universe u

open Omega.PhysicalSpacetimeSkeleton.KernelizationTemplate

/-- Paper-facing procedural grand chain: the chapter-local package is assembled by gluing the
already formalized wrappers for instantiation, clock transport, local clock potential, local
redshift, audited seeds, global Lorentz structure, and gravitational scalar uniqueness.
    thm:physical-spacetime-procedural-grand-chain -/
theorem paper_physical_spacetime_procedural_grand_chain :
    ∀ (I : Omega.PhysicalSpacetimeSkeleton.InstantiationCriterion.AcceptableInstantiation)
      (localGlobalTrivial :
        ∀ {a : I.Addr}, (I.Fiber a).Nonempty → ¬ I.Obstructed a)
      (localGlobalNull :
        ∀ {a : I.Addr}, I.Fiber a = (∅ : Set I.Obj) → I.NullReadout a)
      (witnessObstructed : I.Obstructed I.witness)
      (hinv : ∀ {x x' y y'}, I.R.r x x' → I.R.r y y' → I.K x y = I.K x' y')
      (hpsd : ∀ {ι : Type} [Fintype ι] (ψ : ι → I.Visible) (a : ι → ℝ),
        0 ≤ quadraticEnergy I.K ψ a)
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
      (G : MinimalSecondOrderCovariantClosure) (admissible : Prop) (hAdm : admissible)
      (affineActionEquivalence :
        admissible → ∃ a b divergence : ℝ,
          G.gravitationalScalar = a * G.ricciScalar + b + divergence)
      (normalizeAffinePart :
        admissible →
          ∀ {a b divergence : ℝ},
            G.gravitationalScalar = a * G.ricciScalar + b + divergence →
              a = 1 ∧ b = -2 * G.cosmologicalConstant),
      ((I.Fiber I.witness = (∅ : Set I.Obj) ∧ I.NullReadout I.witness) ∧
        (∀ {ι : Type} [Fintype ι] (ψ ψ' : ι → I.Visible) (a : ι → ℝ),
          (∀ i, I.R.r (ψ i) (ψ' i)) →
            quadraticEnergy I.K ψ a = quadraticEnergy I.K ψ' a ∧
              0 ≤ quadraticEnergy I.K ψ a) ∧
          continuumLimit) ∧
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
        (∃ a b divergence : ℝ, G.gravitationalScalar = a * G.ricciScalar + b + divergence) ∧
        (∃ a b : ℝ,
          a = 1 ∧
            b = -2 * G.cosmologicalConstant ∧
              a * G.ricciScalar + b = G.ricciScalar - 2 * G.cosmologicalConstant) := by
  intro I localGlobalTrivial localGlobalNull witnessObstructed hinv hpsd continuumLimit
    continuumWitness ClockC _ delta ThetaU dDeltaTau dA OmegaU hTheta hDeltaTau hOmega hFlat hExact
    U N A B deltaT nuA nuB hNA hNB hT hA hB v hv ι _ F metric_compat lorentz G admissible hAdm
    affineActionEquivalence normalizeAffinePart
  have hInst :
      (I.Fiber I.witness = (∅ : Set I.Obj) ∧ I.NullReadout I.witness) ∧
        (∀ {ι : Type} [Fintype ι] (ψ ψ' : ι → I.Visible) (a : ι → ℝ),
          (∀ i, I.R.r (ψ i) (ψ' i)) →
            quadraticEnergy I.K ψ a = quadraticEnergy I.K ψ' a ∧
              0 ≤ quadraticEnergy I.K ψ a) ∧
          continuumLimit :=
    Omega.PhysicalSpacetimeSkeleton.InstantiationCriterion.paper_physical_spacetime_instantiation_criterion
      I localGlobalTrivial localGlobalNull witnessObstructed hinv hpsd continuumLimit
        continuumWitness
  have hClock : delta ThetaU = OmegaU :=
    paper_physical_spacetime_clock_transport_equation delta ThetaU dDeltaTau dA OmegaU
      hTheta hDeltaTau hOmega
  have hPotential : ∃ φU : ClockC, ThetaU = delta φU :=
    paper_physical_spacetime_local_clock_potential delta ThetaU dDeltaTau dA OmegaU
      hTheta hDeltaTau hOmega hFlat hExact
  have hRedshift : nuB / nuA = N A / N B :=
    paper_physical_spacetime_local_redshift N A B deltaT nuA nuB hNA hNB hT hA hB
  have hRank :
      Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.auditedSeedMatrix.rank = 3 :=
    Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.paper_physical_spacetime_audited_seed_rank_three
  have hQuad :
      0 <
        dotProduct v
          ((Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.auditedSeedMatrix.transpose *
              Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.auditedSeedMatrix).mulVec v) :=
    Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree.paper_physical_spacetime_audited_seed_local_space_quadratic_positive
      v hv
  obtain ⟨g, hg, hLorentz⟩ :=
    Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure.paper_physical_spacetime_global_lorentz_structure
      F metric_compat lorentz
  obtain ⟨ga, gb, divergence, hAffine, hga, hgb, hEinstein⟩ :=
    paper_physical_spacetime_gravitational_scalar_uniqueness G admissible hAdm
      affineActionEquivalence normalizeAffinePart
  refine ⟨hInst, hClock, hPotential, hRedshift, hRank, hQuad, ?_, ?_, ?_, ?_⟩
  · exact ⟨g, hg⟩
  · exact ⟨g, hLorentz⟩
  · exact ⟨ga, gb, divergence, hAffine⟩
  · exact ⟨ga, gb, hga, hgb, hEinstein⟩

/-- Once the backend preserves the chapter interface, the quantum and spacetime outputs are
structural consequences and require no extra axioms.
    cor:physical-spacetime-no-new-axioms -/
theorem paper_physical_spacetime_no_new_axioms
    (backendPreservesInterface quantumStructure spacetimeStructure : Prop)
    (hQuantum : backendPreservesInterface → quantumStructure)
    (hSpacetime : backendPreservesInterface → spacetimeStructure) :
    backendPreservesInterface → quantumStructure ∧ spacetimeStructure := by
  intro hBackend
  exact ⟨hQuantum hBackend, hSpacetime hBackend⟩

end Omega.PhysicalSpacetimeSkeleton
