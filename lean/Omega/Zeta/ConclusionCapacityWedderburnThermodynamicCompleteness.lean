import Omega.Conclusion.CapacityFiniteCompleteness
import Omega.Zeta.ConclusionWedderburnThresholdHolography

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:conclusion-capacity-wedderburn-thermodynamic-completeness`. The finite
capacity completeness package supplies the histogram/tail/capacity/moment equivalence for the
concrete fiber multiplicity profile, while Wedderburn threshold holography identifies the class
with the same histogram. -/
theorem paper_conclusion_capacity_wedderburn_thermodynamic_completeness
    (D : Omega.Zeta.conclusion_wedderburn_threshold_holography_data) :
    let h : ℕ → ℕ := D.histogram
    let N : ℕ → ℕ := D.tailCounts
    let C : ℕ → ℕ := D.capacityCurve
    Omega.Conclusion.FiniteMultiplicityDataEquivalent (X := Fin D.outputSize) h N C
        (fun q => Finset.sum Finset.univ
          (fun x : Fin D.outputSize => D.fiberMultiplicity x ^ q)) ∧
      D.histogramDeterminesWedderburnClass := by
  let d : Fin D.outputSize → ℕ := D.fiberMultiplicity
  have hfinite :=
    Omega.Conclusion.paper_conclusion_capacity_finite_completeness
      (X := Fin D.outputSize) d
  have hwedderburn := Omega.Zeta.paper_conclusion_wedderburn_threshold_holography D
  refine ⟨?_, hwedderburn.2.2⟩
  change Omega.Conclusion.FiniteMultiplicityDataEquivalent
    (fun k => Fintype.card
      {x : Fin D.outputSize // Omega.POM.oracleFiberMultiplicity D.map x = k})
    (fun t => Fintype.card
      {x : Fin D.outputSize // t ≤ Omega.POM.oracleFiberMultiplicity D.map x})
    (Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve
      (Omega.POM.oracleFiberMultiplicity D.map))
    (fun q => ∑ x : Fin D.outputSize,
      Omega.POM.oracleFiberMultiplicity D.map x ^ q)
  exact hfinite

end Omega.Zeta
