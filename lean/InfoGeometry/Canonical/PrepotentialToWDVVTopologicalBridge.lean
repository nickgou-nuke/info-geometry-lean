import InfoGeometry.Canonical.FiniteWDVVSystemTopologicalReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.GromovWittenPrepotentialTopologicalReadout

namespace InfoGeometry.Canonical

theorem continuous_prepotentialToWDVV {dim : ℕ} :
    Continuous (prepotentialToWDVV :
      GromovWittenPrepotential dim → FiniteWDVVSystem dim) := by
  rw [continuous_induced_rng]
  change Continuous (fun F : GromovWittenPrepotential dim => F.F3)
  exact continuous_induced_dom

theorem prepotentialToWDVV_residual_readout {dim : ℕ}
    (F : GromovWittenPrepotential dim) (i j k l : Fin dim) :
    finiteWDVVResidual (prepotentialToWDVV F) i j k l =
      prepotentialWDVVResidualReadout i j k l F := rfl

theorem prepotentialToWDVV_residual_zero {dim : ℕ}
    (F : GromovWittenPrepotential dim) (i j k l : Fin dim) :
    finiteWDVVResidual (prepotentialToWDVV F) i j k l = 0 := by
  exact finiteWDVVResidual_eq_zero (prepotentialToWDVV F) i j k l

end InfoGeometry.Canonical
