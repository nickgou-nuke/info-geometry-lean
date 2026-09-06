import InfoGeometry.Canonical.GromovWittenPrepotentialGaugeQuotientTopological

namespace InfoGeometry.Canonical

open scoped BigOperators

def prepotentialEntryReadout {dim : ℕ} (i j k : Fin dim) :
    GromovWittenPrepotential dim → ℝ :=
  fun F => F.F3 i j k

theorem continuous_prepotentialEntryReadout {dim : ℕ}
    (i j k : Fin dim) :
    Continuous (prepotentialEntryReadout i j k) := by
  have hF3 : Continuous (fun F : GromovWittenPrepotential dim => F.F3) :=
    continuous_induced_dom
  have hi : Continuous (fun F : GromovWittenPrepotential dim => F.F3 i) :=
    (continuous_apply i).comp hF3
  have hij : Continuous (fun F : GromovWittenPrepotential dim => F.F3 i j) :=
    (continuous_apply j).comp hi
  exact (continuous_apply k).comp hij

theorem continuous_gromovWittenInvariant_readout {dim : ℕ}
    (i j k : Fin dim) :
    Continuous (fun F : GromovWittenPrepotential dim =>
      gromovWittenInvariant F i j k) := by
  exact continuous_prepotentialEntryReadout i j k

def prepotentialWDVVResidualReadout {dim : ℕ}
    (i j k l : Fin dim) : GromovWittenPrepotential dim → ℝ :=
  fun F =>
    (∑ a : Fin dim, F.F3 i j a * F.F3 a k l) -
      ∑ a : Fin dim, F.F3 j k a * F.F3 i a l

theorem prepotentialWDVVResidualReadout_eq_zero {dim : ℕ}
    (F : GromovWittenPrepotential dim) (i j k l : Fin dim) :
    prepotentialWDVVResidualReadout i j k l F = 0 := by
  unfold prepotentialWDVVResidualReadout
  rw [F.wdvv]
  ring

theorem continuous_prepotentialWDVVResidualReadout {dim : ℕ}
    (i j k l : Fin dim) :
    Continuous (prepotentialWDVVResidualReadout i j k l) := by
  unfold prepotentialWDVVResidualReadout
  apply Continuous.sub
  · apply continuous_finset_sum
    intro a ha
    exact (continuous_prepotentialEntryReadout i j a).mul
      (continuous_prepotentialEntryReadout a k l)
  · apply continuous_finset_sum
    intro a ha
    exact (continuous_prepotentialEntryReadout j k a).mul
      (continuous_prepotentialEntryReadout i a l)

theorem prepotentialWDVVResidualReadout_zeroLocus_isClosed {dim : ℕ}
    (i j k l : Fin dim) :
    IsClosed {F : GromovWittenPrepotential dim |
      prepotentialWDVVResidualReadout i j k l F = 0} := by
  simpa only [Set.preimage, Set.mem_setOf_eq] using
    (isClosed_singleton : IsClosed ({0} : Set ℝ)).preimage
      (continuous_prepotentialWDVVResidualReadout i j k l)

end InfoGeometry.Canonical
