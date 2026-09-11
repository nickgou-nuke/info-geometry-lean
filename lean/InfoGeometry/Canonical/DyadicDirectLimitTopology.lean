import InfoGeometry.Canonical.DyadicRankFamilyTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-!
# Induced topology on the concrete dyadic direct-limit carrier

The quotient carrier receives the topology transported from its concrete
dyadic-rational model.  This is a deliberate algebraic topology choice: it
does not assert a completion or a C*-algebra topology.
-/

noncomputable instance dyadicDirectLimitTopologicalSpace :
    TopologicalSpace DyadicDirectLimit :=
  TopologicalSpace.induced dyadicDirectLimitEquiv inferInstance

theorem continuous_dyadicDirectLimitEquiv :
    Continuous (dyadicDirectLimitEquiv : DyadicDirectLimit → DyadicRational) := by
  exact continuous_induced_dom

theorem continuous_dyadicDirectLimitEquiv_symm :
    Continuous (dyadicDirectLimitEquiv.symm : DyadicRational → DyadicDirectLimit) := by
  apply continuous_induced_rng.mpr
  simpa [Function.comp_def] using (continuous_id : Continuous (id : DyadicRational → DyadicRational))

theorem continuous_dyadicDirectLimitValue :
    Continuous dyadicDirectLimitValue := by
  exact continuous_dyadicDirectLimitEquiv

/-! The transported topology makes the concrete quotient readout a genuine
topological equivalence, not merely a pair of one-way continuity lemmas. -/
noncomputable def dyadicDirectLimitHomeomorph :
    DyadicDirectLimit ≃ₜ DyadicRational :=
  { dyadicDirectLimitEquiv with
    continuous_toFun := continuous_dyadicDirectLimitEquiv
    continuous_invFun := continuous_dyadicDirectLimitEquiv_symm }

@[simp] theorem dyadicDirectLimitHomeomorph_apply (x : DyadicDirectLimit) :
    dyadicDirectLimitHomeomorph x = dyadicDirectLimitEquiv x := rfl

@[simp] theorem dyadicDirectLimitHomeomorph_symm_apply (q : DyadicRational) :
    dyadicDirectLimitHomeomorph.symm q = dyadicDirectLimitEquiv.symm q := rfl

end InfoGeometry.Canonical
