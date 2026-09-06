import InfoGeometry.Canonical.DyadicDirectLimitTopologicalGroup

namespace InfoGeometry.Canonical

/-!
# Dyadic scalar action on the concrete direct-limit carrier

The dyadic rationals form a ring under the inherited rational multiplication.
They act on the direct-limit carrier after transport through
`dyadicDirectLimitEquiv`.  This is the correct scalar layer for the current
model; arbitrary rational scalars are intentionally not admitted.
-/

def dyadicScalarMul (a b : DyadicRational) : DyadicRational :=
  ⟨(a : ℚ) * (b : ℚ), by
    rcases a.property with ⟨za, na, hza⟩
    rcases b.property with ⟨zb, nb, hzb⟩
    refine ⟨za * zb, na + nb, ?_⟩
    rw [hza, hzb, pow_add]
    push_cast
    ring⟩

theorem dyadicScalarMul_value (a b : DyadicRational) :
    (dyadicScalarMul a b : ℚ) = (a : ℚ) * (b : ℚ) := rfl

theorem continuous_dyadicScalarMul :
    Continuous (fun p : DyadicRational × DyadicRational =>
      dyadicScalarMul p.1 p.2) := by
  apply continuous_induced_rng.mpr
  simpa [Function.comp_def, dyadicScalarMul_value] using
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))

noncomputable instance : SMul DyadicRational DyadicDirectLimit where
  smul a x :=
    dyadicDirectLimitEquiv.symm
      (dyadicScalarMul a (dyadicDirectLimitEquiv x))

theorem dyadicDirectLimitEquiv_dyadic_smul
    (a : DyadicRational) (x : DyadicDirectLimit) :
    dyadicDirectLimitEquiv (a • x) =
      dyadicScalarMul a (dyadicDirectLimitEquiv x) := by
  change dyadicDirectLimitEquiv
      (dyadicDirectLimitEquiv.symm
        (dyadicScalarMul a (dyadicDirectLimitEquiv x))) = _
  simp

theorem continuous_dyadicDirectLimit_dyadic_smul :
    Continuous
      (fun p : DyadicRational × DyadicDirectLimit => p.1 • p.2) := by
  apply continuous_induced_rng.mpr
  have hpair : Continuous
      (fun p : DyadicRational × DyadicDirectLimit =>
        (p.1, dyadicDirectLimitEquiv p.2)) :=
    by
      exact (continuous_fst :
        Continuous (fun p : DyadicRational × DyadicDirectLimit => p.1)).prodMk
        (continuous_dyadicDirectLimitEquiv.comp continuous_snd)
  have h : Continuous
      (fun p : DyadicRational × DyadicDirectLimit =>
        dyadicScalarMul p.1 (dyadicDirectLimitEquiv p.2)) :=
    by
      simpa [Function.comp_def] using
        continuous_dyadicScalarMul.comp hpair
  convert h using 1
  funext p
  exact dyadicDirectLimitEquiv_dyadic_smul p.1 p.2

instance : ContinuousSMul DyadicRational DyadicDirectLimit where
  continuous_smul := continuous_dyadicDirectLimit_dyadic_smul

end InfoGeometry.Canonical
