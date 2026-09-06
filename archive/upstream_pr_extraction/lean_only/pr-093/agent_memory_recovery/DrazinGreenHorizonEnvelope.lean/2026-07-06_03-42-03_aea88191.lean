
/--
If `p_A` and `P_harm` commute, the two-stage envelope equals compression by
the combined matter support `e = p_A * P_harm`.
-/
@[rep_depth operator]
theorem envelope_eq_combined_support_compression
    {Obs : Type*} [Ring Obs] [Star Obs]
    (H : DrazinHorizon Obs)
    (G : DrazinGreenData Obs)
    (x : Obs)
    (hComm : H.p * G.P_harm = G.P_harm * H.p) :
    horizonHarmonicEnvelope H G x =
      matterSupport H G * x * matterSupport H G := by
  unfold horizonHarmonicEnvelope matterSupport
  calc
    G.P_harm * (H.p * x * H.p) * G.P_harm
        = (G.P_harm * H.p) * x * (H.p * G.P_harm) := by
            simp only [mul_assoc]
    _ = (H.p * G.P_harm) * x * (H.p * G.P_harm) := by
            rw [← hComm]

/--
Convert `DrazinGreenData` into the frequency socket used by horizon zitter
modes.
-/
@[rep_depth operator]
def toDrazinFrequencyData
    {Obs : Type*} [Ring Obs] [Star Obs]
    (G : DrazinGreenData Obs) :
    DrazinFrequencyData Obs where
  L := G.L
  LD := G.LD
  harmonicProj := G.P_harm
  index := G.index
  drazin_True := G.drazin_True
  harmonicProj_def := by
    rw [G.P_harm_def, G.P_reg_def]
  harmonic_self_adjoint := G.P_harm_self_adjoint

end InfoGeometry.Canonical.DrazinGreenHorizonEnvelope
