import InfoGeometry.Krein.KreinModularSpinorBilinearBridge

namespace InfoGeometry.Krein

namespace KreinCartanOperatorDecomposition

variable (X : InvolutiveSelfDualCarrier)

noncomputable def cartanInvolution (T : X.H →L[ℝ] X.H) : X.H →L[ℝ] X.H :=
  X.ε.comp (T.comp X.ε)

noncomputable def cartanCompactPart (T : X.H →L[ℝ] X.H) : X.H →L[ℝ] X.H :=
  (1 / 2 : ℝ) • (T + cartanInvolution X T)

noncomputable def cartanNoncompactPart (T : X.H →L[ℝ] X.H) : X.H →L[ℝ] X.H :=
  (1 / 2 : ℝ) • (T - cartanInvolution X T)

theorem cartanInvolution_involutive (T : X.H →L[ℝ] X.H) :
    cartanInvolution X (cartanInvolution X T) = T := by
  unfold cartanInvolution
  ext x
  have hε (y : X.H) : X.ε (X.ε y) = y := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun S : X.H →L[ℝ] X.H => S y) X.ε_sq
  change X.ε (X.ε (T (X.ε (X.ε x)))) = T x
  rw [hε x, hε (T x)]

theorem cartanCompactPart_commutes_fundamentalSymmetry
    (T : X.H →L[ℝ] X.H) :
    (cartanCompactPart X T).comp X.ε = X.ε.comp (cartanCompactPart X T) := by
  unfold cartanCompactPart cartanInvolution
  ext x
  have hε (y : X.H) : X.ε (X.ε y) = y := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun S : X.H →L[ℝ] X.H => S y) X.ε_sq
  simp [hε, map_add, map_smul, add_comm, add_left_comm, add_assoc]

theorem cartanNoncompactPart_anticommutes_fundamentalSymmetry
    (T : X.H →L[ℝ] X.H) :
    (cartanNoncompactPart X T).comp X.ε = -(X.ε.comp (cartanNoncompactPart X T)) := by
  unfold cartanNoncompactPart cartanInvolution
  ext x
  have hε (y : X.H) : X.ε (X.ε y) = y := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun S : X.H →L[ℝ] X.H => S y) X.ε_sq
  change (1 / 2 : ℝ) •
      (T (X.ε x) - X.ε (T (X.ε (X.ε x)))) =
    -(X.ε ((1 / 2 : ℝ) • (T x - X.ε (T (X.ε x)))) )
  simp only [map_sub, map_smul, smul_sub]
  rw [hε x, hε (T (X.ε x))]
  simp [hε, map_sub, map_smul, sub_eq_add_neg, smul_add, add_smul,
    add_comm, add_left_comm, add_assoc]

theorem cartan_decomposition (T : X.H →L[ℝ] X.H) :
    cartanCompactPart X T + cartanNoncompactPart X T = T := by
  unfold cartanCompactPart cartanNoncompactPart
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply]
  module

end KreinCartanOperatorDecomposition

end InfoGeometry.Krein
