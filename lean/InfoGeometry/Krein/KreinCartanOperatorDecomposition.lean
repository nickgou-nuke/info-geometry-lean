import InfoGeometry.Krein.KreinModularSpinorBilinearBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Krein

namespace KreinCartanOperatorDecomposition

variable (X : InvolutiveSelfDualCarrier)

noncomputable def cartanInvolution (T : X.H →L[ℝ] X.H) : X.H →L[ℝ] X.H :=
  X.ε.comp (T.comp X.ε)

noncomputable def cartanCompactPart (T : X.H →L[ℝ] X.H) : X.H →L[ℝ] X.H :=
  (1 / 2 : ℝ) • (T + cartanInvolution X T)

noncomputable def cartanNoncompactPart (T : X.H →L[ℝ] X.H) : X.H →L[ℝ] X.H :=
  (1 / 2 : ℝ) • (T - cartanInvolution X T)

theorem cartanInvolution_add (T S : X.H →L[ℝ] X.H) :
    cartanInvolution X (T + S) =
      cartanInvolution X T + cartanInvolution X S := by
  unfold cartanInvolution
  ext x
  simp [ContinuousLinearMap.comp_apply, add_comm, add_left_comm, add_assoc]

theorem cartanInvolution_smul (a : ℝ) (T : X.H →L[ℝ] X.H) :
    cartanInvolution X (a • T) = a • cartanInvolution X T := by
  unfold cartanInvolution
  ext x
  simp [ContinuousLinearMap.comp_apply]

theorem cartanInvolution_neg (T : X.H →L[ℝ] X.H) :
    cartanInvolution X (-T) = -cartanInvolution X T := by
  unfold cartanInvolution
  ext x
  simp [ContinuousLinearMap.comp_apply]

theorem cartanInvolution_sub (T S : X.H →L[ℝ] X.H) :
    cartanInvolution X (T - S) =
      cartanInvolution X T - cartanInvolution X S := by
  rw [sub_eq_add_neg, sub_eq_add_neg, cartanInvolution_add]
  rw [cartanInvolution_neg]

theorem cartanCompactPart_add (T S : X.H →L[ℝ] X.H) :
    cartanCompactPart X (T + S) =
      cartanCompactPart X T + cartanCompactPart X S := by
  unfold cartanCompactPart
  rw [cartanInvolution_add]
  module

theorem cartanNoncompactPart_add (T S : X.H →L[ℝ] X.H) :
    cartanNoncompactPart X (T + S) =
      cartanNoncompactPart X T + cartanNoncompactPart X S := by
  unfold cartanNoncompactPart
  rw [cartanInvolution_add]
  module

theorem cartanCompactPart_smul (a : ℝ) (T : X.H →L[ℝ] X.H) :
    cartanCompactPart X (a • T) = a • cartanCompactPart X T := by
  unfold cartanCompactPart
  rw [cartanInvolution_smul]
  module

theorem cartanNoncompactPart_smul (a : ℝ) (T : X.H →L[ℝ] X.H) :
    cartanNoncompactPart X (a • T) = a • cartanNoncompactPart X T := by
  unfold cartanNoncompactPart
  rw [cartanInvolution_smul]
  module

theorem cartanInvolution_involutive (T : X.H →L[ℝ] X.H) :
    cartanInvolution X (cartanInvolution X T) = T := by
  unfold cartanInvolution
  ext x
  have hε (y : X.H) : X.ε (X.ε y) = y := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun S : X.H →L[ℝ] X.H => S y) X.ε_sq
  change X.ε (X.ε (T (X.ε (X.ε x)))) = T x
  rw [hε x, hε (T x)]

theorem cartanInvolution_comp (T S : X.H →L[ℝ] X.H) :
    cartanInvolution X (T.comp S) =
      (cartanInvolution X T).comp (cartanInvolution X S) := by
  unfold cartanInvolution
  ext x
  have hε (y : X.H) : X.ε (X.ε y) = y := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun R : X.H →L[ℝ] X.H => R y) X.ε_sq
  simp [ContinuousLinearMap.comp_apply, hε]

theorem cartanInvolution_lie (T S : X.H →L[ℝ] X.H) :
    cartanInvolution X ⁅T, S⁆ =
      ⁅cartanInvolution X T, cartanInvolution X S⁆ := by
  have hmul : ∀ A B : X.H →L[ℝ] X.H,
      cartanInvolution X (A * B) =
        cartanInvolution X A * cartanInvolution X B := by
    intro A B
    exact cartanInvolution_comp X A B
  simp only [Ring.lie_def, cartanInvolution_sub, hmul]

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

/-- The compact Cartan component is an idempotent projection on operators. -/
theorem cartanCompactPart_idempotent (T : X.H →L[ℝ] X.H) :
    cartanCompactPart X (cartanCompactPart X T) = cartanCompactPart X T := by
  unfold cartanCompactPart cartanInvolution
  ext x
  have hε (y : X.H) : X.ε (X.ε y) = y := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun S : X.H →L[ℝ] X.H => S y) X.ε_sq
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, map_add, map_smul]
  rw [hε x, hε (T x)]
  module

/-- The noncompact Cartan component is an idempotent projection on operators. -/
theorem cartanNoncompactPart_idempotent (T : X.H →L[ℝ] X.H) :
    cartanNoncompactPart X (cartanNoncompactPart X T) =
      cartanNoncompactPart X T := by
  unfold cartanNoncompactPart cartanInvolution
  ext x
  have hε (y : X.H) : X.ε (X.ε y) = y := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun S : X.H →L[ℝ] X.H => S y) X.ε_sq
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, map_sub, map_smul]
  rw [hε x, hε (T x)]
  module

/-- The compact projection is the `+1` eigenspace of the Cartan involution. -/
theorem cartanInvolution_cartanCompactPart (T : X.H →L[ℝ] X.H) :
    cartanInvolution X (cartanCompactPart X T) = cartanCompactPart X T := by
  unfold cartanCompactPart cartanInvolution
  ext x
  have hε (y : X.H) : X.ε (X.ε y) = y := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun S : X.H →L[ℝ] X.H => S y) X.ε_sq
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, map_add, map_smul]
  rw [hε x, hε (T x)]
  module

/-- The noncompact projection is the `-1` eigenspace of the Cartan involution. -/
theorem cartanInvolution_cartanNoncompactPart (T : X.H →L[ℝ] X.H) :
    cartanInvolution X (cartanNoncompactPart X T) =
      -(cartanNoncompactPart X T) := by
  unfold cartanInvolution
  ext x
  have hε (y : X.H) : X.ε (X.ε y) = y := by
    simpa [ContinuousLinearMap.comp_apply]
      using congrArg (fun S : X.H →L[ℝ] X.H => S y) X.ε_sq
  have hanti := congrArg
    (fun S : X.H →L[ℝ] X.H => S x)
    (cartanNoncompactPart_anticommutes_fundamentalSymmetry X T)
  change X.ε ((cartanNoncompactPart X T) (X.ε x)) =
    -(cartanNoncompactPart X T) x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply] at hanti
  rw [hanti]
  simp [hε]

/-- The compact projection vanishes exactly on the `-1` eigenspace. -/
theorem cartanCompactPart_eq_zero_iff (T : X.H →L[ℝ] X.H) :
    cartanCompactPart X T = 0 ↔ cartanInvolution X T = -T := by
  constructor
  · intro h
    unfold cartanCompactPart at h
    have hsum : T + cartanInvolution X T = 0 := by
      exact (smul_eq_zero.mp h).resolve_left (by norm_num)
    simpa using (eq_neg_of_add_eq_zero_right hsum)
  · intro h
    unfold cartanCompactPart
    rw [h]
    module

/-- The noncompact projection vanishes exactly on the `+1` eigenspace. -/
theorem cartanNoncompactPart_eq_zero_iff (T : X.H →L[ℝ] X.H) :
    cartanNoncompactPart X T = 0 ↔ cartanInvolution X T = T := by
  constructor
  · intro h
    unfold cartanNoncompactPart at h
    have hsub : T - cartanInvolution X T = 0 := by
      exact (smul_eq_zero.mp h).resolve_left (by norm_num)
    exact (sub_eq_zero.mp hsub).symm
  · intro h
    unfold cartanNoncompactPart
    rw [h]
    module

theorem cartanCompactPart_cartanNoncompactPart (T : X.H →L[ℝ] X.H) :
    cartanCompactPart X (cartanNoncompactPart X T) = 0 := by
  apply (cartanCompactPart_eq_zero_iff X (cartanNoncompactPart X T)).2
  exact cartanInvolution_cartanNoncompactPart X T

theorem cartanNoncompactPart_cartanCompactPart (T : X.H →L[ℝ] X.H) :
    cartanNoncompactPart X (cartanCompactPart X T) = 0 := by
  apply (cartanNoncompactPart_eq_zero_iff X (cartanCompactPart X T)).2
  exact cartanInvolution_cartanCompactPart X T

theorem cartanCompactPart_eq_of_involution_eq
    (T : X.H →L[ℝ] X.H)
    (hT : cartanInvolution X T = T) :
    cartanCompactPart X T = T := by
  unfold cartanCompactPart
  rw [hT]
  module

theorem cartanNoncompactPart_eq_of_involution_neg
    (T : X.H →L[ℝ] X.H)
    (hT : cartanInvolution X T = -T) :
    cartanNoncompactPart X T = T := by
  unfold cartanNoncompactPart
  rw [hT]
  module

theorem cartanCompactPart_lie_compact (T S : X.H →L[ℝ] X.H) :
    cartanCompactPart X
        ⁅cartanCompactPart X T, cartanCompactPart X S⁆ =
      ⁅cartanCompactPart X T, cartanCompactPart X S⁆ := by
  apply cartanCompactPart_eq_of_involution_eq
  rw [cartanInvolution_lie,
    cartanInvolution_cartanCompactPart,
    cartanInvolution_cartanCompactPart]

theorem cartanCompactPart_lie_noncompact (T S : X.H →L[ℝ] X.H) :
    cartanCompactPart X
        ⁅cartanNoncompactPart X T, cartanNoncompactPart X S⁆ =
      ⁅cartanNoncompactPart X T, cartanNoncompactPart X S⁆ := by
  apply cartanCompactPart_eq_of_involution_eq
  rw [cartanInvolution_lie,
    cartanInvolution_cartanNoncompactPart,
    cartanInvolution_cartanNoncompactPart]
  simp [Ring.lie_def]

theorem cartanNoncompactPart_lie_mixed (T S : X.H →L[ℝ] X.H) :
    cartanNoncompactPart X
        ⁅cartanCompactPart X T, cartanNoncompactPart X S⁆ =
      ⁅cartanCompactPart X T, cartanNoncompactPart X S⁆ := by
  apply cartanNoncompactPart_eq_of_involution_neg
  rw [cartanInvolution_lie,
    cartanInvolution_cartanCompactPart,
    cartanInvolution_cartanNoncompactPart]
  simp [Ring.lie_def]
  abel

theorem cartanNoncompactPart_lie_mixed_right (T S : X.H →L[ℝ] X.H) :
    cartanNoncompactPart X
        ⁅cartanNoncompactPart X T, cartanCompactPart X S⁆ =
      ⁅cartanNoncompactPart X T, cartanCompactPart X S⁆ := by
  apply cartanNoncompactPart_eq_of_involution_neg
  rw [cartanInvolution_lie,
    cartanInvolution_cartanNoncompactPart,
    cartanInvolution_cartanCompactPart]
  simp [Ring.lie_def]
  abel

theorem cartan_decomposition_unique
    (T K P : X.H →L[ℝ] X.H)
    (hK : cartanInvolution X K = K)
    (hP : cartanInvolution X P = -P)
    (hKP : K + P = T) :
    K = cartanCompactPart X T ∧ P = cartanNoncompactPart X T := by
  have hθKP : cartanInvolution X (K + P) = K - P := by
    have hθadd : cartanInvolution X (K + P) =
        cartanInvolution X K + cartanInvolution X P := by
      exact cartanInvolution_add X K P
    rw [hθadd, hK, hP]
    simp [sub_eq_add_neg]
  constructor
  · unfold cartanCompactPart
    rw [← hKP, hθKP]
    module
  · unfold cartanNoncompactPart
    rw [← hKP, hθKP]
    module

theorem cartan_decomposition (T : X.H →L[ℝ] X.H) :
    cartanCompactPart X T + cartanNoncompactPart X T = T := by
  unfold cartanCompactPart cartanNoncompactPart
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply]
  module

end KreinCartanOperatorDecomposition

end InfoGeometry.Krein
