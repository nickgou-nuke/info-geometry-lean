import InfoGeometry.Canonical.BogoliubovProjectorTransport

namespace InfoGeometry.Canonical.BogoliubovProjectorFlux

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovClosedForms
open InfoGeometry.Canonical.BogoliubovProjectorTransport
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Krein

section Basic

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "P₊" => spectralPlusProj (E := E)
local notation "P₋" => spectralMinusProj (E := E)
local notation "J" => modularConjugationJ (E := E)
local notation "K" => InfoGeometry.Krein.clockAxis (E := E)

/-- The transported positive grading projector under an operator-valued transport. -/
noncomputable def transportedPlusProjector (T : EndH) : EndH :=
  P₊.comp T

/-- The transported negative grading projector under an operator-valued transport. -/
noncomputable def transportedMinusProjector (T : EndH) : EndH :=
  P₋.comp T

/-- The positive projector exchange/flux induced by a transport operator. -/
noncomputable def plusProjectorFlux (T : EndH) : EndH :=
  P₊.comp T - T.comp P₊

/-- The negative projector exchange/flux induced by a transport operator. -/
noncomputable def minusProjectorFlux (T : EndH) : EndH :=
  P₋.comp T - T.comp P₋

/-- Right-composition action of the `ε`-boost on the positive projector block. -/
theorem epsilonBoost_comp_spectralPlusProj
    (t : ℝ) :
    (epsilonBoost (E := E) t).comp P₊ = Real.exp t • P₊ := by
  rw [epsilonBoost_eq_cosh_add_sinh_eps (E := E) t]
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp,
    eps_comp_spectralPlusProj (E := E)]
  have hcomp1 : (1 : EndH).comp P₊ = P₊ := by
    change (ContinuousLinearMap.id ℝ H₂).comp P₊ = P₊
    exact ContinuousLinearMap.id_comp P₊
  rw [hcomp1]
  calc
    Real.cosh t • P₊ + Real.sinh t • P₊
      = (Real.cosh t + Real.sinh t) • P₊ := by
          simpa using (add_smul (Real.cosh t) (Real.sinh t) P₊).symm
    _ = Real.exp t • P₊ := by
          rw [Real.cosh_add_sinh]

/-- Right-composition action of the `ε`-boost on the negative projector block. -/
theorem epsilonBoost_comp_spectralMinusProj
    (t : ℝ) :
    (epsilonBoost (E := E) t).comp P₋ = Real.exp (-t) • P₋ := by
  rw [epsilonBoost_eq_cosh_add_sinh_eps (E := E) t]
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp,
    eps_comp_spectralMinusProj (E := E)]
  have hcomp1 : (1 : EndH).comp P₋ = P₋ := by
    change (ContinuousLinearMap.id ℝ H₂).comp P₋ = P₋
    exact ContinuousLinearMap.id_comp P₋
  rw [hcomp1, smul_neg]
  calc
    Real.cosh t • P₋ + -(Real.sinh t • P₋)
      = (Real.cosh t - Real.sinh t) • P₋ := by
          simpa [sub_eq_add_neg] using
            (sub_smul (Real.cosh t) (Real.sinh t) P₋).symm
    _ = Real.exp (-t) • P₋ := by
          rw [Real.cosh_sub_sinh]

/-- Right-composition action of the `J`-boost on the positive projector block. -/
theorem JBoost_comp_spectralPlusProj
    (t : ℝ) :
    (JBoost (E := E) t).comp P₊
      = Real.cosh t • P₊ + Real.sinh t • (P₋.comp (modularConjugationJ (E := E))) := by
  rw [JBoost_eq_cosh_add_sinh_J (E := E) t]
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp]
  have hcomp1 : (1 : EndH).comp P₊ = P₊ := by
    change (ContinuousLinearMap.id ℝ H₂).comp P₊ = P₊
    exact ContinuousLinearMap.id_comp P₊
  rw [hcomp1, ← spectralMinusProj_comp_modular_j (E := E)]

theorem JBoost_comp_spectralPlusProj_modular_j
    (t : ℝ) :
    (JBoost (E := E) t).comp P₊
      = Real.cosh t • P₊ + Real.sinh t • (P₋.comp (modular_j (E := E))) := by
  simpa [TomitaTakesaki.modularConjugationJ_eq_modular_j] using
    JBoost_comp_spectralPlusProj (E := E) t

/-- Right-composition action of the `J`-boost on the negative projector block. -/
theorem JBoost_comp_spectralMinusProj
    (t : ℝ) :
    (JBoost (E := E) t).comp P₋
      = Real.cosh t • P₋ + Real.sinh t • (P₊.comp (modularConjugationJ (E := E))) := by
  rw [JBoost_eq_cosh_add_sinh_J (E := E) t]
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp]
  have hcomp1 : (1 : EndH).comp P₋ = P₋ := by
    change (ContinuousLinearMap.id ℝ H₂).comp P₋ = P₋
    exact ContinuousLinearMap.id_comp P₋
  rw [hcomp1, ← spectralPlusProj_comp_modular_j (E := E)]

theorem JBoost_comp_spectralMinusProj_modular_j
    (t : ℝ) :
    (JBoost (E := E) t).comp P₋
      = Real.cosh t • P₋ + Real.sinh t • (P₊.comp (modular_j (E := E))) := by
  simpa [TomitaTakesaki.modularConjugationJ_eq_modular_j] using
    JBoost_comp_spectralMinusProj (E := E) t

/-- Right-composition action of the `K`-rotation on the positive projector block. -/
theorem KRotation_comp_spectralPlusProj
    (t : ℝ) :
    (KRotation (E := E) t).comp P₊
      = Real.cos t • P₊ + Real.sin t • (P₋.comp (InfoGeometry.Krein.clockAxis (E := E))) := by
  rw [KRotation_eq_cos_add_sin_K (E := E) t]
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp]
  have hcomp1 : (1 : EndH).comp P₊ = P₊ := by
    change (ContinuousLinearMap.id ℝ H₂).comp P₊ = P₊
    exact ContinuousLinearMap.id_comp P₊
  rw [hcomp1, ← spectralMinusProj_comp_K (E := E)]

theorem KRotation_comp_spectralPlusProj_complex_i
    (t : ℝ) :
    (KRotation (E := E) t).comp P₊
      = Real.cos t • P₊ + Real.sin t • (P₋.comp (complex_i (E := E))) := by
  simpa [InfoGeometry.Krein.clockAxis_eq_complex_i] using
    KRotation_comp_spectralPlusProj (E := E) t

/-- Right-composition action of the `K`-rotation on the negative projector block. -/
theorem KRotation_comp_spectralMinusProj
    (t : ℝ) :
    (KRotation (E := E) t).comp P₋
      = Real.cos t • P₋ + Real.sin t • (P₊.comp (InfoGeometry.Krein.clockAxis (E := E))) := by
  rw [KRotation_eq_cos_add_sin_K (E := E) t]
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_comp]
  have hcomp1 : (1 : EndH).comp P₋ = P₋ := by
    change (ContinuousLinearMap.id ℝ H₂).comp P₋ = P₋
    exact ContinuousLinearMap.id_comp P₋
  rw [hcomp1, ← spectralPlusProj_comp_K (E := E)]

theorem KRotation_comp_spectralMinusProj_complex_i
    (t : ℝ) :
    (KRotation (E := E) t).comp P₋
      = Real.cos t • P₋ + Real.sin t • (P₊.comp (complex_i (E := E))) := by
  simpa [InfoGeometry.Krein.clockAxis_eq_complex_i] using
    KRotation_comp_spectralMinusProj (E := E) t

@[simp] theorem transportedPlusProjector_epsilonBoost
    (t : ℝ) :
    transportedPlusProjector (E := E) (epsilonBoost (E := E) t)
      = Real.exp t • P₊ := by
  simpa [transportedPlusProjector] using spectralPlusProj_comp_epsilonBoost (E := E) t

@[simp] theorem transportedMinusProjector_epsilonBoost
    (t : ℝ) :
    transportedMinusProjector (E := E) (epsilonBoost (E := E) t)
      = Real.exp (-t) • P₋ := by
  simpa [transportedMinusProjector] using spectralMinusProj_comp_epsilonBoost (E := E) t

@[simp] theorem transportedPlusProjector_JBoost
    (t : ℝ) :
    transportedPlusProjector (E := E) (JBoost (E := E) t)
      = Real.cosh t • P₊ + Real.sinh t • ((modularConjugationJ (E := E)).comp P₋) := by
  simpa [transportedPlusProjector] using spectralPlusProj_comp_JBoost (E := E) t

@[simp] theorem transportedPlusProjector_JBoost_modular_j
    (t : ℝ) :
    transportedPlusProjector (E := E) (JBoost (E := E) t)
      = Real.cosh t • P₊ + Real.sinh t • ((modular_j (E := E)).comp P₋) := by
  rw [transportedPlusProjector_JBoost (E := E) t]

@[simp] theorem transportedMinusProjector_JBoost
    (t : ℝ) :
    transportedMinusProjector (E := E) (JBoost (E := E) t)
      = Real.cosh t • P₋ + Real.sinh t • ((modularConjugationJ (E := E)).comp P₊) := by
  simpa [transportedMinusProjector] using spectralMinusProj_comp_JBoost (E := E) t

@[simp] theorem transportedMinusProjector_JBoost_modular_j
    (t : ℝ) :
    transportedMinusProjector (E := E) (JBoost (E := E) t)
      = Real.cosh t • P₋ + Real.sinh t • ((modular_j (E := E)).comp P₊) := by
  rw [transportedMinusProjector_JBoost (E := E) t]

@[simp] theorem transportedPlusProjector_KRotation
    (t : ℝ) :
    transportedPlusProjector (E := E) (KRotation (E := E) t)
      = Real.cos t • P₊ + Real.sin t • ((InfoGeometry.Krein.clockAxis (E := E)).comp P₋) := by
  simpa [transportedPlusProjector] using spectralPlusProj_comp_KRotation (E := E) t

@[simp] theorem transportedPlusProjector_KRotation_complex_i
    (t : ℝ) :
    transportedPlusProjector (E := E) (KRotation (E := E) t)
      = Real.cos t • P₊ + Real.sin t • ((complex_i (E := E)).comp P₋) := by
  rw [transportedPlusProjector_KRotation (E := E) t]
  simp [InfoGeometry.Krein.clockAxis]

@[simp] theorem transportedMinusProjector_KRotation
    (t : ℝ) :
    transportedMinusProjector (E := E) (KRotation (E := E) t)
      = Real.cos t • P₋ + Real.sin t • ((InfoGeometry.Krein.clockAxis (E := E)).comp P₊) := by
  simpa [transportedMinusProjector] using spectralMinusProj_comp_KRotation (E := E) t

@[simp] theorem transportedMinusProjector_KRotation_complex_i
    (t : ℝ) :
    transportedMinusProjector (E := E) (KRotation (E := E) t)
      = Real.cos t • P₋ + Real.sin t • ((complex_i (E := E)).comp P₊) := by
  rw [transportedMinusProjector_KRotation (E := E) t]
  simp [InfoGeometry.Krein.clockAxis]

/-- The positive projector flux vanishes for the grading-diagonal `ε`-boost. -/
theorem plusProjectorFlux_epsilonBoost
    (t : ℝ) :
    plusProjectorFlux (E := E) (epsilonBoost (E := E) t) = 0 := by
  unfold plusProjectorFlux
  rw [spectralPlusProj_comp_epsilonBoost (E := E) t, epsilonBoost_comp_spectralPlusProj (E := E) t]
  simp

/-- The negative projector flux vanishes for the grading-diagonal `ε`-boost. -/
theorem minusProjectorFlux_epsilonBoost
    (t : ℝ) :
    minusProjectorFlux (E := E) (epsilonBoost (E := E) t) = 0 := by
  unfold minusProjectorFlux
  rw [spectralMinusProj_comp_epsilonBoost (E := E) t,
    epsilonBoost_comp_spectralMinusProj (E := E) t]
  simp

/-- The positive projector flux of the `J`-boost is the hyperbolic off-diagonal block. -/
theorem plusProjectorFlux_JBoost
    (t : ℝ) :
    plusProjectorFlux (E := E) (JBoost (E := E) t)
      = Real.sinh t • (((modularConjugationJ (E := E)).comp P₋) - (P₋.comp (modularConjugationJ (E := E)))) := by
  unfold plusProjectorFlux
  rw [spectralPlusProj_comp_JBoost (E := E) t, JBoost_comp_spectralPlusProj (E := E) t]
  calc
    (Real.cosh t • P₊ + Real.sinh t • ((modularConjugationJ (E := E)).comp P₋)) -
        (Real.cosh t • P₊ + Real.sinh t • (P₋.comp (modularConjugationJ (E := E))))
      = (Real.sinh t • ((modularConjugationJ (E := E)).comp P₋)) - (Real.sinh t • (P₋.comp (modularConjugationJ (E := E)))) := by
          abel
    _ = Real.sinh t • (((modularConjugationJ (E := E)).comp P₋) - (P₋.comp (modularConjugationJ (E := E)))) := by
          rw [smul_sub]

theorem plusProjectorFlux_JBoost_modular_j
    (t : ℝ) :
    plusProjectorFlux (E := E) (JBoost (E := E) t)
      = Real.sinh t • (((modular_j (E := E)).comp P₋) - (P₋.comp (modular_j (E := E)))) := by
  simpa [TomitaTakesaki.modularConjugationJ_eq_modular_j] using
    plusProjectorFlux_JBoost (E := E) t

/-- The negative projector flux of the `J`-boost is the hyperbolic off-diagonal block. -/
theorem minusProjectorFlux_JBoost
    (t : ℝ) :
    minusProjectorFlux (E := E) (JBoost (E := E) t)
      = Real.sinh t • (((modularConjugationJ (E := E)).comp P₊) - (P₊.comp (modularConjugationJ (E := E)))) := by
  unfold minusProjectorFlux
  rw [spectralMinusProj_comp_JBoost (E := E) t, JBoost_comp_spectralMinusProj (E := E) t]
  calc
    (Real.cosh t • P₋ + Real.sinh t • ((modularConjugationJ (E := E)).comp P₊)) -
        (Real.cosh t • P₋ + Real.sinh t • (P₊.comp (modularConjugationJ (E := E))))
      = (Real.sinh t • ((modularConjugationJ (E := E)).comp P₊)) - (Real.sinh t • (P₊.comp (modularConjugationJ (E := E)))) := by
          abel
    _ = Real.sinh t • (((modularConjugationJ (E := E)).comp P₊) - (P₊.comp (modularConjugationJ (E := E)))) := by
          rw [smul_sub]

theorem minusProjectorFlux_JBoost_modular_j
    (t : ℝ) :
    minusProjectorFlux (E := E) (JBoost (E := E) t)
      = Real.sinh t • (((modular_j (E := E)).comp P₊) - (P₊.comp (modular_j (E := E)))) := by
  simpa [TomitaTakesaki.modularConjugationJ_eq_modular_j] using
    minusProjectorFlux_JBoost (E := E) t

/-- The positive projector flux of the `K`-rotation is the oscillatory off-diagonal block. -/
theorem plusProjectorFlux_KRotation
    (t : ℝ) :
    plusProjectorFlux (E := E) (KRotation (E := E) t)
      = Real.sin t • (((InfoGeometry.Krein.clockAxis (E := E)).comp P₋) - (P₋.comp (InfoGeometry.Krein.clockAxis (E := E)))) := by
  unfold plusProjectorFlux
  rw [spectralPlusProj_comp_KRotation (E := E) t, KRotation_comp_spectralPlusProj (E := E) t]
  calc
    (Real.cos t • P₊ + Real.sin t • ((InfoGeometry.Krein.clockAxis (E := E)).comp P₋)) -
        (Real.cos t • P₊ + Real.sin t • (P₋.comp (InfoGeometry.Krein.clockAxis (E := E))))
      = (Real.sin t • ((InfoGeometry.Krein.clockAxis (E := E)).comp P₋)) - (Real.sin t • (P₋.comp (InfoGeometry.Krein.clockAxis (E := E)))) := by
          abel
    _ = Real.sin t • (((InfoGeometry.Krein.clockAxis (E := E)).comp P₋) - (P₋.comp (InfoGeometry.Krein.clockAxis (E := E)))) := by
          rw [smul_sub]

theorem plusProjectorFlux_KRotation_complex_i
    (t : ℝ) :
    plusProjectorFlux (E := E) (KRotation (E := E) t)
      = Real.sin t • (((complex_i (E := E)).comp P₋) - (P₋.comp (complex_i (E := E)))) := by
  simpa [InfoGeometry.Krein.clockAxis_eq_complex_i] using
    plusProjectorFlux_KRotation (E := E) t

/-- The negative projector flux of the `K`-rotation is the oscillatory off-diagonal block. -/
theorem minusProjectorFlux_KRotation
    (t : ℝ) :
    minusProjectorFlux (E := E) (KRotation (E := E) t)
      = Real.sin t • (((InfoGeometry.Krein.clockAxis (E := E)).comp P₊) - (P₊.comp (InfoGeometry.Krein.clockAxis (E := E)))) := by
  unfold minusProjectorFlux
  rw [spectralMinusProj_comp_KRotation (E := E) t, KRotation_comp_spectralMinusProj (E := E) t]
  calc
    (Real.cos t • P₋ + Real.sin t • ((InfoGeometry.Krein.clockAxis (E := E)).comp P₊)) -
        (Real.cos t • P₋ + Real.sin t • (P₊.comp (InfoGeometry.Krein.clockAxis (E := E))))
      = (Real.sin t • ((InfoGeometry.Krein.clockAxis (E := E)).comp P₊)) - (Real.sin t • (P₊.comp (InfoGeometry.Krein.clockAxis (E := E)))) := by
          abel
    _ = Real.sin t • (((InfoGeometry.Krein.clockAxis (E := E)).comp P₊) - (P₊.comp (InfoGeometry.Krein.clockAxis (E := E)))) := by
          rw [smul_sub]

theorem minusProjectorFlux_KRotation_complex_i
    (t : ℝ) :
    minusProjectorFlux (E := E) (KRotation (E := E) t)
      = Real.sin t • (((complex_i (E := E)).comp P₊) - (P₊.comp (complex_i (E := E)))) := by
  simpa [InfoGeometry.Krein.clockAxis_eq_complex_i] using
    minusProjectorFlux_KRotation (E := E) t

end Basic

end InfoGeometry.Canonical.BogoliubovProjectorFlux
