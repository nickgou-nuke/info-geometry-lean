import Mathlib.Tactic
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Lie.SplitOctonionCircularWittForm

noncomputable section

namespace InfoGeometry.Canonical.ThermofieldWittSoldering

open InfoGeometry.Krein
open InfoGeometry.Lie.SplitOctonionCircularWittForm

abbrev V4 := Fin 4 → ℝ
abbrev WittCoord := Fin 8 → ℝ

/-- Minkowski bilinear pairing on the four-dimensional diagonal slice. -/
def minkowskiPair (x y : V4) : ℝ :=
  x 0 * y 0 - (x 1 * y 1 + x 2 * y 2 + x 3 * y 3)

/--
Finite soldering map from the canonical doubled real four-vector carrier into
its split-octonion circular Witt frame.

The forward branch is placed in the positive totally-isotropic four-plane and
the backward branch in the negative totally-isotropic four-plane.
-/
noncomputable def wittSoldering :
    DoubledSpace V4 →ₗ[ℝ] WittCoord where
  toFun u :=
    positiveCircularEmbedding (WithLp.fst u) +
      negativeCircularEmbedding (WithLp.snd u)
  map_add' u v := by
    ext i
    fin_cases i <;>
      simp [positiveCircularEmbedding, negativeCircularEmbedding,
        WithLp.add_fst, WithLp.add_snd]
  map_smul' c u := by
    ext i
    fin_cases i <;>
      simp [positiveCircularEmbedding, negativeCircularEmbedding,
        WithLp.smul_fst, WithLp.smul_snd, smul_eq_mul]

@[simp]
theorem wittSoldering_to_doubled (x ξ : V4) :
    wittSoldering (to_doubled x ξ : DoubledSpace V4) =
      positiveCircularEmbedding x + negativeCircularEmbedding ξ := by
  rfl

/-- Witt grading: `+1` on the forward isotropic plane and `-1` on the backward one. -/
noncomputable def wittGrade : WittCoord →ₗ[ℝ] WittCoord where
  toFun z i := if h : i.val < 4 then z i else -z i
  map_add' x y := by
    funext i
    by_cases h : i.val < 4 <;> simp [h]
  map_smul' c x := by
    funext i
    by_cases h : i.val < 4 <;> simp [h, smul_eq_mul]

/-- Exchange of the two maximally isotropic Witt sectors. -/
noncomputable def wittSwap : WittCoord →ₗ[ℝ] WittCoord where
  toFun z i :=
    if h : i.val < 4 then
      z ⟨i.val + 4, by omega⟩
    else
      z ⟨i.val - 4, by omega⟩
  map_add' x y := by
    funext i
    by_cases h : i.val < 4 <;> simp [h]
  map_smul' c x := by
    funext i
    by_cases h : i.val < 4 <;> simp [h, smul_eq_mul]

@[simp]
theorem wittGrade_sq :
    wittGrade.comp wittGrade = LinearMap.id := by
  ext z i
  fin_cases i <;> simp [wittGrade]

@[simp]
theorem wittSwap_sq :
    wittSwap.comp wittSwap = LinearMap.id := by
  ext z i
  fin_cases i <;> simp [wittSwap]

/-- The target Witt grading is the soldered image of the doubled Krein grading. -/
theorem wittSoldering_intertwines_spectral_epsilon
    (u : DoubledSpace V4) :
    wittSoldering (spectral_epsilon u) =
      wittGrade (wittSoldering u) := by
  ext i
  fin_cases i <;>
    simp [wittSoldering, wittGrade, spectral_epsilon,
      positiveCircularEmbedding, negativeCircularEmbedding]

/-- The target Witt-sector exchange is the soldered image of the modular swap. -/
theorem wittSoldering_intertwines_modular_j
    (u : DoubledSpace V4) :
    wittSoldering (modular_j u) =
      wittSwap (wittSoldering u) := by
  ext i
  fin_cases i <;>
    simp [wittSoldering, wittSwap, modular_j,
      positiveCircularEmbedding, negativeCircularEmbedding]

/-- The finite soldering map loses no doubled degrees of freedom. -/
theorem wittSoldering_injective :
    Function.Injective wittSoldering := by
  intro u v h
  apply DoubledSpace.ext
  · funext i
    have hi := congrFun h (Fin.castAdd 4 i)
    simpa [wittSoldering, positiveCircularEmbedding,
      negativeCircularEmbedding] using hi
  · funext i
    have hi := congrFun h (Fin.addNat i 4)
    simpa [wittSoldering, positiveCircularEmbedding,
      negativeCircularEmbedding] using hi

/-- Every circular Witt coordinate vector is soldered from a unique doubled four-vector. -/
theorem wittSoldering_surjective :
    Function.Surjective wittSoldering := by
  intro z
  let x : V4 := fun i => z (Fin.castAdd 4 i)
  let ξ : V4 := fun i => z (Fin.addNat i 4)
  refine ⟨to_doubled x ξ, ?_⟩
  ext i
  fin_cases i <;>
    simp [wittSoldering, x, ξ, positiveCircularEmbedding,
      negativeCircularEmbedding]

/-- The soldering is therefore an honest finite linear equivalence. -/
noncomputable def wittSolderingEquiv :
    DoubledSpace V4 ≃ₗ[ℝ] WittCoord :=
  LinearEquiv.ofBijective wittSoldering
    ⟨wittSoldering_injective, wittSoldering_surjective⟩

/-- A pure forward state lands in a totally isotropic Witt plane. -/
theorem forward_soldered_isotropic (x y : V4) :
    circularPeircePolar
        (wittSoldering (to_doubled x 0 : DoubledSpace V4))
        (wittSoldering (to_doubled y 0 : DoubledSpace V4)) = 0 := by
  rw [wittSoldering_to_doubled, wittSoldering_to_doubled]
  simp
  exact positive_isTotallyIsotropic
    (by simp [positiveCircularSubmodule, positiveCircularEmbedding])
    (by simp [positiveCircularSubmodule, positiveCircularEmbedding])

/-- A pure backward state lands in the complementary totally isotropic Witt plane. -/
theorem backward_soldered_isotropic (ξ η : V4) :
    circularPeircePolar
        (wittSoldering (to_doubled 0 ξ : DoubledSpace V4))
        (wittSoldering (to_doubled 0 η : DoubledSpace V4)) = 0 := by
  rw [wittSoldering_to_doubled, wittSoldering_to_doubled]
  simp
  exact negative_isTotallyIsotropic
    (by simp [negativeCircularSubmodule, negativeCircularEmbedding])
    (by simp [negativeCircularSubmodule, negativeCircularEmbedding])

/--
The pullback of the split `(4,4)` polar form is exactly the symmetric
forward/backward cross-pairing.
-/
theorem circularPeircePolar_wittSoldering
    (x ξ y η : V4) :
    circularPeircePolar
        (wittSoldering (to_doubled x ξ : DoubledSpace V4))
        (wittSoldering (to_doubled y η : DoubledSpace V4)) =
      minkowskiPair x η + minkowskiPair y ξ := by
  simp [wittSoldering, circularPeircePolar, minkowskiPair,
    positiveCircularEmbedding, negativeCircularEmbedding]
  ring

/-- On the diagonal doubled slice the Witt metric is twice the Minkowski form. -/
theorem diagonal_soldering_metric (x y : V4) :
    circularPeircePolar
        (wittSoldering (to_doubled x x : DoubledSpace V4))
        (wittSoldering (to_doubled y y : DoubledSpace V4)) =
      2 * minkowskiPair x y := by
  rw [circularPeircePolar_wittSoldering]
  simp [minkowskiPair]
  ring

/-- Reciprocal forward/backward thermal dilation on the doubled carrier. -/
noncomputable def thermalDilation (r : ℝ) :
    DoubledSpace V4 →ₗ[ℝ] DoubledSpace V4 where
  toFun u :=
    to_doubled
      (Real.exp r • WithLp.fst u)
      (Real.exp (-r) • WithLp.snd u)
  map_add' u v := by
    apply DoubledSpace.ext <;>
      simp [WithLp.add_fst, WithLp.add_snd, smul_add]
  map_smul' c u := by
    apply DoubledSpace.ext <;>
      simp [WithLp.smul_fst, WithLp.smul_snd, smul_smul]

/-- The same reciprocal dilation expressed directly in Witt coordinates. -/
noncomputable def wittThermalDilation (r : ℝ) :
    WittCoord →ₗ[ℝ] WittCoord where
  toFun z i :=
    if h : i.val < 4 then Real.exp r * z i else Real.exp (-r) * z i
  map_add' x y := by
    funext i
    by_cases h : i.val < 4 <;> simp [h, mul_add]
  map_smul' c x := by
    funext i
    by_cases h : i.val < 4 <;> simp [h, smul_eq_mul]
    all_goals ring

/-- Thermal forward/backward dilation commutes exactly with the soldering map. -/
theorem wittSoldering_intertwines_thermalDilation
    (r : ℝ) (u : DoubledSpace V4) :
    wittSoldering (thermalDilation r u) =
      wittThermalDilation r (wittSoldering u) := by
  ext i
  fin_cases i <;>
    simp [wittSoldering, thermalDilation, wittThermalDilation,
      positiveCircularEmbedding, negativeCircularEmbedding, smul_eq_mul]

end InfoGeometry.Canonical.ThermofieldWittSoldering
