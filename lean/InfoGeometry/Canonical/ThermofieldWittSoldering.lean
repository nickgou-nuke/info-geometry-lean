import Mathlib.Tactic
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Lie.SplitOctonionCircularWittForm

noncomputable section

namespace InfoGeometry.Canonical.ThermofieldWittSoldering

open InfoGeometry.Krein
open InfoGeometry.Lie.SplitOctonionCircularWittForm

abbrev V4 := EuclideanSpace ℝ (Fin 4)
abbrev WittCoord := Fin 8 → ℝ

/-- Minkowski bilinear pairing on the four-dimensional diagonal slice. -/
def minkowskiPair (x y : V4) : ℝ :=
  x 0 * y 0 - (x 1 * y 1 + x 2 * y 2 + x 3 * y 3)

/--
Finite soldering map from the canonical doubled real four-vector carrier into
its split-octonion circular Witt frame.
-/
noncomputable def wittSoldering :
    DoubledSpace V4 →ₗ[ℝ] WittCoord where
  toFun u i :=
    if h : i.val < 4 then
      (WithLp.fst u) ⟨i.val, h⟩
    else
      (WithLp.snd u) ⟨i.val - 4, by omega⟩
  map_add' u v := by
    ext i
    by_cases h : i.val < 4 <;> simp [h]
  map_smul' c u := by
    ext i
    by_cases h : i.val < 4 <;> simp [h]

@[simp]
theorem wittSoldering_to_doubled_apply (x ξ : V4) (i : Fin 8) :
    wittSoldering (to_doubled x ξ : DoubledSpace V4) i =
      if h : i.val < 4 then x ⟨i.val, h⟩ else ξ ⟨i.val - 4, by omega⟩ := by
  rfl

/-- Witt grading: `+1` on the forward isotropic plane and `-1` on the backward one. -/
noncomputable def wittGrade : WittCoord →ₗ[ℝ] WittCoord where
  toFun z i := if h : i.val < 4 then z i else -z i
  map_add' x y := by
    funext i
    by_cases h : i.val < 4
    · simp [h]
    · simp [h, add_comm]
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
  fin_cases i <;> rfl

/-- The target Witt-sector exchange is the soldered image of the modular swap. -/
theorem wittSoldering_intertwines_modular_j
    (u : DoubledSpace V4) :
    wittSoldering (modular_j u) =
      wittSwap (wittSoldering u) := by
  ext i
  fin_cases i <;> rfl

/-- The finite soldering map loses no doubled degrees of freedom. -/
theorem wittSoldering_injective :
    Function.Injective wittSoldering := by
  intro u v h
  apply DoubledSpace.ext
  · ext i
    have hi := congr_fun h ⟨i.val, by omega⟩
    simpa [wittSoldering, i.isLt] using hi
  · ext i
    have hi := congr_fun h ⟨i.val + 4, by omega⟩
    simpa [wittSoldering, show ¬(i.val + 4 < 4) by omega] using hi

/-- Every circular Witt coordinate vector is soldered from a unique doubled four-vector. -/
theorem wittSoldering_surjective :
    Function.Surjective wittSoldering := by
  intro z
  let x : V4 := WithLp.toLp 2 (fun (i : Fin 4) => z ⟨i.val, by omega⟩)
  let ξ : V4 := WithLp.toLp 2 (fun (i : Fin 4) => z ⟨i.val + 4, by omega⟩)
  refine ⟨to_doubled x ξ, ?_⟩
  ext i
  fin_cases i <;> rfl

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
  simp [circularPeircePolar, wittSoldering]

/-- A pure backward state lands in the complementary totally isotropic Witt plane. -/
theorem backward_soldered_isotropic (ξ η : V4) :
    circularPeircePolar
        (wittSoldering (to_doubled 0 ξ : DoubledSpace V4))
        (wittSoldering (to_doubled 0 η : DoubledSpace V4)) = 0 := by
  simp [circularPeircePolar, wittSoldering]

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
  simp [wittSoldering, circularPeircePolar, minkowskiPair]
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
    apply DoubledSpace.ext
    · simp only [WithLp.smul_fst, fst_to_doubled, smul_smul, RingHom.id_apply]
      rw [mul_comm]
    · simp only [WithLp.smul_snd, snd_to_doubled, smul_smul, RingHom.id_apply]
      rw [mul_comm]

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
  fin_cases i <;> rfl

/-- Reciprocal thermal dilation preserves the split `(4,4)` Witt polar form. -/
theorem wittThermalDilation_isometry
    (r : ℝ) (z w : WittCoord) :
    circularPeircePolar (wittThermalDilation r z)
        (wittThermalDilation r w) = circularPeircePolar z w := by
  have hcancel : Real.exp r * Real.exp (-r) = 1 := by
    rw [← Real.exp_add]
    simp
  simp [circularPeircePolar, wittThermalDilation]
  linear_combination
    (z 0 * w 4 + w 0 * z 4 - z 1 * w 5 - w 1 * z 5 - z 2 * w 6 - w 2 * z 6 - z 3 * w 7 - w 3 * z 7) * hcancel

/-- The doubled thermal squeeze preserves the pulled-back Witt metric. -/
theorem thermalDilation_soldered_isometry
    (r : ℝ) (u v : DoubledSpace V4) :
    circularPeircePolar (wittSoldering (thermalDilation r u))
        (wittSoldering (thermalDilation r v)) =
      circularPeircePolar (wittSoldering u) (wittSoldering v) := by
  rw [wittSoldering_intertwines_thermalDilation,
    wittSoldering_intertwines_thermalDilation]
  exact wittThermalDilation_isometry r (wittSoldering u) (wittSoldering v)

end InfoGeometry.Canonical.ThermofieldWittSoldering
