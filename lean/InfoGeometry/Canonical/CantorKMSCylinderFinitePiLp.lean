import Mathlib.Analysis.InnerProductSpace.PiL2
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorKMSCylinderState

noncomputable section

namespace InfoGeometry.Canonical.CantorKMSCylinderState

/-!
# Finite Cantor cylinder stages in native `PiLp`

This file realizes each finite cylinder stage in Mathlib's native `PiLp 2`
carrier.  It does not identify the infinite finitely-supported carrier with
an `lp` completion.
-/

abbrev cylinderKMSFinitePiLp (n : ℕ) : Type :=
  PiLp 2 (fun _ : Fin n → Bool => ℂ)

noncomputable def cylinderKMSFiniteToPiLp (n : ℕ) :
    ((Fin n → Bool) → ℂ) →ₗ[ℂ] cylinderKMSFinitePiLp n where
  toFun f := WithLp.toLp 2 f
  map_add' f g := WithLp.toLp_add 2 f g
  map_smul' c f := WithLp.toLp_smul 2 c f

theorem cylinderKMSFiniteToPiLp_injective (n : ℕ) :
    Function.Injective (cylinderKMSFiniteToPiLp n) := by
  intro f g h
  exact WithLp.toLp_injective 2 h

theorem cylinderKMSFiniteToPiLp_surjective (n : ℕ) :
    Function.Surjective (cylinderKMSFiniteToPiLp n) := by
  intro x
  obtain ⟨f, hf⟩ := WithLp.toLp_surjective (2 : ENNReal) x
  exact ⟨f, hf⟩

noncomputable def cylinderKMSFiniteToPiLpLinearEquiv (n : ℕ) :
    ((Fin n → Bool) → ℂ) ≃ₗ[ℂ] cylinderKMSFinitePiLp n :=
  LinearEquiv.ofBijective (cylinderKMSFiniteToPiLp n)
    ⟨cylinderKMSFiniteToPiLp_injective n,
      cylinderKMSFiniteToPiLp_surjective n⟩

@[simp]
theorem cylinderKMSFiniteToPiLp_apply (n : ℕ)
    (f : (Fin n → Bool) → ℂ) :
    cylinderKMSFiniteToPiLp n f = WithLp.toLp 2 f :=
  rfl

theorem cylinderKMSFiniteToPiLp_norm_sq (n : ℕ)
    (f : (Fin n → Bool) → ℂ) :
    ‖cylinderKMSFiniteToPiLp n f‖ ^ 2 =
      ∑ w : (Fin n → Bool), ‖f w‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [cylinderKMSFiniteToPiLp]

theorem cylinderKMSQuadratic_eq_weighted_PiLp_norm_sq
    (n : ℕ) (f : (Fin n → Bool) → ℂ) :
    cylinderKMSQuadratic n f =
      ((1 / 2 : ℝ) ^ n) *
        ‖cylinderKMSFiniteToPiLp n f‖ ^ 2 := by
  rw [cylinderKMSQuadratic]
  calc
    (∑ w : (Fin n → Bool),
        cylinderKMSWeight (List.ofFn w) * ‖f w‖ ^ 2) =
        ∑ w : (Fin n → Bool),
          ((1 / 2 : ℝ) ^ n) * ‖f w‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [cylinderKMSWeight_ofFn]
    _ = ((1 / 2 : ℝ) ^ n) *
          (∑ w : (Fin n → Bool), ‖f w‖ ^ 2) := by
            rw [Finset.mul_sum]
    _ = ((1 / 2 : ℝ) ^ n) *
          ‖cylinderKMSFiniteToPiLp n f‖ ^ 2 := by
            rw [cylinderKMSFiniteToPiLp_norm_sq]

theorem cylinderKMSQuadratic_pos_of_PiLp_ne_zero
    (n : ℕ) (f : (Fin n → Bool) → ℂ)
    (hf : cylinderKMSFiniteToPiLp n f ≠ 0) :
    0 < cylinderKMSQuadratic n f := by
  rw [cylinderKMSQuadratic_eq_weighted_PiLp_norm_sq]
  exact mul_pos (pow_pos (by norm_num) n)
    (sq_pos_of_pos (norm_pos_iff.mpr hf))

theorem cylinderKMSQuadratic_eq_zero_iff_PiLp_eq_zero
    (n : ℕ) (f : (Fin n → Bool) → ℂ) :
    cylinderKMSQuadratic n f = 0 ↔
      cylinderKMSFiniteToPiLp n f = 0 := by
  constructor
  · intro h
    have hf : f = 0 :=
      (cylinderKMSQuadratic_eq_zero_iff_fun_eq_zero n f).mp h
    rw [hf]
    exact WithLp.toLp_zero 2
  · intro h
    have hf : f = 0 := (cylinderKMSFiniteToPiLp_injective n) h
    subst f
    simp [cylinderKMSQuadratic]

noncomputable def cylinderKMSFiniteWeightSqrt (n : ℕ) : ℝ :=
  Real.sqrt ((1 / 2 : ℝ) ^ n)

theorem cylinderKMSFiniteWeightSqrt_sq (n : ℕ) :
    cylinderKMSFiniteWeightSqrt n ^ 2 = (1 / 2 : ℝ) ^ n := by
  unfold cylinderKMSFiniteWeightSqrt
  exact Real.sq_sqrt (pow_nonneg (by norm_num) n)

noncomputable def cylinderKMSFiniteWeightedToPiLp (n : ℕ) :
    ((Fin n → Bool) → ℂ) →ₗ[ℂ] cylinderKMSFinitePiLp n :=
  (cylinderKMSFiniteWeightSqrt n : ℂ) • cylinderKMSFiniteToPiLp n

theorem cylinderKMSFiniteWeightedToPiLp_injective (n : ℕ) :
    Function.Injective (cylinderKMSFiniteWeightedToPiLp n) := by
  intro f g h
  have hc : (cylinderKMSFiniteWeightSqrt n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ n)))
  change (cylinderKMSFiniteWeightSqrt n : ℂ) •
      cylinderKMSFiniteToPiLp n f =
    (cylinderKMSFiniteWeightSqrt n : ℂ) •
      cylinderKMSFiniteToPiLp n g at h
  have hL : cylinderKMSFiniteToPiLp n f =
      cylinderKMSFiniteToPiLp n g := by
    exact smul_right_injective (cylinderKMSFinitePiLp n) hc h
  exact cylinderKMSFiniteToPiLp_injective n hL

theorem cylinderKMSFiniteWeightedToPiLp_surjective (n : ℕ) :
    Function.Surjective (cylinderKMSFiniteWeightedToPiLp n) := by
  intro x
  have hc : (cylinderKMSFiniteWeightSqrt n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by positivity :
      (0 : ℝ) < (1 / 2 : ℝ) ^ n)))
  obtain ⟨f, hf⟩ := cylinderKMSFiniteToPiLp_surjective n
    ((cylinderKMSFiniteWeightSqrt n : ℂ)⁻¹ • x)
  refine ⟨f, ?_⟩
  change (cylinderKMSFiniteWeightSqrt n : ℂ) •
      cylinderKMSFiniteToPiLp n f = x
  rw [hf, smul_smul]
  field_simp
  simp

noncomputable def cylinderKMSFiniteWeightedToPiLpLinearEquiv (n : ℕ) :
    ((Fin n → Bool) → ℂ) ≃ₗ[ℂ] cylinderKMSFinitePiLp n :=
  LinearEquiv.ofBijective (cylinderKMSFiniteWeightedToPiLp n)
    ⟨cylinderKMSFiniteWeightedToPiLp_injective n,
      cylinderKMSFiniteWeightedToPiLp_surjective n⟩

theorem cylinderKMSFiniteWeightedToPiLpLinearEquiv_apply (n : ℕ)
    (f : (Fin n → Bool) → ℂ) :
    cylinderKMSFiniteWeightedToPiLpLinearEquiv n f =
      cylinderKMSFiniteWeightedToPiLp n f :=
  rfl

theorem cylinderKMSFiniteWeightedToPiLp_norm_sq (n : ℕ)
    (f : (Fin n → Bool) → ℂ) :
    ‖cylinderKMSFiniteWeightedToPiLp n f‖ ^ 2 =
      cylinderKMSQuadratic n f := by
  have hnorm : ‖cylinderKMSFiniteWeightSqrt n‖ =
      cylinderKMSFiniteWeightSqrt n := by
    simp [cylinderKMSFiniteWeightSqrt, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    ‖cylinderKMSFiniteWeightedToPiLp n f‖ ^ 2 =
        (cylinderKMSFiniteWeightSqrt n *
          ‖cylinderKMSFiniteToPiLp n f‖) ^ 2 := by
            rw [cylinderKMSFiniteWeightedToPiLp,
              LinearMap.smul_apply, norm_smul,
              Complex.norm_real, hnorm]
    _ = (cylinderKMSFiniteWeightSqrt n) ^ 2 *
          ‖cylinderKMSFiniteToPiLp n f‖ ^ 2 := by ring
    _ = ((1 / 2 : ℝ) ^ n) *
          ‖cylinderKMSFiniteToPiLp n f‖ ^ 2 := by
            rw [cylinderKMSFiniteWeightSqrt_sq]
    _ = cylinderKMSQuadratic n f := by
      rw [cylinderKMSQuadratic_eq_weighted_PiLp_norm_sq]

theorem cylinderKMSFiniteWeightedToPiLp_dist_sq (n : ℕ)
    (f g : (Fin n → Bool) → ℂ) :
    ‖cylinderKMSFiniteWeightedToPiLp n f -
        cylinderKMSFiniteWeightedToPiLp n g‖ ^ 2 =
      cylinderKMSQuadratic n (f - g) := by
  rw [← map_sub]
  exact cylinderKMSFiniteWeightedToPiLp_norm_sq n (f - g)

end InfoGeometry.Canonical.CantorKMSCylinderState
