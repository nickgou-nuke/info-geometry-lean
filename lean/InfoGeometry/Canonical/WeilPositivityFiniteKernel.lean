import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic

/-!
# Finite Weil positivity kernels

This owner contains only finite, unconditional positivity statements and a
typed premise for a future global Weil functional.  It does not identify a
finite spectral sum with the Riemann zeros and does not state an RH theorem.
-/

noncomputable section

namespace InfoGeometry.WeilPositivity

/-! ## Finite spectral kernel -/

structure SpectralEvaluation where
  eval : ℝ → ℂ

def finiteSpectralEnergy (ordinates : List ℝ) (f : SpectralEvaluation) : ℝ :=
  (ordinates.map (fun γ => (‖f.eval γ‖ : ℝ) ^ 2)).sum

@[simp]
theorem finiteSpectralEnergy_append
    (left right : List ℝ) (f : SpectralEvaluation) :
    finiteSpectralEnergy (left ++ right) f =
      finiteSpectralEnergy left f + finiteSpectralEnergy right f := by
  simp [finiteSpectralEnergy, List.map_append, List.sum_append]

theorem finiteSpectralEnergy_nonneg (ordinates : List ℝ) (f : SpectralEvaluation) :
    0 ≤ finiteSpectralEnergy ordinates f := by
  induction ordinates with
  | nil => simp [finiteSpectralEnergy]
  | cons γ rest ih =>
      simp only [finiteSpectralEnergy, List.map_cons, List.sum_cons]
      exact add_nonneg (sq_nonneg _) ih

@[simp]
theorem finiteSpectralEnergy_zero (ordinates : List ℝ) :
    finiteSpectralEnergy ordinates ⟨fun _ => 0⟩ = 0 := by
  induction ordinates with
  | nil => simp [finiteSpectralEnergy]
  | cons γ rest ih =>
      simpa [finiteSpectralEnergy] using ih

/-- A finite spectral energy vanishes exactly when every sampled mode
vanishes. -/
theorem finiteSpectralEnergy_eq_zero_iff
    (ordinates : List ℝ) (f : SpectralEvaluation) :
    finiteSpectralEnergy ordinates f = 0 ↔
      ∀ γ ∈ ordinates, f.eval γ = 0 := by
  induction ordinates with
  | nil => simp [finiteSpectralEnergy]
  | cons γ rest ih =>
      constructor
      · intro h
        have hrest_nonneg : 0 ≤ finiteSpectralEnergy rest f :=
          finiteSpectralEnergy_nonneg rest f
        have hrest_sum_nonneg :
            0 ≤ (List.map (fun γ => (‖f.eval γ‖ : ℝ) ^ 2) rest).sum := by
          simpa [finiteSpectralEnergy] using hrest_nonneg
        have hdecomp :
            (‖f.eval γ‖ : ℝ) ^ 2 + finiteSpectralEnergy rest f = 0 := by
          simpa [finiteSpectralEnergy] using h
        have hγ_sq : (‖f.eval γ‖ : ℝ) ^ 2 = 0 := by
          nlinarith [hdecomp, hrest_nonneg]
        have hγ_norm : (‖f.eval γ‖ : ℝ) = 0 := by
          nlinarith [sq_nonneg (‖f.eval γ‖ : ℝ)]
        have hγ : f.eval γ = 0 := norm_eq_zero.mp hγ_norm
        have hrest : finiteSpectralEnergy rest f = 0 := by
          nlinarith [hdecomp, hγ_sq]
        have hrest_sum :
            (List.map (fun γ => (‖f.eval γ‖ : ℝ) ^ 2) rest).sum = 0 := by
          simpa [finiteSpectralEnergy] using hrest
        have hrest_all := (ih).mp hrest
        intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact hγ
        · exact hrest_all a ha
      · intro h
        simp only [finiteSpectralEnergy, List.map_cons, List.sum_cons]
        have hγ : f.eval γ = 0 := h γ (by simp)
        have hrest : finiteSpectralEnergy rest f = 0 :=
          (ih).mpr (fun a ha => h a (by simp [ha]))
        have hrest_sum :
            (List.map (fun γ => (‖f.eval γ‖ : ℝ) ^ 2) rest).sum = 0 := by
          simpa [finiteSpectralEnergy] using hrest
        simp [hγ, hrest_sum]

/-! ## Finite arithmetic prime-power kernel -/

structure PrimePowerData where
  prime : ℕ
  power : ℕ
  logPrime : ℝ
  weight : ℝ

def primePowerArgument (p : PrimePowerData) : ℝ :=
  (p.power : ℝ) * p.logPrime

def finitePrimeComb (entries : List PrimePowerData) (f : ℝ → ℝ) : ℝ :=
  (entries.map (fun p =>
    p.weight * (f (primePowerArgument p) +
      f (-primePowerArgument p)))).sum

theorem finitePrimeComb_add (entries : List PrimePowerData) (f g : ℝ → ℝ) :
    finitePrimeComb entries (fun x => f x + g x) =
      finitePrimeComb entries f + finitePrimeComb entries g := by
  induction entries with
  | nil => simp [finitePrimeComb]
  | cons p rest ih =>
      change
        p.weight * ((f (primePowerArgument p) + g (primePowerArgument p)) +
          (f (-primePowerArgument p) + g (-primePowerArgument p))) +
            finitePrimeComb rest (fun x => f x + g x) =
          p.weight * (f (primePowerArgument p) + f (-primePowerArgument p)) +
            finitePrimeComb rest f +
            (p.weight * (g (primePowerArgument p) + g (-primePowerArgument p)) +
              finitePrimeComb rest g)
      rw [ih]
      ring

/-! ## Finite Turán/log-curvature kernel -/

/-- The three-coefficient Turán discriminant. -/
def finiteTuranDiscriminant (f₀ f₁ f₂ : ℝ) : ℝ :=
  f₁ ^ 2 - f₀ * f₂

theorem finiteTuranDiscriminant_eq_peak_numerator
    (f₀ f₁ f₂ : ℝ) :
    finiteTuranDiscriminant f₀ f₁ f₂ =
      -(f₀ * f₂ - f₁ ^ 2) := by
  unfold finiteTuranDiscriminant
  ring

/-- The logarithmic curvature numerator is the negative Turán discriminant. -/
theorem finiteTuran_log_curvature_identity
    (f₀ f₁ f₂ : ℝ) :
    (f₀ * f₂ - f₁ ^ 2) / f₀ ^ 2 =
      -finiteTuranDiscriminant f₀ f₁ f₂ / f₀ ^ 2 := by
  unfold finiteTuranDiscriminant
  ring

theorem finiteTuran_nonneg_iff_log_curvature_nonpos
    (f₀ f₁ f₂ : ℝ) (hf₀ : 0 < f₀) :
    0 ≤ finiteTuranDiscriminant f₀ f₁ f₂ ↔
      (f₀ * f₂ - f₁ ^ 2) / f₀ ^ 2 ≤ 0 := by
  have hsq : 0 < f₀ ^ 2 := sq_pos_of_pos hf₀
  rw [finiteTuran_log_curvature_identity f₀ f₁ f₂]
  constructor
  · intro h
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) (le_of_lt hsq)
  · intro h
    have hneg : -finiteTuranDiscriminant f₀ f₁ f₂ ≤ 0 := by
      have hmul := (div_le_iff₀ hsq).mp h
      simpa using hmul
    linarith

/-- A positive symmetric peak has strictly positive finite Turán discriminant. -/
theorem finiteTuran_positive_of_symmetric_peak
    (f₀ f₂ : ℝ) (hf₀ : 0 < f₀) (hf₂ : f₂ < 0) :
    0 < finiteTuranDiscriminant f₀ 0 f₂ := by
  unfold finiteTuranDiscriminant
  nlinarith

/-- The degree-two Jensen coefficient discriminant. -/
def finiteJensenQuadraticDiscriminant (f₀ f₁ f₂ : ℝ) : ℝ :=
  (2 * f₁) ^ 2 - 4 * f₀ * f₂

/-! The degree-two Jensen discriminant is exactly four times the Turán one.
This is a coefficient identity only; it does not assert hyperbolicity of a
particular entire function. -/
theorem finiteJensenQuadraticDiscriminant_eq_four_mul_turan
    (f₀ f₁ f₂ : ℝ) :
    finiteJensenQuadraticDiscriminant f₀ f₁ f₂ =
      4 * finiteTuranDiscriminant f₀ f₁ f₂ := by
  unfold finiteJensenQuadraticDiscriminant finiteTuranDiscriminant
  ring

theorem finiteJensenQuadraticDiscriminant_nonneg_of_turan_nonneg
    (f₀ f₁ f₂ : ℝ)
    (h : 0 ≤ finiteTuranDiscriminant f₀ f₁ f₂) :
    0 ≤ finiteJensenQuadraticDiscriminant f₀ f₁ f₂ := by
  rw [finiteJensenQuadraticDiscriminant_eq_four_mul_turan]
  positivity

/-- A nonnegative quadratic discriminant supplies a real root witness. -/
theorem finiteRealQuadratic_root_of_discriminant_nonneg
    (a b c : ℝ) (ha : a ≠ 0)
    (hdisc : 0 ≤ b ^ 2 - 4 * a * c) :
    ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 := by
  let d : ℝ := b ^ 2 - 4 * a * c
  have hd : 0 ≤ d := by
    exact hdisc
  have hsqrt : (Real.sqrt d) ^ 2 = d := by
    exact Real.sq_sqrt hd
  refine ⟨(-b + Real.sqrt d) / (2 * a), ?_⟩
  field_simp [ha]
  nlinarith

/-- A strictly positive quadratic discriminant supplies two distinct real roots. -/
theorem finiteRealQuadratic_two_distinct_roots_of_discriminant_pos
    (a b c : ℝ) (ha : a ≠ 0)
    (hdisc : 0 < b ^ 2 - 4 * a * c) :
    ∃ x y : ℝ,
      x ≠ y ∧
      a * x ^ 2 + b * x + c = 0 ∧
      a * y ^ 2 + b * y + c = 0 := by
  let d : ℝ := b ^ 2 - 4 * a * c
  have hd : 0 < d := hdisc
  have hsqrt_sq : (Real.sqrt d) ^ 2 = d := by
    exact Real.sq_sqrt hd.le
  have hsqrt_pos : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hroot : ∀ s : ℝ, s ^ 2 = d →
      a * ((-b + s) / (2 * a)) ^ 2 +
        b * ((-b + s) / (2 * a)) + c = 0 := by
    intro s hs
    field_simp [ha]
    nlinarith
  refine ⟨(-b + Real.sqrt d) / (2 * a),
    (-b - Real.sqrt d) / (2 * a), ?_,
    hroot (Real.sqrt d) hsqrt_sq, ?_⟩
  · intro h
    field_simp [ha] at h
    nlinarith
  · apply hroot (-Real.sqrt d)
    nlinarith [hsqrt_sq]

/-- The finite symmetric-peak sign pattern directly yields two distinct real
roots for the associated Jensen quadratic. -/
theorem finiteJensenQuadratic_two_distinct_roots_of_symmetric_peak
    (f₀ f₂ : ℝ) (hf₀ : 0 < f₀) (hf₂ : f₂ < 0) :
    ∃ x y : ℝ,
      x ≠ y ∧
      f₀ * x ^ 2 + 0 * x + f₂ = 0 ∧
      f₀ * y ^ 2 + 0 * y + f₂ = 0 := by
  have ht : 0 < finiteTuranDiscriminant f₀ 0 f₂ :=
    finiteTuran_positive_of_symmetric_peak f₀ f₂ hf₀ hf₂
  have hd : 0 < finiteJensenQuadraticDiscriminant f₀ 0 f₂ := by
    rw [finiteJensenQuadraticDiscriminant_eq_four_mul_turan]
    positivity
  simpa using
    (finiteRealQuadratic_two_distinct_roots_of_discriminant_pos
      f₀ 0 f₂ (ne_of_gt hf₀) (by simpa [finiteJensenQuadraticDiscriminant] using hd))

/-! ## Native positivity premise -/

def weilSquareEnergy {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    (weilFunctional : A →ₗ[ℝ] ℝ) (a : A) : ℝ :=
  weilFunctional (star a * a)

theorem weilSquareEnergy_nonneg
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    (weilFunctional : A →ₗ[ℝ] ℝ)
    (hpositive : ∀ a : A, 0 ≤ weilFunctional (star a * a))
    (a : A) :
    0 ≤ weilSquareEnergy weilFunctional a :=
  hpositive a

theorem weilSquareEnergy_zero
    {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    (weilFunctional : A →ₗ[ℝ] ℝ) :
    weilSquareEnergy weilFunctional 0 = 0 := by
  simp [weilSquareEnergy]

end InfoGeometry.WeilPositivity

end noncomputable section
