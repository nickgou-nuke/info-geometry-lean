import InfoGeometry.Projective.HadjiivanovKleinMonodromyBridge

noncomputable section

namespace InfoGeometry.Projective.KleinHadjiivanovPeriodMonodromyBridge

open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Projective.HadjiivanovKleinMonodromyBridge
open InfoGeometry.Projective.KleinQuadric.DeRhamComplex
open InfoGeometry.Projective.KleinQuadric.LogDeRhamClass
open InfoGeometry.Projective.KleinQuadric.DeRhamComplex

def windingPeriod (n : ℤ) : ℂ :=
  (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)

theorem windingPeriod_add (m n : ℤ) :
    windingPeriod (m + n) = windingPeriod m + windingPeriod n := by
  unfold windingPeriod
  norm_num [Int.cast_add]
  ring

theorem windingPeriod_neg (n : ℤ) :
    windingPeriod (-n) = -windingPeriod n := by
  unfold windingPeriod
  norm_num [Int.cast_neg]

theorem unipotentPeriodMap_winding_neg_mul (n : ℤ) :
    unipotentPeriodMap (windingPeriod (-n)) *
        unipotentPeriodMap (windingPeriod n) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [windingPeriod_neg]
  exact unipotentPeriodMap_neg_mul (windingPeriod n)

theorem unipotentPeriodMap_winding (n : ℤ) :
    unipotentPeriodMap (windingPeriod n) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) -
        ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) • jordanNilpotent := by
  rfl

theorem unipotentPeriodMap_winding_add (m n : ℤ) :
    unipotentPeriodMap (windingPeriod (m + n)) =
      unipotentPeriodMap (windingPeriod m) *
        unipotentPeriodMap (windingPeriod n) := by
  rw [windingPeriod_add, unipotentPeriodMap_add]
theorem windingPeriod_eq_logarithmicPeriod
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    windingPeriod n = (n : ℂ) * logarithmicPeriod R := by
  unfold windingPeriod
  rw [logarithmicPeriod_eq_residue R hR]

theorem hadjiivanovPower_eq_windingPeriod
    (R : ℝ) (hR : 0 < R) (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        unipotentPeriodMap (windingPeriod (n : ℤ)) := by
  rw [windingPeriod_eq_logarithmicPeriod R hR (n : ℤ)]
  exact hadjiivanovMonodromy_pow_eq_period_monodromy R hR h n

theorem periodMonodromy_factorsThroughDeRhamQuotient
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0) :
    ∃ periodClass : cohomologyModule d₀ d₁ hdd →ₗ[ℂ] ℂ,
      ∀ (ω : Ω₁) (hω : d₁ ω = 0),
        periodClass (closedClass d₀ d₁ hdd ω hω) = period ω := by
  refine ⟨periodClassFactor d₀ d₁ hdd period hperiod, ?_⟩
  intro ω hω
  exact periodClassFactor_apply d₀ d₁ hdd period hperiod ω hω

/-! ## Cohomology-to-unipotent transport

The quotient class is first evaluated by a scalar period functional and only
then sent to the square-zero matrix transport.  This keeps the form, its
period, and the matrix monodromy as distinct typed objects.
-/

theorem unipotentPeriodMap_periodClass_zero
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0)
    (periodClass : cohomologyModule d₀ d₁ hdd →ₗ[ℂ] ℂ) :
    unipotentPeriodMap (periodClass 0) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [map_zero]
  exact unipotentPeriodMap_zero

theorem unipotentPeriodMap_periodClass_add
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0)
    (periodClass : cohomologyModule d₀ d₁ hdd →ₗ[ℂ] ℂ)
    (c₁ c₂ : cohomologyModule d₀ d₁ hdd) :
    unipotentPeriodMap (periodClass (c₁ + c₂)) =
      unipotentPeriodMap (periodClass c₁) *
        unipotentPeriodMap (periodClass c₂) := by
  rw [map_add]
  exact unipotentPeriodMap_add _ _

theorem unipotentPeriodMap_exact_periodClass
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0)
    (periodClass : cohomologyModule d₀ d₁ hdd →ₗ[ℂ] ℂ)
    (η : Ω₀) :
    unipotentPeriodMap
        (periodClass (closedClass d₀ d₁ hdd (d₀ η)
          (exact_forms_are_closed d₀ d₁ hdd η))) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [exact_form_class_eq_zero]
  exact unipotentPeriodMap_periodClass_zero d₀ d₁ hdd periodClass

/-! ## Concrete finite Klein readout -/

def kleinReadoutPeriodClass :
    cohomologyModule kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex →ₗ[ℂ] ℂ :=
  periodClassFactor kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (by simp [kleinZeroD₀])

theorem kleinReadoutPeriodClass_apply (R : ℝ) :
    kleinReadoutPeriodClass (kleinLogPeriodReadoutClass R) =
      InfoGeometry.Projective.KleinQuadric.LogDeRhamClass.logarithmicPeriod R := by
  simpa using
    (periodClassFactor_apply kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
      (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
      (by intro η; simp [kleinZeroD₀])
      _ (by simp [kleinZeroD₁]))

theorem kleinReadoutUnipotentPeriodMap_eq_logarithmicPeriod
    (R : ℝ) :
    unipotentPeriodMap
        (kleinReadoutPeriodClass (kleinLogPeriodReadoutClass R)) =
      unipotentPeriodMap
        (InfoGeometry.Projective.KleinQuadric.LogDeRhamClass.logarithmicPeriod R) := by
  rw [kleinReadoutPeriodClass_apply]

theorem kleinReadoutPeriodMonodromy_eq_logarithmicPeriod
    (R : ℝ) :
    periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutClass R) =
      unipotentPeriodMap
        (InfoGeometry.Projective.KleinQuadric.LogDeRhamClass.logarithmicPeriod R) := by
  change unipotentPeriodMap
      (kleinReadoutPeriodClass (kleinLogPeriodReadoutClass R)) = _
  exact kleinReadoutUnipotentPeriodMap_eq_logarithmicPeriod R

theorem kleinReadoutPeriodMonodromy_eq_cohomology_coordinate
    (c : cohomologyModule kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex) :
    periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀]) c =
      unipotentPeriodMap (kleinZeroCohomologyEquiv c) := by
  change unipotentPeriodMap (kleinReadoutPeriodClass c) = _
  rw [kleinZeroCohomologyEquiv_apply]
  rfl

theorem kleinReadoutPeriodMonodromy_eq_one_iff
    (c : cohomologyModule kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex) :
    periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀]) c =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      kleinZeroCohomologyEquiv c = 0 := by
  rw [kleinReadoutPeriodMonodromy_eq_cohomology_coordinate]
  exact unipotentPeriodMap_eq_one_iff

theorem kleinReadoutPeriodMonodromy_eq_one_iff_class_eq_zero
    (c : cohomologyModule kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex) :
    periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀]) c =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      c = 0 := by
  constructor
  · intro h
    have hcoord := (kleinReadoutPeriodMonodromy_eq_one_iff c).mp h
    apply kleinZeroCohomologyEquiv.injective
    simpa using hcoord
  · intro hc
    subst c
    rw [kleinReadoutPeriodMonodromy_eq_cohomology_coordinate]
    exact unipotentPeriodMap_zero

theorem kleinReadoutLogarithmicPeriodMonodromy_eq_one_iff
    (R : ℝ) :
    periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutClass R) =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      InfoGeometry.Projective.KleinQuadric.LogDeRhamClass.logarithmicPeriod R = 0 := by
  rw [kleinReadoutPeriodMonodromy_eq_logarithmicPeriod]
  exact unipotentPeriodMap_eq_one_iff

theorem kleinReadoutPeriodMonodromy_ne_one
    (R : ℝ) (hR : 0 < R) :
    periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutClass R) ≠
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [kleinReadoutPeriodMonodromy_eq_logarithmicPeriod]
  apply unipotentPeriodMap_ne_one_of_ne_zero
  exact InfoGeometry.Projective.KleinQuadric.LogDeRhamClass.logarithmicPeriod_ne_zero
    R hR

theorem kleinReadoutUnipotentMonodromy_ne_one
    (R : ℝ) (hR : 0 < R) :
    unipotentPeriodMap
        (kleinReadoutPeriodClass (kleinLogPeriodReadoutClass R)) ≠
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply unipotentPeriodMap_ne_one_of_ne_zero
  rw [kleinReadoutPeriodClass_apply]
  exact InfoGeometry.Projective.KleinQuadric.LogDeRhamClass.logarithmicPeriod_ne_zero
    R hR

theorem kleinReadoutWindingPeriodMonodromy
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutWindingClass R n) =
      unipotentPeriodMap (windingPeriod n) := by
  change unipotentPeriodMap
      (kleinReadoutPeriodClass
        (kleinLogPeriodReadoutWindingClass R n)) = _
  change unipotentPeriodMap
      ((periodClassFactor kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀]))
        (closedClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
          ((n : ℂ) * logarithmicPeriod R) (by simp [kleinZeroD₁]))) = _
  rw [periodClassFactor_apply]
  rw [windingPeriod_eq_logarithmicPeriod R hR n]
  rfl

theorem kleinReadoutWindingPeriodMonodromy_eq_one_iff
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutWindingClass R n) =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      n = 0 := by
  rw [kleinReadoutWindingPeriodMonodromy R hR n,
    unipotentPeriodMap_eq_one_iff]
  constructor
  · intro hperiod
    have hperiod' : (n : ℂ) * logarithmicPeriod R = 0 := by
      rw [← windingPeriod_eq_logarithmicPeriod R hR n]
      exact hperiod
    have hn : (n : ℂ) = 0 :=
      (mul_eq_zero.mp hperiod').resolve_right
        (InfoGeometry.Projective.KleinQuadric.LogDeRhamClass.logarithmicPeriod_ne_zero
          R hR)
    exact_mod_cast hn
  · intro hn
    simp [hn, windingPeriod]

theorem kleinReadoutWindingPeriodMonodromy_injective
    (R : ℝ) (hR : 0 < R) :
    Function.Injective (fun n : ℤ =>
      periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutWindingClass R n)) := by
  intro m n hmn
  change
    periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutWindingClass R m) =
      periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutWindingClass R n) at hmn
  rw [kleinReadoutWindingPeriodMonodromy R hR m,
    kleinReadoutWindingPeriodMonodromy R hR n] at hmn
  have hperiod : windingPeriod m = windingPeriod n :=
    unipotentPeriodMap_injective hmn
  rw [windingPeriod_eq_logarithmicPeriod R hR m,
    windingPeriod_eq_logarithmicPeriod R hR n] at hperiod
  have hzero : ((m - n : ℤ) : ℂ) *
      InfoGeometry.Projective.KleinQuadric.LogDeRhamClass.logarithmicPeriod R = 0 := by
    rw [Int.cast_sub]
    calc
      ((m : ℂ) - (n : ℂ)) *
          InfoGeometry.Projective.KleinQuadric.LogDeRhamClass.logarithmicPeriod R =
          (m : ℂ) *
              InfoGeometry.Projective.KleinQuadric.LogDeRhamClass.logarithmicPeriod R -
            (n : ℂ) *
              InfoGeometry.Projective.KleinQuadric.LogDeRhamClass.logarithmicPeriod R := by
        ring
      _ = 0 := sub_eq_zero.mpr hperiod
  have hdiff : m - n = 0 := by
    by_contra hne
    exact (mul_ne_zero (by exact_mod_cast hne)
      (InfoGeometry.Projective.KleinQuadric.LogDeRhamClass.logarithmicPeriod_ne_zero
        R hR)) hzero
  exact sub_eq_zero.mp hdiff

theorem hadjiivanovPower_eq_windingReadoutPeriodMonodromy
    (R : ℝ) (hR : 0 < R) (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
          (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
          (by intro η; simp [kleinZeroD₀])
          (kleinLogPeriodReadoutWindingClass R (n : ℤ)) := by
  rw [hadjiivanovPower_eq_windingPeriod R hR h n]
  rw [kleinReadoutWindingPeriodMonodromy R hR (n : ℤ)]

theorem kleinReadoutWindingPeriodMonodromy_add
    (R : ℝ) (hR : 0 < R) (m n : ℤ) :
    periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutWindingClass R (m + n)) =
      periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutWindingClass R m) *
      periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutWindingClass R n) := by
  rw [kleinReadoutWindingPeriodMonodromy R hR (m + n)]
  rw [kleinReadoutWindingPeriodMonodromy R hR m,
    kleinReadoutWindingPeriodMonodromy R hR n]
  exact unipotentPeriodMap_winding_add m n

theorem kleinReadoutWindingPeriodMonodromy_neg_mul
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutWindingClass R (-n)) *
      periodMonodromyOfClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutWindingClass R n) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [kleinReadoutWindingPeriodMonodromy R hR (-n),
    kleinReadoutWindingPeriodMonodromy R hR n]
  exact unipotentPeriodMap_winding_neg_mul n

end InfoGeometry.Projective.KleinHadjiivanovPeriodMonodromyBridge
