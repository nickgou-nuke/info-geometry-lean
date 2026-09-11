import InfoGeometry.Projective.KleinQuadricLogDeRhamClass
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.KleinQuadricDeRhamComplex
import InfoGeometry.Projective.KleinFiniteDifferentialForms
import InfoGeometry.Clifford.LogCftMonodromy

/-!
# Hadjiivanov/Klein logarithmic monodromy bridge

This owner connects the two existing finite lanes through their shared
`2πi` logarithmic datum.  The integer parameter is a winding/deck index on
the logarithmic cover, not a second geometric sheet.  It does not identify
the matrix carrier with the Klein complement or claim a classical de Rham
isomorphism.
-/

namespace InfoGeometry.Projective.HadjiivanovKleinMonodromyBridge

noncomputable section

open Complex
open Matrix
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Projective.KleinQuadric.DeRhamComplex
open InfoGeometry.Projective.KleinQuadric.LogDeRhamClass
open InfoGeometry.Projective.KleinQuadric.FiniteDifferentialForms

/-! ## Square-zero period transport -/

def unipotentPeriodMap (p : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) - p • jordanNilpotent

theorem unipotentPeriodMap_zero :
    unipotentPeriodMap 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [unipotentPeriodMap]

theorem unipotentPeriodMap_add (p q : ℂ) :
    unipotentPeriodMap (p + q) =
      unipotentPeriodMap p * unipotentPeriodMap q := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [unipotentPeriodMap, jordanNilpotent, Matrix.mul_apply]

theorem unipotentPeriodMap_neg_mul (p : ℂ) :
    unipotentPeriodMap (-p) * unipotentPeriodMap p =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [← unipotentPeriodMap_add]
  simpa using unipotentPeriodMap_zero

theorem unipotentPeriodMap_mul_neg (p : ℂ) :
    unipotentPeriodMap p * unipotentPeriodMap (-p) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [← unipotentPeriodMap_add]
  simpa using unipotentPeriodMap_zero

theorem unipotentPeriodMap_ne_one_of_ne_zero
    {p : ℂ} (hp : p ≠ 0) :
    unipotentPeriodMap p ≠ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  apply hp
  simpa [unipotentPeriodMap, jordanNilpotent] using hentry

theorem unipotentPeriodMap_eq_one_iff {p : ℂ} :
    unipotentPeriodMap p = (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔ p = 0 := by
  constructor
  · intro h
    by_contra hp
    exact unipotentPeriodMap_ne_one_of_ne_zero hp h
  · intro hp
    rw [hp]
    exact unipotentPeriodMap_zero

theorem unipotentPeriodMap_injective :
    Function.Injective unipotentPeriodMap := by
  intro p q h
  have hentry := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  simpa [unipotentPeriodMap, jordanNilpotent] using hentry

def hadjiivanovWindingRepresentation (h : ℂ) (n : ℕ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  hadjiivanovMonodromy h ^ n

theorem hadjiivanovWindingRepresentation_zero (h : ℂ) :
    hadjiivanovWindingRepresentation h 0 =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp [hadjiivanovWindingRepresentation]

theorem hadjiivanovWindingRepresentation_add (h : ℂ) (m n : ℕ) :
    hadjiivanovWindingRepresentation h (m + n) =
      hadjiivanovWindingRepresentation h m *
        hadjiivanovWindingRepresentation h n := by
  simp [hadjiivanovWindingRepresentation, pow_add]

theorem logShearBase_eq_neg_logarithmicPeriod
    (R : ℝ) (hR : 0 < R) :
    logShearBase = -logarithmicPeriod R := by
  rw [logarithmicPeriod_eq_residue R hR]
  unfold logShearBase
  ring

theorem hadjiivanovMonodromy_pow_eq_phase_period_shear
    (R : ℝ) (hR : 0 < R) (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) -
          ((n : ℂ) * logarithmicPeriod R) • jordanNilpotent) := by
  rw [hadjiivanovMonodromy_pow_winding]
  rw [logShearBase_eq_neg_logarithmicPeriod R hR]
  congr 1
  rw [mul_neg, neg_smul]
  simp [sub_eq_add_neg]

theorem hadjiivanov_shear_coefficient_is_winding_period
    (R : ℝ) (hR : 0 < R) (n : ℕ) :
    (n : ℂ) * logShearBase =
      -((n : ℂ) * logarithmicPeriod R) := by
  rw [logShearBase_eq_neg_logarithmicPeriod R hR]
  rw [mul_neg]

theorem hadjiivanovMonodromy_pow_eq_period_monodromy
    (R : ℝ) (hR : 0 < R) (h : ℂ) (n : ℕ) :
    hadjiivanovWindingRepresentation h n =
      lcftPhase h ^ n •
        unipotentPeriodMap ((n : ℂ) * logarithmicPeriod R) := by
  rw [hadjiivanovWindingRepresentation]
  rw [hadjiivanovMonodromy_pow_eq_phase_period_shear R hR h n]
  rfl

/-! ## Cohomology-to-monodromy factorization -/

def periodMonodromyOfClass
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (c : cohomologyModule d₀ d₁ hdd) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  unipotentPeriodMap (periodClassFactor d₀ d₁ hdd period hperiod c)

theorem periodMonodromyOfClass_apply
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (ω : Ω₁) (hω : d₁ ω = 0) :
    periodMonodromyOfClass d₀ d₁ hdd period hperiod
        (closedClass d₀ d₁ hdd ω hω) =
      unipotentPeriodMap (period ω) := by
  rw [periodMonodromyOfClass, periodClassFactor_apply]

theorem periodMonodromyOfClass_eq_one_iff
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (c : cohomologyModule d₀ d₁ hdd) :
    periodMonodromyOfClass d₀ d₁ hdd period hperiod c =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      periodClassFactor d₀ d₁ hdd period hperiod c = 0 := by
  unfold periodMonodromyOfClass
  exact unipotentPeriodMap_eq_one_iff

theorem periodMonodromyOfClass_ne_one_iff
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (c : cohomologyModule d₀ d₁ hdd) :
    periodMonodromyOfClass d₀ d₁ hdd period hperiod c ≠
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      periodClassFactor d₀ d₁ hdd period hperiod c ≠ 0 := by
  exact not_congr (periodMonodromyOfClass_eq_one_iff
    d₀ d₁ hdd period hperiod c)

theorem periodMonodromyOfClass_closedClass_ne_one_iff
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (ω : Ω₁) (hω : d₁ ω = 0) :
    periodMonodromyOfClass d₀ d₁ hdd period hperiod
        (closedClass d₀ d₁ hdd ω hω) ≠
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      period ω ≠ 0 := by
  rw [periodMonodromyOfClass_apply d₀ d₁ hdd period hperiod ω hω]
  exact not_congr unipotentPeriodMap_eq_one_iff

theorem finiteLogarithmicForm_periodMonodromy (p : ℂ) :
    periodMonodromyOfClass
        dZero dOne differential_squared
        logarithmicPeriod period_vanishes_on_exact
        (cohomologyClass p) =
      unipotentPeriodMap p := by
  unfold cohomologyClass
  rw [periodMonodromyOfClass_apply]
  rfl

theorem finiteLogarithmicForm_periodMonodromy_ne_one
    {p : ℂ} (hp : p ≠ 0) :
    periodMonodromyOfClass
        dZero dOne differential_squared
        logarithmicPeriod period_vanishes_on_exact
        (cohomologyClass p) ≠
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [finiteLogarithmicForm_periodMonodromy]
  exact unipotentPeriodMap_ne_one_of_ne_zero hp

theorem hadjiivanovMonodromy_pow_eq_finiteLogarithmicForm_monodromy
    (R : ℝ) (hR : 0 < R) (h : ℂ) (n : ℕ) :
    hadjiivanovWindingRepresentation h n =
      lcftPhase h ^ n •
        periodMonodromyOfClass
          dZero dOne differential_squared
          logarithmicPeriod period_vanishes_on_exact
          (cohomologyClass ((n : ℂ) * logarithmicPeriod R)) := by
  rw [finiteLogarithmicForm_periodMonodromy]
  exact hadjiivanovMonodromy_pow_eq_period_monodromy R hR h n

theorem kleinDLogCoefficient_ne_zero (P : KleinComplement) :
    kleinDLogCoefficient P ≠ 0 := by
  exact one_div_ne_zero P.2

theorem kleinComplement_dLog_periodMonodromy (P : KleinComplement) :
    periodMonodromyOfClass
        dZero dOne differential_squared
        logarithmicPeriod period_vanishes_on_exact
        (cohomologyClass (kleinDLogCoefficient P)) =
      unipotentPeriodMap (kleinDLogCoefficient P) := by
  exact finiteLogarithmicForm_periodMonodromy (kleinDLogCoefficient P)

theorem kleinComplement_dLog_periodMonodromy_ne_one (P : KleinComplement) :
    periodMonodromyOfClass
        dZero dOne differential_squared
        logarithmicPeriod period_vanishes_on_exact
        (cohomologyClass (kleinDLogCoefficient P)) ≠
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [kleinComplement_dLog_periodMonodromy]
  exact unipotentPeriodMap_ne_one_of_ne_zero
    (kleinDLogCoefficient_ne_zero P)

theorem kleinLogPeriodReadoutClass_monodromy
    (R : ℝ) :
    periodMonodromyOfClass
        kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutClass R) =
      unipotentPeriodMap (logarithmicPeriod R) := by
  unfold kleinLogPeriodReadoutClass
  rw [periodMonodromyOfClass_apply
    kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
    (by intro η; simp [kleinZeroD₀])
    (logarithmicPeriod R) (by simp [kleinZeroD₁])]
  simp

theorem kleinLogPeriodReadoutWindingClass_monodromy
    (R : ℝ) (n : ℤ) :
    periodMonodromyOfClass
        kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass R n) =
      unipotentPeriodMap ((n : ℂ) * logarithmicPeriod R) := by
  unfold InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass
  rw [periodMonodromyOfClass_apply
    kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
    (by intro η; simp [kleinZeroD₀])
    ((n : ℂ) * logarithmicPeriod R) (by simp [kleinZeroD₁])]
  simp

theorem kleinLogPeriodReadoutWindingClass_monodromy_ne_one_iff
    (R : ℝ) (n : ℤ) :
    periodMonodromyOfClass
        kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass R n) ≠
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      (n : ℂ) * logarithmicPeriod R ≠ 0 := by
  rw [kleinLogPeriodReadoutWindingClass_monodromy]
  exact not_congr unipotentPeriodMap_eq_one_iff

theorem kleinLogPeriodReadoutWindingClass_monodromy_ne_one_iff_winding_ne_zero
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    periodMonodromyOfClass
        kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass R n) ≠
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔ n ≠ 0 := by
  rw [kleinLogPeriodReadoutWindingClass_monodromy_ne_one_iff]
  constructor
  · intro h hn
    subst n
    apply h
    simp
  · intro hn
    exact mul_ne_zero (by exact_mod_cast hn)
      (logarithmicPeriod_ne_zero R hR)

theorem kleinLogPeriodReadoutClass_monodromy_ne_one
    (R : ℝ) (hR : 0 < R) :
    periodMonodromyOfClass
        kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutClass R) ≠
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [kleinLogPeriodReadoutClass_monodromy]
  exact unipotentPeriodMap_ne_one_of_ne_zero
    (logarithmicPeriod_ne_zero R hR)

theorem periodMonodromyOfClass_zero
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0) :
    periodMonodromyOfClass d₀ d₁ hdd period hperiod 0 =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [periodMonodromyOfClass]
  simp [unipotentPeriodMap]

theorem periodMonodromyOfClass_add
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (c₁ c₂ : cohomologyModule d₀ d₁ hdd) :
    periodMonodromyOfClass d₀ d₁ hdd period hperiod (c₁ + c₂) =
      periodMonodromyOfClass d₀ d₁ hdd period hperiod c₁ *
        periodMonodromyOfClass d₀ d₁ hdd period hperiod c₂ := by
  rw [periodMonodromyOfClass, periodMonodromyOfClass,
    periodMonodromyOfClass, map_add]
  exact unipotentPeriodMap_add _ _

theorem kleinLogPeriodReadoutWindingClass_monodromy_add
    (R : ℝ) (m n : ℤ) :
    periodMonodromyOfClass
        kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass
          R (m + n)) =
      periodMonodromyOfClass
          kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
          (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
          (by intro η; simp [kleinZeroD₀])
          (InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass
            R m) *
        periodMonodromyOfClass
          kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
          (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
          (by intro η; simp [kleinZeroD₀])
          (InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass
            R n) := by
  rw [InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass_add]
  exact periodMonodromyOfClass_add
    kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
    (by intro η; simp [kleinZeroD₀])
    (InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass
      R m)
    (InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass
      R n)

theorem periodMonodromyOfClass_neg_mul
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (c : cohomologyModule d₀ d₁ hdd) :
    periodMonodromyOfClass d₀ d₁ hdd period hperiod (-c) *
        periodMonodromyOfClass d₀ d₁ hdd period hperiod c =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [periodMonodromyOfClass, periodMonodromyOfClass, map_neg]
  exact unipotentPeriodMap_neg_mul _

theorem kleinLogPeriodReadoutWindingClass_monodromy_neg_mul
    (R : ℝ) (n : ℤ) :
    periodMonodromyOfClass
        kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass
          R (-n)) *
      periodMonodromyOfClass
        kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass
          R n) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass_neg]
  exact periodMonodromyOfClass_neg_mul
    kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
    (by intro η; simp [kleinZeroD₀])
    (InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass
      R n)

theorem periodMonodromyOfClass_mul_neg
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (c : cohomologyModule d₀ d₁ hdd) :
    periodMonodromyOfClass d₀ d₁ hdd period hperiod c *
        periodMonodromyOfClass d₀ d₁ hdd period hperiod (-c) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [periodMonodromyOfClass, periodMonodromyOfClass, map_neg]
  exact unipotentPeriodMap_mul_neg _

theorem kleinLogPeriodReadoutWindingClass_monodromy_mul_neg
    (R : ℝ) (n : ℤ) :
    periodMonodromyOfClass
        kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass
          R n) *
      periodMonodromyOfClass
        kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass
          R (-n)) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass_neg]
  exact periodMonodromyOfClass_mul_neg
    kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
    (by intro η; simp [kleinZeroD₀])
    (InfoGeometry.Projective.KleinQuadric.DeRhamComplex.kleinLogPeriodReadoutWindingClass
      R n)

/-- The additive cohomology quotient acts multiplicatively through its
    unipotent period monodromy.  `Multiplicative` is the native Mathlib
    change of monoid structure; no new quotient carrier is introduced. -/
def periodMonodromyRepresentation
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0) :
    Multiplicative (cohomologyModule d₀ d₁ hdd) →*
      Matrix (Fin 2) (Fin 2) ℂ where
  toFun := periodMonodromyOfClass d₀ d₁ hdd period hperiod
  map_one' := by
    exact periodMonodromyOfClass_zero d₀ d₁ hdd period hperiod
  map_mul' := by
    intro c₁ c₂
    exact periodMonodromyOfClass_add d₀ d₁ hdd period hperiod c₁ c₂

@[simp] theorem periodMonodromyRepresentation_apply
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (c : cohomologyModule d₀ d₁ hdd) :
    periodMonodromyRepresentation d₀ d₁ hdd period hperiod
        (Multiplicative.ofAdd c) =
      periodMonodromyOfClass d₀ d₁ hdd period hperiod c := rfl

theorem periodMonodromyRepresentation_ofAdd_neg_mul
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (c : cohomologyModule d₀ d₁ hdd) :
    periodMonodromyRepresentation d₀ d₁ hdd period hperiod
        (Multiplicative.ofAdd (-c)) *
        periodMonodromyRepresentation d₀ d₁ hdd period hperiod
        (Multiplicative.ofAdd c) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simpa only [periodMonodromyRepresentation_apply] using
    periodMonodromyOfClass_neg_mul d₀ d₁ hdd period hperiod c

theorem periodMonodromyRepresentation_ofAdd_mul_neg
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (c : cohomologyModule d₀ d₁ hdd) :
    periodMonodromyRepresentation d₀ d₁ hdd period hperiod
        (Multiplicative.ofAdd c) *
        periodMonodromyRepresentation d₀ d₁ hdd period hperiod
        (Multiplicative.ofAdd (-c)) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simpa only [periodMonodromyRepresentation_apply] using
    periodMonodromyOfClass_mul_neg d₀ d₁ hdd period hperiod c

theorem periodMonodromyRepresentation_injective
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (hinj : Function.Injective
      (periodClassFactor d₀ d₁ hdd period hperiod)) :
    Function.Injective
      (periodMonodromyRepresentation d₀ d₁ hdd period hperiod) := by
  intro c₁ c₂ h
  apply Multiplicative.toAdd.injective
  apply hinj
  apply unipotentPeriodMap_injective
  simpa only [periodMonodromyRepresentation_apply] using h

theorem periodMonodromyOfClass_injective
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (hinj : Function.Injective
      (periodClassFactor d₀ d₁ hdd period hperiod)) :
    Function.Injective
      (periodMonodromyOfClass d₀ d₁ hdd period hperiod) := by
  intro c₁ c₂ h
  apply hinj
  apply unipotentPeriodMap_injective
  exact h

theorem periodMonodromyOfClass_exact
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (η : Ω₀) :
    periodMonodromyOfClass d₀ d₁ hdd period hperiod
        (closedClass d₀ d₁ hdd (d₀ η)
          (exact_forms_are_closed d₀ d₁ hdd η)) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [exact_form_class_eq_zero]
  exact periodMonodromyOfClass_zero d₀ d₁ hdd period hperiod

theorem periodMonodromyOfClass_ne_one_of_period_ne_zero
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (ω : Ω₁) (hω : d₁ ω = 0)
    (hωperiod : period ω ≠ 0) :
    periodMonodromyOfClass d₀ d₁ hdd period hperiod
        (closedClass d₀ d₁ hdd ω hω) ≠
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [periodMonodromyOfClass_apply d₀ d₁ hdd period hperiod ω hω]
  exact unipotentPeriodMap_ne_one_of_ne_zero hωperiod

theorem periodMonodromyOfClass_eq_one_iff_periodClass_eq_zero
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (c : cohomologyModule d₀ d₁ hdd) :
    periodMonodromyOfClass d₀ d₁ hdd period hperiod c =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      periodClassFactor d₀ d₁ hdd period hperiod c = 0 := by
  change unipotentPeriodMap
      (periodClassFactor d₀ d₁ hdd period hperiod c) = _ ↔ _
  exact unipotentPeriodMap_eq_one_iff

theorem periodMonodromyOfClass_ne_one_iff_periodClass_ne_zero
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (c : cohomologyModule d₀ d₁ hdd) :
    periodMonodromyOfClass d₀ d₁ hdd period hperiod c ≠
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      periodClassFactor d₀ d₁ hdd period hperiod c ≠ 0 := by
  exact not_congr
    (periodMonodromyOfClass_eq_one_iff_periodClass_eq_zero
      d₀ d₁ hdd period hperiod c)

theorem periodMonodromyOfClass_eq_one_iff_class_eq_zero
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (hinj : Function.Injective
      (periodClassFactor d₀ d₁ hdd period hperiod))
    (c : cohomologyModule d₀ d₁ hdd) :
    periodMonodromyOfClass d₀ d₁ hdd period hperiod c =
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      c = 0 := by
  rw [periodMonodromyOfClass_eq_one_iff_periodClass_eq_zero]
  constructor
  · intro hc
    apply hinj
    simpa using hc
  · intro hc
    rw [hc]
    simp

theorem periodMonodromyOfClass_ne_one_iff_class_ne_zero
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (hinj : Function.Injective
      (periodClassFactor d₀ d₁ hdd period hperiod))
    (c : cohomologyModule d₀ d₁ hdd) :
    periodMonodromyOfClass d₀ d₁ hdd period hperiod c ≠
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      c ≠ 0 := by
  exact not_congr
    (periodMonodromyOfClass_eq_one_iff_class_eq_zero
      d₀ d₁ hdd period hperiod hinj c)

theorem kleinLogPeriodReadoutClass_monodromy_eq_one_iff
    (R : ℝ) :
    periodMonodromyOfClass
        kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutClass R) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      kleinLogPeriodReadoutClass R = 0 := by
  exact periodMonodromyOfClass_eq_one_iff_class_eq_zero
    kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
    (by intro η; simp [kleinZeroD₀])
    kleinZeroPeriodClassFactor_injective
    (kleinLogPeriodReadoutClass R)

theorem kleinLogPeriodReadoutClass_monodromy_ne_one_iff
    (R : ℝ) :
    periodMonodromyOfClass
        kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutClass R) ≠
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      kleinLogPeriodReadoutClass R ≠ 0 := by
  exact periodMonodromyOfClass_ne_one_iff_class_ne_zero
    kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
    (by intro η; simp [kleinZeroD₀])
    kleinZeroPeriodClassFactor_injective
    (kleinLogPeriodReadoutClass R)

theorem kleinLogPeriodReadoutClass_monodromy_ne_one_iff_period_ne_zero
    (R : ℝ) :
    periodMonodromyOfClass
        kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])
        (kleinLogPeriodReadoutClass R) ≠
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      logarithmicPeriod R ≠ 0 := by
  rw [kleinLogPeriodReadoutClass_monodromy_ne_one_iff,
    kleinLogPeriodReadoutClass_ne_zero_iff]

theorem periodMonodromyRepresentation_ofAdd_eq_one_iff
    {Ω₀ Ω₁ Ω₂ : Type*}
    [AddCommGroup Ω₀] [Module ℂ Ω₀]
    [AddCommGroup Ω₁] [Module ℂ Ω₁]
    [AddCommGroup Ω₂] [Module ℂ Ω₂]
    (d₀ : Ω₀ →ₗ[ℂ] Ω₁) (d₁ : Ω₁ →ₗ[ℂ] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[ℂ] ℂ)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (c : cohomologyModule d₀ d₁ hdd) :
    periodMonodromyRepresentation d₀ d₁ hdd period hperiod
        (Multiplicative.ofAdd c) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) ↔
      periodClassFactor d₀ d₁ hdd period hperiod c = 0 := by
  simpa only [periodMonodromyRepresentation_apply] using
    periodMonodromyOfClass_eq_one_iff_periodClass_eq_zero
      d₀ d₁ hdd period hperiod c

theorem hadjiivanov_unit_winding_holonomy
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    windingCharacter 1 n =
      Complex.exp ((n : ℂ) * logarithmicPeriod R) := by
  rw [windingCharacter_one_is_trivial]
  exact (klein_logarithmic_holonomy_of_winding R hR n).symm

end
end InfoGeometry.Projective.HadjiivanovKleinMonodromyBridge
