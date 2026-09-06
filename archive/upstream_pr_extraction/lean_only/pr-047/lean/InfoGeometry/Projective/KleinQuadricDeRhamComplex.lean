import InfoGeometry.Projective.KleinQuadricLogDeRhamClass
import Mathlib.Tactic

/-!
# A theorem-safe de Rham quotient interface for the Klein complement

This owner deliberately constructs only the algebraic three-term de Rham
quotient supplied by a concrete finite-stage complex.  It does not claim a
classical manifold de Rham complex or a global `H¹_dR` computation.  The
non-exactness theorem is the period obstruction: a linear period functional
which vanishes on exact forms cannot take a nonzero value on an exact closed
form.
-/

namespace InfoGeometry.Projective.KleinQuadric.DeRhamComplex

noncomputable section

variable {R Ω₀ Ω₁ Ω₂ : Type*}
variable [CommRing R]
variable [AddCommGroup Ω₀] [Module R Ω₀]
variable [AddCommGroup Ω₁] [Module R Ω₁]
variable [AddCommGroup Ω₂] [Module R Ω₂]

def cohomologyModule
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (_hdd : d₁.comp d₀ = 0) : Type _ :=
  LinearMap.ker d₁ ⧸ (LinearMap.range d₀).comap (LinearMap.ker d₁).subtype

instance cohomologyModule.addCommGroup
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) :
    AddCommGroup (cohomologyModule d₀ d₁ hdd) := by
  change AddCommGroup
    (LinearMap.ker d₁ ⧸ (LinearMap.range d₀).comap (LinearMap.ker d₁).subtype)
  infer_instance

instance cohomologyModule.module
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) :
    Module R (cohomologyModule d₀ d₁ hdd) := by
  change Module R
    (LinearMap.ker d₁ ⧸ (LinearMap.range d₀).comap (LinearMap.ker d₁).subtype)
  infer_instance

def cycleQuotientMap
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) :
    LinearMap.ker d₁ →ₗ[R] cohomologyModule d₀ d₁ hdd :=
  Submodule.mkQ
    ((LinearMap.range d₀).comap (LinearMap.ker d₁).subtype)

def closedClass
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) (ω : Ω₁) (hω : d₁ ω = 0) :
    cohomologyModule d₀ d₁ hdd :=
  cycleQuotientMap d₀ d₁ hdd ⟨ω, hω⟩

theorem cycleQuotientMap_apply
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) (ω : Ω₁) (hω : d₁ ω = 0) :
    cycleQuotientMap d₀ d₁ hdd ⟨ω, hω⟩ =
      closedClass d₀ d₁ hdd ω hω := rfl

theorem cycleQuotientMap_surjective
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) :
    Function.Surjective (cycleQuotientMap d₀ d₁ hdd) := by
  exact Submodule.mkQ_surjective _

theorem cycleQuotientMap_ker
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) :
    LinearMap.ker (cycleQuotientMap d₀ d₁ hdd) =
      (LinearMap.range d₀).comap (LinearMap.ker d₁).subtype := by
  exact Submodule.ker_mkQ _

def cycleQuotientLift
    {X : Type*} [AddCommGroup X] [Module R X]
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) (f : LinearMap.ker d₁ →ₗ[R] X)
    (hf : ∀ x, x ∈ (LinearMap.range d₀).comap
        (LinearMap.ker d₁).subtype → f x = 0) :
    cohomologyModule d₀ d₁ hdd →ₗ[R] X :=
  ((LinearMap.range d₀).comap (LinearMap.ker d₁).subtype).liftQ f hf

theorem cycleQuotientLift_comp_cycleQuotientMap
    {X : Type*} [AddCommGroup X] [Module R X]
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) (f : LinearMap.ker d₁ →ₗ[R] X)
    (hf : ∀ x, x ∈ (LinearMap.range d₀).comap
        (LinearMap.ker d₁).subtype → f x = 0) :
    (cycleQuotientLift d₀ d₁ hdd f hf).comp
        (cycleQuotientMap d₀ d₁ hdd) = f := by
  exact Submodule.liftQ_mkQ
    ((LinearMap.range d₀).comap (LinearMap.ker d₁).subtype) f hf

theorem cycleQuotientLift_unique
    {X : Type*} [AddCommGroup X] [Module R X]
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) (f : LinearMap.ker d₁ →ₗ[R] X)
    (hf : ∀ x, x ∈ (LinearMap.range d₀).comap
        (LinearMap.ker d₁).subtype → f x = 0)
    (g : cohomologyModule d₀ d₁ hdd →ₗ[R] X)
    (hg : g.comp (cycleQuotientMap d₀ d₁ hdd) = f) :
    g = cycleQuotientLift d₀ d₁ hdd f hf := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := cycleQuotientMap_surjective d₀ d₁ hdd y
  have hgx := LinearMap.congr_fun hg x
  have hlx := LinearMap.congr_fun
    (cycleQuotientLift_comp_cycleQuotientMap d₀ d₁ hdd f hf) x
  simpa [LinearMap.comp_apply] using hgx.trans hlx.symm

theorem closedClass_add
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0)
    (ω η : Ω₁) (hω : d₁ ω = 0) (hη : d₁ η = 0)
    (hsum : d₁ (ω + η) = 0) :
    closedClass d₀ d₁ hdd (ω + η) hsum =
      closedClass d₀ d₁ hdd ω hω +
        closedClass d₀ d₁ hdd η hη := by
  change Submodule.Quotient.mk (⟨ω + η, hsum⟩ : LinearMap.ker d₁) =
    Submodule.Quotient.mk (⟨ω, hω⟩ : LinearMap.ker d₁) +
      Submodule.Quotient.mk (⟨η, hη⟩ : LinearMap.ker d₁)
  rw [← Submodule.Quotient.mk_add]
  rfl

theorem closedClass_smul
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0)
    (r : R) (ω : Ω₁) (hω : d₁ ω = 0)
    (hsmul : d₁ (r • ω) = 0) :
    closedClass d₀ d₁ hdd (r • ω) hsmul =
      r • closedClass d₀ d₁ hdd ω hω := by
  change Submodule.Quotient.mk (⟨r • ω, hsmul⟩ : LinearMap.ker d₁) =
    r • Submodule.Quotient.mk (⟨ω, hω⟩ : LinearMap.ker d₁)
  rw [← Submodule.Quotient.mk_smul]
  rfl

theorem closedClass_neg
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0)
    (ω : Ω₁) (hω : d₁ ω = 0)
    (hneg : d₁ (-ω) = 0) :
    closedClass d₀ d₁ hdd (-ω) hneg =
      -closedClass d₀ d₁ hdd ω hω := by
  change Submodule.Quotient.mk (⟨-ω, hneg⟩ : LinearMap.ker d₁) =
    -Submodule.Quotient.mk (⟨ω, hω⟩ : LinearMap.ker d₁)
  rw [← Submodule.Quotient.mk_neg]
  rfl

/-! ## Period functionals descend to the algebraic cohomology quotient -/

def periodClassFactor
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[R] R)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0) :
    cohomologyModule d₀ d₁ hdd →ₗ[R] R :=
  ((LinearMap.range d₀).comap (LinearMap.ker d₁).subtype).liftQ
    (period.comp (LinearMap.ker d₁).subtype) (by
      intro x hx
      rw [Submodule.mem_comap, LinearMap.mem_range] at hx
      rcases hx with ⟨η, hη⟩
      change period ((LinearMap.ker d₁).subtype x) = 0
      rw [← hη]
      exact hperiod η)

theorem periodClassFactor_comp_cycleQuotientMap
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[R] R)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0) :
    (periodClassFactor d₀ d₁ hdd period hperiod).comp
        (cycleQuotientMap d₀ d₁ hdd) =
      period.comp (LinearMap.ker d₁).subtype := by
  let H := (LinearMap.range d₀).comap (LinearMap.ker d₁).subtype
  have hfactor : H ≤ (period.comp (LinearMap.ker d₁).subtype).ker := by
    intro x hx
    rw [Submodule.mem_comap, LinearMap.mem_range] at hx
    rcases hx with ⟨η, hη⟩
    change period ((LinearMap.ker d₁).subtype x) = 0
    rw [← hη]
    exact hperiod η
  change
    (H.liftQ (period.comp (LinearMap.ker d₁).subtype) hfactor).comp
        (Submodule.mkQ H) =
      period.comp (LinearMap.ker d₁).subtype
  exact Submodule.liftQ_mkQ H
    (period.comp (LinearMap.ker d₁).subtype) hfactor

theorem periodClassFactor_unique
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[R] R)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (g : cohomologyModule d₀ d₁ hdd →ₗ[R] R)
    (hg : g.comp (cycleQuotientMap d₀ d₁ hdd) =
      period.comp (LinearMap.ker d₁).subtype) :
    g = periodClassFactor d₀ d₁ hdd period hperiod := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := cycleQuotientMap_surjective d₀ d₁ hdd y
  have hgx := LinearMap.congr_fun hg x
  have hpx := LinearMap.congr_fun
    (periodClassFactor_comp_cycleQuotientMap
      d₀ d₁ hdd period hperiod) x
  simpa [LinearMap.comp_apply] using hgx.trans hpx.symm

theorem periodClassFactor_apply
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[R] R)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (ω : Ω₁) (hω : d₁ ω = 0) :
    periodClassFactor d₀ d₁ hdd period hperiod
        (closedClass d₀ d₁ hdd ω hω) = period ω := by
  change
    (((LinearMap.range d₀).comap (LinearMap.ker d₁).subtype).liftQ
      (period.comp (LinearMap.ker d₁).subtype) _) 
      (Submodule.Quotient.mk (⟨ω, hω⟩ : LinearMap.ker d₁)) = period ω
  exact Submodule.liftQ_apply
    ((LinearMap.range d₀).comap (LinearMap.ker d₁).subtype)
    (period.comp (LinearMap.ker d₁).subtype) ⟨ω, hω⟩

theorem periodClassFactor_closedClass_eq_zero_iff
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[R] R)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (ω : Ω₁) (hω : d₁ ω = 0) :
    periodClassFactor d₀ d₁ hdd period hperiod
        (closedClass d₀ d₁ hdd ω hω) = 0 ↔
      period ω = 0 := by
  rw [periodClassFactor_apply d₀ d₁ hdd period hperiod ω hω]

theorem periodClassFactor_closedClass_ne_zero_iff
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) (period : Ω₁ →ₗ[R] R)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (ω : Ω₁) (hω : d₁ ω = 0) :
    periodClassFactor d₀ d₁ hdd period hperiod
        (closedClass d₀ d₁ hdd ω hω) ≠ 0 ↔
      period ω ≠ 0 := by
  exact not_congr (periodClassFactor_closedClass_eq_zero_iff
    d₀ d₁ hdd period hperiod ω hω)

theorem exact_forms_are_closed
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) (η : Ω₀) :
    d₁ (d₀ η) = 0 := by
  exact LinearMap.congr_fun hdd η

theorem exact_form_class_eq_zero
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) (η : Ω₀) :
    closedClass d₀ d₁ hdd (d₀ η) (exact_forms_are_closed d₀ d₁ hdd η) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).2
  rw [Submodule.mem_comap, LinearMap.mem_range]
  exact ⟨η, rfl⟩

theorem closedClass_eq_zero_iff
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) (ω : Ω₁) (hω : d₁ ω = 0) :
    closedClass d₀ d₁ hdd ω hω = 0 ↔
      (⟨ω, hω⟩ : LinearMap.ker d₁) ∈
        (LinearMap.range d₀).comap (LinearMap.ker d₁).subtype := by
  change Submodule.Quotient.mk (⟨ω, hω⟩ : LinearMap.ker d₁) = 0 ↔ _
  exact Submodule.Quotient.mk_eq_zero _

theorem closedClass_ne_zero_of_period_ne_zero
    (d₀ : Ω₀ →ₗ[R] Ω₁) (d₁ : Ω₁ →ₗ[R] Ω₂)
    (hdd : d₁.comp d₀ = 0) (ω : Ω₁) (hω : d₁ ω = 0)
    (period : Ω₁ →ₗ[R] R)
    (hperiod : ∀ η : Ω₀, period (d₀ η) = 0)
    (hωperiod : period ω ≠ 0) :
    closedClass d₀ d₁ hdd ω hω ≠ 0 := by
  intro hzero
  have hmem : (⟨ω, hω⟩ : LinearMap.ker d₁) ∈
      (LinearMap.range d₀).comap (LinearMap.ker d₁).subtype :=
    (Submodule.Quotient.mk_eq_zero _).mp hzero
  rw [Submodule.mem_comap, LinearMap.mem_range] at hmem
  rcases hmem with ⟨η, hη⟩
  have hscalar : d₀ η = ω := by simpa using hη
  apply hωperiod
  rw [← hscalar]
  exact hperiod η

/-! ## Concrete finite logarithmic-period readout

This is the smallest finite complex carrying the already-proved Klein period:
both differentials are zero and the middle object is the scalar period
readout `ℂ`.  It is intentionally a readout complex, not a claim that the
classical manifold de Rham complex has been constructed here.
-/

def kleinZeroD₀ : ℂ →ₗ[ℂ] ℂ := 0

def kleinZeroD₁ : ℂ →ₗ[ℂ] ℂ := 0

theorem kleinZeroD_complex :
    kleinZeroD₁.comp kleinZeroD₀ = 0 := by
  simp [kleinZeroD₀, kleinZeroD₁]

def kleinLogPeriodReadoutClass (R : ℝ) :
    cohomologyModule kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex :=
  closedClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (LogDeRhamClass.logarithmicPeriod R) (by simp [kleinZeroD₁])

def kleinLogPeriodReadoutWindingClass (R : ℝ) (n : ℤ) :
    cohomologyModule kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex :=
  closedClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    ((n : ℂ) * LogDeRhamClass.logarithmicPeriod R) (by simp [kleinZeroD₁])

theorem kleinLogPeriodReadoutWindingClass_eq_int_smul
    (R : ℝ) (n : ℤ) :
    kleinLogPeriodReadoutWindingClass R n =
      (n : ℂ) • kleinLogPeriodReadoutClass R := by
  unfold kleinLogPeriodReadoutWindingClass kleinLogPeriodReadoutClass
  change
    closedClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        ((n : ℂ) • LogDeRhamClass.logarithmicPeriod R) _ =
      (n : ℂ) • closedClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LogDeRhamClass.logarithmicPeriod R) _
  rw [closedClass_smul]

theorem kleinLogPeriodReadoutWindingClass_eq_zero_iff
    (R : ℝ) (n : ℤ) :
    kleinLogPeriodReadoutWindingClass R n = 0 ↔
      (n : ℂ) * LogDeRhamClass.logarithmicPeriod R = 0 := by
  unfold kleinLogPeriodReadoutWindingClass
  change
    Submodule.Quotient.mk
        (⟨(n : ℂ) * LogDeRhamClass.logarithmicPeriod R,
          by simp [kleinZeroD₁]⟩ : LinearMap.ker kleinZeroD₁) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h
    rw [Submodule.mem_comap, LinearMap.mem_range] at h
    rcases h with ⟨η, hη⟩
    simpa [kleinZeroD₀] using hη
  · intro h
    rw [Submodule.mem_comap, LinearMap.mem_range]
    refine ⟨0, ?_⟩
    simp [kleinZeroD₀, h]

theorem kleinLogPeriodReadoutWindingClass_ne_zero
    (R : ℝ) (hR : 0 < R) (n : ℤ) (hn : n ≠ 0) :
    kleinLogPeriodReadoutWindingClass R n ≠ 0 := by
  apply closedClass_ne_zero_of_period_ne_zero
    kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    ((n : ℂ) * LogDeRhamClass.logarithmicPeriod R)
    (by simp [kleinZeroD₁])
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
  · intro η
    simp [kleinZeroD₀]
  · exact mul_ne_zero (by exact_mod_cast hn)
      (LogDeRhamClass.logarithmicPeriod_ne_zero R hR)

theorem kleinLogPeriodReadoutWindingClass_ne_zero_iff
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    kleinLogPeriodReadoutWindingClass R n ≠ 0 ↔ n ≠ 0 := by
  constructor
  · intro h hn
    subst n
    apply h
    unfold kleinLogPeriodReadoutWindingClass
    convert exact_form_class_eq_zero kleinZeroD₀ kleinZeroD₁
      kleinZeroD_complex 0 using 1 <;> simp [kleinZeroD₀]
  · intro hn
    exact kleinLogPeriodReadoutWindingClass_ne_zero R hR n hn

theorem kleinLogPeriodReadoutWindingClass_zero
    (R : ℝ) :
    kleinLogPeriodReadoutWindingClass R 0 = 0 := by
  rw [kleinLogPeriodReadoutWindingClass_eq_int_smul]
  simp

theorem kleinLogPeriodReadoutWindingClass_add
    (R : ℝ) (m n : ℤ) :
    kleinLogPeriodReadoutWindingClass R (m + n) =
      kleinLogPeriodReadoutWindingClass R m +
        kleinLogPeriodReadoutWindingClass R n := by
  rw [kleinLogPeriodReadoutWindingClass_eq_int_smul,
    kleinLogPeriodReadoutWindingClass_eq_int_smul,
    kleinLogPeriodReadoutWindingClass_eq_int_smul]
  simp only [Int.cast_add, add_smul]

def kleinLogPeriodReadoutWindingAddHom (R : ℝ) :
    ℤ →+ cohomologyModule kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex where
  toFun n := kleinLogPeriodReadoutWindingClass R n
  map_zero' := kleinLogPeriodReadoutWindingClass_zero R
  map_add' m n := kleinLogPeriodReadoutWindingClass_add R m n

@[simp]
theorem kleinLogPeriodReadoutWindingAddHom_apply
    (R : ℝ) (n : ℤ) :
    kleinLogPeriodReadoutWindingAddHom R n =
      kleinLogPeriodReadoutWindingClass R n :=
  rfl

theorem kleinLogPeriodReadoutWindingClass_neg
    (R : ℝ) (n : ℤ) :
    kleinLogPeriodReadoutWindingClass R (-n) =
      -kleinLogPeriodReadoutWindingClass R n := by
  rw [kleinLogPeriodReadoutWindingClass_eq_int_smul,
    kleinLogPeriodReadoutWindingClass_eq_int_smul]
  simp only [Int.cast_neg, neg_smul]

theorem kleinLogPeriodReadoutWindingClass_injective
    (R : ℝ) (hR : 0 < R) :
    Function.Injective (kleinLogPeriodReadoutWindingClass R) := by
  intro m n hmn
  by_contra hne
  have hdiff : m - n ≠ 0 := sub_ne_zero.mpr hne
  have hclass :
      kleinLogPeriodReadoutWindingClass R (m - n) ≠ 0 :=
    (kleinLogPeriodReadoutWindingClass_ne_zero_iff R hR (m - n)).2 hdiff
  apply hclass
  calc
    kleinLogPeriodReadoutWindingClass R (m - n) =
        kleinLogPeriodReadoutWindingClass R m +
          kleinLogPeriodReadoutWindingClass R (-n) := by
      rw [sub_eq_add_neg, kleinLogPeriodReadoutWindingClass_add]
    _ = kleinLogPeriodReadoutWindingClass R m -
          kleinLogPeriodReadoutWindingClass R n := by
      rw [kleinLogPeriodReadoutWindingClass_neg]
      rfl
    _ = 0 := by rw [hmn, sub_self]

theorem kleinLogPeriodReadoutWindingAddHom_injective
    (R : ℝ) (hR : 0 < R) :
    Function.Injective (kleinLogPeriodReadoutWindingAddHom R) := by
  simpa only [kleinLogPeriodReadoutWindingAddHom_apply] using
    kleinLogPeriodReadoutWindingClass_injective R hR

theorem kleinLogPeriodReadoutClass_ne_zero
    (R : ℝ) (hR : 0 < R) :
    kleinLogPeriodReadoutClass R ≠ 0 := by
  apply closedClass_ne_zero_of_period_ne_zero
    kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (LogDeRhamClass.logarithmicPeriod R)
    (by simp [kleinZeroD₁])
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
  · intro η
    simp [kleinZeroD₀]
  · exact LogDeRhamClass.logarithmicPeriod_ne_zero R hR

theorem kleinZeroPeriodClassFactor_surjective :
    Function.Surjective
      (periodClassFactor kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])) := by
  intro z
  refine ⟨closedClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
      z (by simp [kleinZeroD₁]), ?_⟩
  exact periodClassFactor_apply kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
    (by intro η; simp [kleinZeroD₀]) z (by simp [kleinZeroD₁])

theorem kleinZeroPeriodClassFactor_injective :
    Function.Injective
      (periodClassFactor kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])) := by
  intro x y hxy
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro x y hxy
  have hxy' : (x : ℂ) = (y : ℂ) := by
    change
      periodClassFactor kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
          (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
          (by intro η; simp [kleinZeroD₀])
          (closedClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
            (x : ℂ) (by simp [kleinZeroD₁])) =
        periodClassFactor kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
          (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
          (by intro η; simp [kleinZeroD₀])
          (closedClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
            (y : ℂ) (by simp [kleinZeroD₁])) at hxy
    simpa only [periodClassFactor_apply] using hxy
  apply Quotient.sound
  rw [Subtype.ext hxy']
  simp

theorem kleinZeroPeriodClassFactor_bijective :
    Function.Bijective
      (periodClassFactor kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀])) :=
  ⟨kleinZeroPeriodClassFactor_injective,
    kleinZeroPeriodClassFactor_surjective⟩

noncomputable def kleinZeroCohomologyEquiv :
    cohomologyModule kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective
    (periodClassFactor kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
      (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
      (by intro η; simp [kleinZeroD₀]))
    kleinZeroPeriodClassFactor_bijective

@[simp] theorem kleinZeroCohomologyEquiv_apply
    (x : cohomologyModule kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex) :
    kleinZeroCohomologyEquiv x =
      periodClassFactor kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
        (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
        (by intro η; simp [kleinZeroD₀]) x := rfl

theorem kleinZeroCohomologyEquiv_logarithmicPeriod (R : ℝ) :
    kleinZeroCohomologyEquiv (kleinLogPeriodReadoutClass R) =
      LogDeRhamClass.logarithmicPeriod R := by
  rw [kleinZeroCohomologyEquiv_apply]
  exact periodClassFactor_apply kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
    (by intro η; simp [kleinZeroD₀])
    (LogDeRhamClass.logarithmicPeriod R) (by simp [kleinZeroD₁])

theorem kleinZeroCohomologyEquiv_windingPeriod (R : ℝ) (n : ℤ) :
    kleinZeroCohomologyEquiv (kleinLogPeriodReadoutWindingClass R n) =
      (n : ℂ) * LogDeRhamClass.logarithmicPeriod R := by
  rw [kleinZeroCohomologyEquiv_apply]
  exact periodClassFactor_apply kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
    (by intro η; simp [kleinZeroD₀])
    ((n : ℂ) * LogDeRhamClass.logarithmicPeriod R) (by simp [kleinZeroD₁])

theorem kleinLogPeriodReadoutClass_eq_zero_iff (R : ℝ) :
    kleinLogPeriodReadoutClass R = 0 ↔
      LogDeRhamClass.logarithmicPeriod R = 0 := by
  constructor
  · intro h
    have h' := congrArg kleinZeroCohomologyEquiv h
    rw [map_zero, kleinZeroCohomologyEquiv_logarithmicPeriod] at h'
    exact h'
  · intro h
    unfold kleinLogPeriodReadoutClass
    rw [h]
    exact exact_form_class_eq_zero kleinZeroD₀ kleinZeroD₁
      kleinZeroD_complex 0

theorem kleinLogPeriodReadoutClass_ne_zero_iff (R : ℝ) :
    kleinLogPeriodReadoutClass R ≠ 0 ↔
      LogDeRhamClass.logarithmicPeriod R ≠ 0 := by
  exact not_congr (kleinLogPeriodReadoutClass_eq_zero_iff R)

end
end InfoGeometry.Projective.KleinQuadric.DeRhamComplex
