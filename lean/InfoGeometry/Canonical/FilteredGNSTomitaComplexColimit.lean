import InfoGeometry.Canonical.FilteredGNSTomitaModularFormColimit

/-!
# Complex structure and sesquilinear Tomita form on the filtered colimit

The closed-domain direct limit was first constructed over `ℝ`, because the
closed Tomita operator itself is conjugate-linear.  Nevertheless, complex
scalar multiplication at every stage commutes with all transition maps.
This file descends those scalar operators through the genuine module direct
limit, proves the complex module laws, and upgrades the descended modular form
from its real-bilinear carrier to a genuine complex sesquilinear map.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaComplexColimit

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
open CStarStateColimit.Native.FilteredGNSTomitaClosedTransport
open CStarStateColimit.Native.FilteredGNSTomitaModularForm
open CStarStateColimit.Native.FilteredGNSTomitaModularFormColimit

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      Stage sys)
variable
  (hclos :
    ∀ i, IsClosableTomitaCore (ω.state i))

/-- Complex scalar multiplication on one closed stage, viewed as a real-linear
operator. -/
def stageComplexScalarMap
    (c : ℂ) (i : I) :
    closedTomitaDomain (ω.state i) →ₗ[ℝ]
      closedTomitaDomain (ω.state i) where
  toFun := fun x => c • x
  map_add' := smul_add c
  map_smul' := by
    intro r x
    change c • ((r : ℂ) • x) = (r : ℂ) • (c • x)
    simp only [smul_smul]
    rw [mul_comm]

/-- Closed-domain transitions commute with the original complex scalar
action. -/
theorem domainTransition_smul_complex
    {i j : I} (hij : i ≤ j)
    (c : ℂ) (x : closedTomitaDomain (ω.state i)) :
    domainTransition Stage sys ω hij (c • x) =
      c • domainTransition Stage sys ω hij x := by
  exact
    (filteredClosedTomitaDomainMap
      Stage sys ω hij).map_smul c x

/-- Stage scalar multiplication followed by the canonical direct-limit
inclusion. -/
def complexScalarCoconeMap
    (c : ℂ) (i : I) :
    closedTomitaDomain (ω.state i) →ₗ[ℝ]
      ClosedDomainDirectLimit Stage sys ω :=
  (Module.DirectLimit.of
    ℝ I
    (fun k => closedTomitaDomain (ω.state k))
    (fun _ _ h => domainTransition Stage sys ω h)
    i).comp
      (stageComplexScalarMap Stage sys ω c i)

/-- The scalar-multiplied stage inclusions form a cocone. -/
theorem complexScalarCoconeMap_compatible
    (c : ℂ) (i j : I) (hij : i ≤ j)
    (x : closedTomitaDomain (ω.state i)) :
    complexScalarCoconeMap Stage sys ω c j
        (domainTransition Stage sys ω hij x) =
      complexScalarCoconeMap Stage sys ω c i x := by
  change
    Module.DirectLimit.of
        ℝ I
        (fun k => closedTomitaDomain (ω.state k))
        (fun _ _ h => domainTransition Stage sys ω h)
        j
        (c • domainTransition Stage sys ω hij x) =
      Module.DirectLimit.of
        ℝ I
        (fun k => closedTomitaDomain (ω.state k))
        (fun _ _ h => domainTransition Stage sys ω h)
        i (c • x)
  rw [← domainTransition_smul_complex
    Stage sys ω hij c x]
  exact Module.DirectLimit.of_f

/-- Complex scalar multiplication descended to the real filtered direct-limit
carrier. -/
def complexScalarDirectLimit
    (c : ℂ) :
    ClosedDomainDirectLimit Stage sys ω →ₗ[ℝ]
      ClosedDomainDirectLimit Stage sys ω :=
  Module.DirectLimit.lift
    ℝ I
    (fun i => closedTomitaDomain (ω.state i))
    (fun _ _ hij => domainTransition Stage sys ω hij)
    (complexScalarCoconeMap Stage sys ω c)
    (complexScalarCoconeMap_compatible Stage sys ω c)

@[simp] theorem complexScalarDirectLimit_of
    (c : ℂ) (i : I)
    (x : closedTomitaDomain (ω.state i)) :
    complexScalarDirectLimit Stage sys ω c
        (Module.DirectLimit.of
          ℝ I
          (fun k => closedTomitaDomain (ω.state k))
          (fun _ _ h => domainTransition Stage sys ω h)
          i x) =
      Module.DirectLimit.of
        ℝ I
        (fun k => closedTomitaDomain (ω.state k))
        (fun _ _ h => domainTransition Stage sys ω h)
        i (c • x) := by
  simpa only [complexScalarCoconeMap,
    stageComplexScalarMap] using
    (Module.DirectLimit.lift_of
      (g := complexScalarCoconeMap Stage sys ω c)
      (complexScalarCoconeMap_compatible Stage sys ω c)
      (i := i) x)

/-- The descended complex scalar operation. -/
noncomputable instance complexSMulClosedDomainDirectLimit :
    SMul ℂ (ClosedDomainDirectLimit Stage sys ω) where
  smul c := complexScalarDirectLimit Stage sys ω c

@[simp] theorem complex_smul_of
    (c : ℂ) (i : I)
    (x : closedTomitaDomain (ω.state i)) :
    c •
        (Module.DirectLimit.of
          ℝ I
          (fun k => closedTomitaDomain (ω.state k))
          (fun _ _ h => domainTransition Stage sys ω h)
          i x) =
      Module.DirectLimit.of
        ℝ I
        (fun k => closedTomitaDomain (ω.state k))
        (fun _ _ h => domainTransition Stage sys ω h)
        i (c • x) :=
  complexScalarDirectLimit_of Stage sys ω c i x

/-- Native distributive complex action on the filtered colimit. -/
noncomputable instance complexDistribMulActionClosedDomainDirectLimit :
    DistribMulAction ℂ (ClosedDomainDirectLimit Stage sys ω) where
  smul := (· • ·)
  one_smul := by
    intro z
    induction z using Module.DirectLimit.induction_on with
    | ih i x => simp
  mul_smul := by
    intro c d z
    induction z using Module.DirectLimit.induction_on with
    | ih i x => simp [mul_smul]
  smul_zero := by
    intro c
    exact (complexScalarDirectLimit Stage sys ω c).map_zero
  smul_add := by
    intro c x y
    exact (complexScalarDirectLimit Stage sys ω c).map_add x y

/-- The filtered real carrier recovers its native complex module structure. -/
noncomputable instance complexModuleClosedDomainDirectLimit :
    Module ℂ (ClosedDomainDirectLimit Stage sys ω) where
  add_smul := by
    intro c d z
    induction z using Module.DirectLimit.induction_on with
    | ih i x => simp [add_smul]
  zero_smul := by
    intro z
    induction z using Module.DirectLimit.induction_on with
    | ih i x => simp

/-- The descended real scalar action agrees with restriction of the new
complex action. -/
theorem real_smul_eq_complex_smul
    (r : ℝ) (z : ClosedDomainDirectLimit Stage sys ω) :
    r • z = (r : ℂ) • z := by
  induction z using Module.DirectLimit.induction_on with
  | ih i x =>
      rw [complex_smul_of]
      exact
        ((Module.DirectLimit.of
          ℝ I
          (fun k => closedTomitaDomain (ω.state k))
          (fun _ _ h => domainTransition Stage sys ω h)
          i).map_smul r x).symm

/-- Complex conjugate homogeneity of the common-stage pairing in its first
argument. -/
theorem commonStageModularPairing_smul_left_complex
    (i j : I) (c : ℂ)
    (x : closedTomitaDomain (ω.state i))
    (y : closedTomitaDomain (ω.state j)) :
    commonStageModularPairing Stage sys ω hclos i j
        (c • x) y =
      star c *
        commonStageModularPairing Stage sys ω hclos i j x y := by
  unfold commonStageModularPairing
  rw [domainTransition_smul_complex]
  have h :=
    (closedTomitaModularForm
      Stage sys ω hclos (commonUpper i j)).map_smulₛₗ c
      (domainTransition Stage sys ω
        (le_commonUpper_left i j) x)
  have happ :=
    LinearMap.congr_fun h
      (domainTransition Stage sys ω
        (le_commonUpper_right i j) y)
  simpa only [LinearMap.smul_apply, smul_eq_mul] using happ

/-- Complex homogeneity of the common-stage pairing in its second argument. -/
theorem commonStageModularPairing_smul_right_complex
    (i j : I) (c : ℂ)
    (x : closedTomitaDomain (ω.state i))
    (y : closedTomitaDomain (ω.state j)) :
    commonStageModularPairing Stage sys ω hclos i j
        x (c • y) =
      c *
        commonStageModularPairing Stage sys ω hclos i j x y := by
  unfold commonStageModularPairing
  rw [domainTransition_smul_complex]
  exact
    (closedTomitaModularForm Stage sys ω hclos
      (commonUpper i j)
      (domainTransition Stage sys ω
        (le_commonUpper_left i j) x)).map_smul c
      (domainTransition Stage sys ω
        (le_commonUpper_right i j) y)

/-- The descended form is conjugate-homogeneous in its first argument on all
direct-limit vectors. -/
theorem directLimitModularForm_smul_left_complex
    (c : ℂ)
    (z w : ClosedDomainDirectLimit Stage sys ω) :
    directLimitModularForm Stage sys ω hclos (c • z) w =
      star c *
        directLimitModularForm Stage sys ω hclos z w := by
  induction z using Module.DirectLimit.induction_on with
  | ih i x =>
      induction w using Module.DirectLimit.induction_on with
      | ih j y =>
          rw [complex_smul_of]
          rw [directLimitModularForm_of_of,
            directLimitModularForm_of_of]
          exact
            commonStageModularPairing_smul_left_complex
              Stage sys ω hclos i j c x y

/-- The descended form is complex-homogeneous in its second argument on all
direct-limit vectors. -/
theorem directLimitModularForm_smul_right_complex
    (c : ℂ)
    (z w : ClosedDomainDirectLimit Stage sys ω) :
    directLimitModularForm Stage sys ω hclos z (c • w) =
      c *
        directLimitModularForm Stage sys ω hclos z w := by
  induction z using Module.DirectLimit.induction_on with
  | ih i x =>
      induction w using Module.DirectLimit.induction_on with
      | ih j y =>
          rw [complex_smul_of]
          rw [directLimitModularForm_of_of,
            directLimitModularForm_of_of]
          exact
            commonStageModularPairing_smul_right_complex
              Stage sys ω hclos i j c x y

/-- The modular form on the filtered colimit, now bundled with its genuine
complex sesquilinear structure. -/
def complexDirectLimitModularForm :
    ClosedDomainDirectLimit Stage sys ω →ₛₗ[starRingEnd ℂ]
      ClosedDomainDirectLimit Stage sys ω →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ
    (starRingEnd ℂ) (RingHom.id ℂ)
    (fun z w =>
      directLimitModularForm Stage sys ω hclos z w)
    (by
      intro z₁ z₂ w
      exact
        LinearMap.congr_fun
          ((directLimitModularForm
            Stage sys ω hclos).map_add z₁ z₂) w)
    (by
      intro c z w
      simpa only [smul_eq_mul] using
        directLimitModularForm_smul_left_complex
          Stage sys ω hclos c z w)
    (by
      intro z w₁ w₂
      exact
        (directLimitModularForm
          Stage sys ω hclos z).map_add w₁ w₂)
    (by
      intro c z w
      simpa only [smul_eq_mul] using
        directLimitModularForm_smul_right_complex
          Stage sys ω hclos c z w)

@[simp] theorem complexDirectLimitModularForm_apply
    (z w : ClosedDomainDirectLimit Stage sys ω) :
    complexDirectLimitModularForm Stage sys ω hclos z w =
      directLimitModularForm Stage sys ω hclos z w :=
  rfl

/-- Positivity of the genuinely complex sesquilinear colimit form. -/
theorem complexDirectLimitModularForm_nonneg
    (z : ClosedDomainDirectLimit Stage sys ω) :
    0 ≤
      Complex.re
        (complexDirectLimitModularForm
          Stage sys ω hclos z z) := by
  rw [complexDirectLimitModularForm_apply]
  exact directLimitModularForm_nonneg Stage sys ω hclos z

/-- Hermitian symmetry of the complex colimit modular form. -/
theorem complexDirectLimitModularForm_conj_symm
    (z w : ClosedDomainDirectLimit Stage sys ω) :
    star
        (complexDirectLimitModularForm
          Stage sys ω hclos w z) =
      complexDirectLimitModularForm
        Stage sys ω hclos z w := by
  induction z using Module.DirectLimit.induction_on with
  | ih i x =>
      induction w using Module.DirectLimit.induction_on with
      | ih j y =>
          simp only [complexDirectLimitModularForm_apply,
            directLimitModularForm_of_of]
          let k := commonUpper i j
          rw [commonStageModularPairing_eq_at
            Stage sys ω hclos j i k
            (le_commonUpper_right i j)
            (le_commonUpper_left i j)]
          rw [commonStageModularPairing_eq_at
            Stage sys ω hclos i j k
            (le_commonUpper_left i j)
            (le_commonUpper_right i j)]
          exact inner_conj_symm _ _

end CStarStateColimit.Native.FilteredGNSTomitaComplexColimit
