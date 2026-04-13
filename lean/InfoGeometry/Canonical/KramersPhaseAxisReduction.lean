import InfoGeometry.Canonical.TimeReversalKramers
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.KramersPhaseAxisReduction

Reduction/factorization criteria between:
- abstract doubled-carrier Kramers symmetries `Θ`, and
- the intrinsic Hestenes phase axis `K = J ∘ ε`.

This file answers the missing capstone question:
when does `Θ` reduce to `K`, and when is it genuinely more general?
-/

namespace InfoGeometry.Canonical.KramersPhaseAxisReduction

open InfoGeometry.Krein
open InfoGeometry.Canonical.HestenesRealStructures
open InfoGeometry.Canonical.OperatorDictionary
open InfoGeometry.Canonical.BogoliubovTransport

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Canonical right factor against the internal phase axis `K`: `R_A := -(A ∘ K)`. -/
@[rep_depth krein]
noncomputable def phaseAxisRightFactor (A : EndH) : EndH :=
  -(A.comp (phaseAxisK (E := E)))

/--
Exact right-factor identity:
`R_A ∘ K = A`.
-/
@[rep_depth krein]
theorem phaseAxisRightFactor_comp_phaseAxis_eq (A : EndH) :
    (phaseAxisRightFactor (E := E) A).comp (phaseAxisK (E := E)) = A := by
  unfold phaseAxisRightFactor
  calc
    (-(A.comp (phaseAxisK (E := E)))).comp (phaseAxisK (E := E))
        = -((A.comp (phaseAxisK (E := E))).comp (phaseAxisK (E := E))) := by
            simp
    _ = -(A.comp ((phaseAxisK (E := E)).comp (phaseAxisK (E := E)))) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = -(A.comp (-(ContinuousLinearMap.id ℝ H₂))) := by
          rw [phaseAxisK_sq_eq_neg_id (E := E)]
    _ = A := by simp

/--
Uniqueness of the canonical right factor through the internal phase axis `K`.

If `R ∘ K = A`, then necessarily `R = -(A ∘ K)`.
-/
@[rep_depth krein]
theorem phaseAxisRightFactor_unique
    (A R : EndH)
    (hRK : R.comp (phaseAxisK (E := E)) = A) :
    R = phaseAxisRightFactor (E := E) A := by
  apply ContinuousLinearMap.ext
  intro x
  have hK2x : (phaseAxisK (E := E)) ((phaseAxisK (E := E)) x) = -x := by
    exact congrArg (fun F : EndH => F x) (phaseAxisK_sq_eq_neg_id (E := E))
  have hRKK : R ((phaseAxisK (E := E)) ((phaseAxisK (E := E)) x)) = -(R x) := by
    simpa using congrArg R hK2x
  calc
    R x = -(-(R x)) := by simp
    _ = -(R ((phaseAxisK (E := E)) ((phaseAxisK (E := E)) x))) := by rw [hRKK]
    _ = -((R.comp (phaseAxisK (E := E))) ((phaseAxisK (E := E)) x)) := by rfl
    _ = -(A ((phaseAxisK (E := E)) x)) := by rw [hRK]
    _ = phaseAxisRightFactor (E := E) A x := by rfl

/--
Every abstract Kramers symmetry factors through the intrinsic phase axis `K`
via the canonical right factor.
-/
@[rep_depth krein]
theorem kramers_factor_through_phaseAxis
    (S : KramersSymmetry (E := E)) :
    ∃ R : EndH, S.Θ = R.comp (phaseAxisK (E := E)) := by
  refine ⟨phaseAxisRightFactor (E := E) S.Θ, ?_⟩
  symm
  exact phaseAxisRightFactor_comp_phaseAxis_eq (E := E) S.Θ

/--
Canonicality of the factorization:
any right factorization of `Θ` through `K` equals the canonical right factor.
-/
@[rep_depth krein]
theorem kramers_factor_through_phaseAxis_unique
    (S : KramersSymmetry (E := E))
    {R : EndH}
    (hR : S.Θ = R.comp (phaseAxisK (E := E))) :
    R = phaseAxisRightFactor (E := E) S.Θ := by
  exact phaseAxisRightFactor_unique (E := E) S.Θ R hR.symm

/--
Canonical reduction package:
every Kramers symmetry has a unique right-factorization through `K`.
-/
@[rep_depth krein]
theorem kramers_unique_phaseAxis_factor
    (S : KramersSymmetry (E := E)) :
    ∃! R : EndH, S.Θ = R.comp (phaseAxisK (E := E)) := by
  refine ⟨phaseAxisRightFactor (E := E) S.Θ, ?_, ?_⟩
  · exact (phaseAxisRightFactor_comp_phaseAxis_eq (E := E) S.Θ).symm
  · intro R hR
    exact kramers_factor_through_phaseAxis_unique (E := E) (S := S) hR

/--
Capstone API name: the canonical phase-reduction equation
`Θ = R ∘ K` for `R := -(Θ ∘ K)`.
-/
@[rep_depth krein]
theorem theta_eq_R_comp_phaseAxisK_of_phaseReduction
    (S : KramersSymmetry (E := E)) :
    S.Θ =
      (phaseAxisRightFactor (E := E) S.Θ).comp (phaseAxisK (E := E)) := by
  simpa using
    (phaseAxisRightFactor_comp_phaseAxis_eq (E := E) S.Θ).symm

/--
Capstone API name: uniqueness of phase reduction through `K`.
-/
@[rep_depth krein]
theorem phaseReduction_unique_of_commute_phaseAxisK
    (S : KramersSymmetry (E := E))
    {R₁ R₂ : EndH}
    (hR₁ : S.Θ = R₁.comp (phaseAxisK (E := E)))
    (hR₂ : S.Θ = R₂.comp (phaseAxisK (E := E))) :
    R₁ = R₂ := by
  have h1 :
      R₁ = phaseAxisRightFactor (E := E) S.Θ :=
    kramers_factor_through_phaseAxis_unique (E := E) (S := S) hR₁
  have h2 :
      R₂ = phaseAxisRightFactor (E := E) S.Θ :=
    kramers_factor_through_phaseAxis_unique (E := E) (S := S) hR₂
  calc
    R₁ = phaseAxisRightFactor (E := E) S.Θ := h1
    _ = R₂ := h2.symm

/--
Capstone API name: abstract Kramers action equals intrinsic phase partner iff
the underlying operator equals `K`.
-/
@[rep_depth krein]
theorem abstract_kramers_eq_intrinsic_phase_partner_iff
    (S : KramersSymmetry (E := E)) :
    (∀ u : H₂, S.Θ u = phaseAxisK (E := E) u)
      ↔
    S.Θ = phaseAxisK (E := E) := by
  constructor
  · intro h
    exact ContinuousLinearMap.ext h
  · intro h u
    simpa [h]

/--
Capstone API name: if abstract Kramers action does not reduce to the intrinsic
phase axis, then it diverges pointwise from it on at least one vector.
-/
@[rep_depth krein]
theorem abstract_kramers_diverges_from_intrinsic_of_not_phaseReduction
    (S : KramersSymmetry (E := E))
    (hNe : S.Θ ≠ phaseAxisK (E := E)) :
    ∃ u : H₂, S.Θ u ≠ phaseAxisK (E := E) u := by
  by_contra hNo
  have hAll : ∀ u : H₂, S.Θ u = phaseAxisK (E := E) u := by
    intro u
    by_contra hu
    exact hNo ⟨u, hu⟩
  exact hNe ((abstract_kramers_eq_intrinsic_phase_partner_iff (E := E) S).1 hAll)

/--
Single capstone package for abstract-vs-intrinsic Kramers comparison:
1. unique right factorization through `K`,
2. exact criterion for equality with the intrinsic phase axis,
3. pointwise divergence witness when reduction fails.
-/
@[rep_depth krein]
theorem abstract_kramers_phaseReduction_package
    (S : KramersSymmetry (E := E)) :
    (∃! R : EndH, S.Θ = R.comp (phaseAxisK (E := E)))
      ∧
    ((∀ u : H₂, S.Θ u = phaseAxisK (E := E) u)
      ↔
    S.Θ = phaseAxisK (E := E))
      ∧
    (S.Θ ≠ phaseAxisK (E := E) →
      ∃ u : H₂, S.Θ u ≠ phaseAxisK (E := E) u) := by
  refine ⟨kramers_unique_phaseAxis_factor (E := E) S, ?_, ?_⟩
  · exact abstract_kramers_eq_intrinsic_phase_partner_iff (E := E) S
  · intro hNe
    exact abstract_kramers_diverges_from_intrinsic_of_not_phaseReduction
      (E := E) S hNe

/--
An operator that is both `K`-linear and `K`-antilinear is forced to zero.
-/
@[rep_depth krein]
theorem eq_zero_of_kLinear_and_kAntilinear
    {A : EndH}
    (hLin : KLinear (E := E) A)
    (hAnti : KAntilinear (E := E) A) :
    A = 0 := by
  let K := phaseAxisK (E := E)
  have hComm : A.comp K = K.comp A := hLin
  have hAntiEq : A.comp K = -(K.comp A) := hAnti
  have hKAEq : K.comp A = -(K.comp A) := by
    calc
      K.comp A = A.comp K := hComm.symm
      _ = -(K.comp A) := hAntiEq
  apply ContinuousLinearMap.ext
  intro x
  have hKAEqApply : K (A x) = -(K (A x)) := by
    exact congrArg (fun F : EndH => F x) hKAEq
  have hApplyZero : K (A x) = 0 := by
    have hSum : K (A x) + K (A x) = 0 := by
      exact (eq_neg_iff_add_eq_zero.mp hKAEqApply)
    have hTwo : (2 : ℝ) • (K (A x)) = 0 := by
      simpa [two_smul] using hSum
    exact (smul_eq_zero.mp hTwo).resolve_left (by norm_num)
  have hK2Apply : K (K (A x)) = -(A x) := by
    exact congrArg (fun F : EndH => F (A x)) (phaseAxisK_sq_eq_neg_id (E := E))
  have hNegAx : -(A x) = 0 := by
    calc
      -(A x) = K (K (A x)) := by simpa using hK2Apply.symm
      _ = K 0 := by rw [hApplyZero]
      _ = 0 := by simp
  exact neg_eq_zero.mp hNegAx

/--
No nontrivial Kramers symmetry can reduce to a scalar multiple of the intrinsic
phase axis `K`.
-/
@[rep_depth krein]
theorem kramers_not_scalar_multiple_phaseAxis
    [Nontrivial H₂]
    (S : KramersSymmetry (E := E))
    (c : ℝ) :
    S.Θ ≠ c • (phaseAxisK (E := E)) := by
  have hThetaNeZero : S.Θ ≠ 0 := by
    intro hThetaZero
    rcases exists_ne (0 : H₂) with ⟨x, hx⟩
    have hApply : (S.Θ.comp S.Θ) x = (-(ContinuousLinearMap.id ℝ H₂) : EndH) x := by
      exact congrArg (fun F : EndH => F x) S.square_neg
    have hZeroNeg : 0 = -x := by
      simpa [hThetaZero] using hApply
    have hNegZero : -x = 0 := by simpa [eq_comm] using hZeroNeg
    have hxZero : x = 0 := neg_eq_zero.mp hNegZero
    exact hx hxZero
  intro hEq
  have hPhaseLinear : KLinear (E := E) S.Θ := by
    rw [hEq]
    unfold KLinear IsPhaseLinear
    simpa [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul] using
      congrArg (fun T : EndH => (c : ℝ) • T) (phaseAxisK_isKLinear (E := E))
  have hZeroTheta : S.Θ = 0 :=
    eq_zero_of_kLinear_and_kAntilinear
      (E := E) hPhaseLinear S.phaseAntilinear
  exact hThetaNeZero hZeroTheta

/--
In nontrivial doubled carriers, a Kramers symmetry cannot be simultaneously
`K`-linear and `K`-antilinear.
-/
@[rep_depth krein]
theorem kramers_not_kLinear
    [Nontrivial H₂]
    (S : KramersSymmetry (E := E)) :
    ¬ KLinear (E := E) S.Θ := by
  intro hLin
  have hZero : S.Θ = 0 :=
    eq_zero_of_kLinear_and_kAntilinear (E := E) hLin S.phaseAntilinear
  rcases exists_ne (0 : H₂) with ⟨x, hx⟩
  have hApply : (S.Θ.comp S.Θ) x = (-(ContinuousLinearMap.id ℝ H₂) : EndH) x := by
    exact congrArg (fun F : EndH => F x) S.square_neg
  have hZeroNeg : 0 = -x := by
    simpa [hZero] using hApply
  have hxZero : x = 0 := by
    exact neg_eq_zero.mp (by simpa [eq_comm] using hZeroNeg)
  exact hx hxZero

/--
No scalar collapse to the intrinsic phase axis:
`Θ` cannot equal `c • K` for any real scalar `c`.
-/
@[rep_depth krein]
theorem kramers_no_scalar_phaseAxis_collapse
    [Nontrivial H₂]
    (S : KramersSymmetry (E := E)) :
    ¬ ∃ c : ℝ, S.Θ = c • (phaseAxisK (E := E)) := by
  intro h
  rcases h with ⟨c, hc⟩
  exact (kramers_not_scalar_multiple_phaseAxis (E := E) (S := S) c) hc

end Core

end InfoGeometry.Canonical.KramersPhaseAxisReduction
