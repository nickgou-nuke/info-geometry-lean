/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# CFC commutation for operator surprisal kernels

Continuous functional calculus values of one carrier commute.  This owner
closes only that algebraic step; it does not assert positivity, traces, or
Rényi differentiability.
-/

namespace InfoGeometry.Canonical.OperatorSurprisalCFCCommute

open InfoGeometry.OperatorAlgebra.NoncommutativeRenyi

variable {A : Type*}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem stateSurprisal_commutes_cfc (ρ : A) (f : ℝ → ℝ) :
    Commute (stateSurprisal ρ) (cfc f ρ) := by
  unfold stateSurprisal
  exact (cfc_commute_cfc Real.log f ρ).neg_left

omit [PartialOrder A] [StarOrderedRing A] in
/-- The real CFC logarithm of a positive two-sheet element has the expected
idempotent normal form.  The carrier remains an arbitrary C⋆-algebra; the
only spectral reduction is the `{0, 1}` spectrum of the self-adjoint
idempotent `P`. -/
theorem cfc_log_two_sheet (P : A) (hPstar : IsSelfAdjoint P)
    (hPid : P * P = P) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    cfc Real.log (p • P + q • (1 - P)) =
      Real.log p • P + Real.log q • (1 - P) := by
  let f : ℝ → ℝ := fun x => q + (p - q) * x
  have hPid' : IsIdempotentElem P := hPid
  have hspec : spectrum ℝ P ⊆ ({0, 1} : Set ℝ) :=
    (isIdempotentElem_iff_spectrum_subset ℝ P hPstar).mp hPid'
  have hf : ContinuousOn f (spectrum ℝ P) := by fun_prop
  have hlogf : ContinuousOn Real.log (f '' spectrum ℝ P) := by
    apply Real.continuousOn_log.mono
    rintro y ⟨x, hx, rfl⟩
    have hx01 := hspec hx
    rcases Set.mem_insert_iff.mp hx01 with h0 | hx01
    · simp [f, h0, ne_of_gt hq]
    · rcases Set.mem_singleton_iff.mp hx01 with h1
      simp [f, h1, ne_of_gt hp]
  have hρ : p • P + q • (1 - P) = cfc f P := by
    calc
      p • P + q • (1 - P) = q • (1 : A) + (p - q) • P := by module
      _ = cfc f P := by
        dsimp [f]
        rw [cfc_add P (fun _ => q) (fun x => (p - q) * x)
          (by fun_prop) (by fun_prop), cfc_const q P hPstar,
          cfc_const_mul_id (p - q) P hPstar]
        rw [Algebra.algebraMap_eq_smul_one]
  rw [hρ, ← cfc_comp' Real.log f P hlogf hf hPstar]
  have hcongr : (spectrum ℝ P).EqOn (Real.log ∘ f)
      (fun x => Real.log q + (Real.log p - Real.log q) * x) := by
    intro x hx
    have hx01 := hspec hx
    rcases Set.mem_insert_iff.mp hx01 with h0 | hx01
    · simp [Function.comp_apply, f, h0]
    · rcases Set.mem_singleton_iff.mp hx01 with h1
      have hf1 : f 1 = p := by dsimp [f]; ring
      rw [Function.comp_apply, h1, hf1]
      change Real.log p = Real.log q + (Real.log p - Real.log q) * 1
      rw [mul_one]
      ring
  change cfc (Real.log ∘ f) P = _
  rw [cfc_congr hcongr,
    cfc_add P (fun _ => Real.log q)
      (fun x => (Real.log p - Real.log q) * x)
      (by fun_prop) (by fun_prop),
    cfc_const (Real.log q) P hPstar,
    cfc_const_mul_id (Real.log p - Real.log q) P hPstar]
  have hnormal :
      algebraMap ℝ A (Real.log q) + (Real.log p - Real.log q) • P =
        Real.log p • P + Real.log q • (1 - P) := by
    rw [Algebra.algebraMap_eq_smul_one]
    module
  exact hnormal

omit [PartialOrder A] [StarOrderedRing A] in
/-- The CFC state surprisal `-cfc Real.log ρ` agrees with the algebraic
two-sheet surprisal coefficients when `ρ` is supported by a self-adjoint
idempotent cut. -/
theorem stateSurprisal_two_sheet (P : A) (hPstar : IsSelfAdjoint P)
    (hPid : P * P = P) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    stateSurprisal (p • P + q • (1 - P)) =
      (-Real.log p) • P + (-Real.log q) • (1 - P) := by
  unfold stateSurprisal
  rw [cfc_log_two_sheet P hPstar hPid p q hp hq]
  simp only [neg_add, neg_smul]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The relative CFC logarithm of two positive states supported on the same
self-adjoint idempotent cut is the difference of their sheet log weights.
This uses `log ρ - log σ`, the repository's noncommutative relative-log
convention; it does not identify that difference with `log (ρ * σ⁻¹)` for
general noncommuting inputs. -/
theorem relativeLogDensity_two_sheet (P : A) (hPstar : IsSelfAdjoint P)
    (hPid : P * P = P) (p q p₀ q₀ : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) :
    relativeLogDensity (p • P + q • (1 - P)) (p₀ • P + q₀ • (1 - P)) =
      Real.log (p / p₀) • P + Real.log (q / q₀) • (1 - P) := by
  unfold relativeLogDensity
  rw [cfc_log_two_sheet P hPstar hPid p q hp hq,
    cfc_log_two_sheet P hPstar hPid p₀ q₀ hp₀ hq₀,
    Real.log_div hp.ne' hp₀.ne', Real.log_div hq.ne' hq₀.ne']
  module

omit [PartialOrder A] [StarOrderedRing A] in
/-- On a shared two-sheet cut, the surprisal of the relative sheet weights is
the negative of the relative CFC log-density of the original states. -/
theorem stateSurprisal_relative_two_sheet (P : A)
    (hPstar : IsSelfAdjoint P) (hPid : P * P = P)
    (p q p₀ q₀ : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hp₀ : 0 < p₀) (hq₀ : 0 < q₀) :
    stateSurprisal ((p / p₀) • P + (q / q₀) • (1 - P)) =
      -relativeLogDensity (p • P + q • (1 - P))
        (p₀ • P + q₀ • (1 - P)) := by
  rw [stateSurprisal_two_sheet P hPstar hPid (p / p₀) (q / q₀)
      (div_pos hp hp₀) (div_pos hq hq₀),
    relativeLogDensity_two_sheet P hPstar hPid p q p₀ q₀ hp hq hp₀ hq₀]
  simp only [neg_add, neg_smul]

theorem cfc_log_commutes_rpow (ρ : A) (hρ : 0 ≤ ρ) (β : ℝ) :
    Commute (cfc Real.log ρ) (ρ ^ β) := by
  rw [CFC.rpow_eq_cfc_real hρ]
  exact cfc_commute_cfc Real.log (fun x : ℝ => x ^ β) ρ

theorem cfc_commutes_rpow (ρ : A) (hρ : 0 ≤ ρ) (f : ℝ → ℝ) (β : ℝ) :
    Commute (cfc f ρ) (ρ ^ β) := by
  rw [CFC.rpow_eq_cfc_real hρ]
  exact cfc_commute_cfc f (fun x : ℝ => x ^ β) ρ

theorem stateSurprisal_commutes_rpow (ρ : A) (hρ : 0 ≤ ρ) (β : ℝ) :
    Commute (stateSurprisal ρ) (ρ ^ β) := by
  unfold stateSurprisal
  exact (cfc_log_commutes_rpow ρ hρ β).neg_left

omit [PartialOrder A] [StarOrderedRing A] in
theorem stateSurprisal_isSelfAdjoint (ρ : A) :
    IsSelfAdjoint (stateSurprisal ρ) := by
  unfold stateSurprisal
  exact IsSelfAdjoint.cfc.neg

/-- Operator surprisal is natural under every complex star-algebra equivalence.
This gives the precise covariance statement for a change of operator-algebra
perspective; it does not assert that the observable is fixed by that action. -/
theorem stateSurprisal_starAlgEquiv (e : A ≃⋆ₐ[ℂ] A) (ρ : A)
    (hρ : IsSelfAdjoint ρ)
    (hlog : ContinuousOn Real.log (spectrum ℝ ρ)) :
    stateSurprisal (e ρ) = e (stateSurprisal ρ) := by
  change -cfc Real.log (e.toStarAlgHom ρ) =
    e.toStarAlgHom (-cfc Real.log ρ)
  have heρ : IsSelfAdjoint (e.toStarAlgHom ρ) := by
    calc
      star (e.toStarAlgHom ρ) = e.toStarAlgHom (star ρ) := by
        rw [map_star]
      _ = e.toStarAlgHom ρ := by rw [hρ]
  have hmap := e.toStarAlgHom.map_cfc Real.log ρ hlog
    (by fun_prop) hρ heρ
  calc
    -cfc Real.log (e ρ) = -e.toStarAlgHom (cfc Real.log ρ) := by
      simpa using congrArg (fun x : A => -x) hmap.symm
    _ = e.toStarAlgHom (-cfc Real.log ρ) := by rw [map_neg]

theorem exp_neg_stateSurprisal (ρ : A) (hρ : IsStrictlyPositive ρ) :
    NormedSpace.exp (- stateSurprisal ρ) = ρ := by
  have hlog : - stateSurprisal ρ = CFC.log ρ := by
    simp [stateSurprisal, CFC.log]
  rw [hlog]
  exact CFC.exp_log ρ hρ

theorem commute_stateSurprisal_implies_commute_state
    (ρ A : A) (hρ : IsStrictlyPositive ρ)
    (hA : Commute A (stateSurprisal ρ)) :
    Commute A ρ := by
  rw [← exp_neg_stateSurprisal ρ hρ]
  exact hA.neg_right.exp_right

omit [PartialOrder A] [StarOrderedRing A] in
theorem stateSurprisal_commutes_exp_self (ρ : A) (t : ℝ) :
    Commute (stateSurprisal ρ)
      (NormedSpace.exp (t • stateSurprisal ρ)) := by
  exact ((Commute.refl (stateSurprisal ρ)).smul_right t).exp_right

omit [PartialOrder A] [StarOrderedRing A] in
theorem commute_state_implies_commute_stateSurprisal
    (ρ A : A) (hA : Commute A ρ) :
    Commute A (stateSurprisal ρ) := by
  unfold stateSurprisal
  exact (hA.symm.cfc_real Real.log).symm.neg_right

theorem commute_state_iff_commute_stateSurprisal
    (ρ A : A) (hρ : IsStrictlyPositive ρ) :
    Commute A ρ ↔ Commute A (stateSurprisal ρ) := by
  constructor
  · exact commute_state_implies_commute_stateSurprisal ρ A
  · exact commute_stateSurprisal_implies_commute_state ρ A hρ

omit [PartialOrder A] [StarOrderedRing A] in
theorem commute_state_implies_commute_cfc
    (ρ A : A) (hA : Commute A ρ) (f : ℝ → ℝ) :
    Commute A (cfc f ρ) := by
  exact (hA.symm.cfc_real f).symm

theorem commute_stateSurprisal_implies_commute_cfc
    (ρ A : A) (hρ : IsStrictlyPositive ρ)
    (hA : Commute A (stateSurprisal ρ)) (f : ℝ → ℝ) :
    Commute A (cfc f ρ) := by
  exact commute_state_implies_commute_cfc ρ A
    (commute_stateSurprisal_implies_commute_state ρ A hρ hA) f

omit [PartialOrder A] [StarOrderedRing A] in
theorem stateSurprisal_commutes_cfc_product
    (ρ : A) (f g : ℝ → ℝ) :
    Commute (stateSurprisal ρ) (cfc f ρ * cfc g ρ) := by
  exact (stateSurprisal_commutes_cfc ρ f).mul_right
    (stateSurprisal_commutes_cfc ρ g)

/-!
The operator surprisal also commutes with the (same-state) Petz kernel.
This is a product statement in the ambient noncommutative algebra: no
simultaneous diagonalization is used, and the multiplication order of the
kernel remains explicit.
-/
theorem stateSurprisal_commutes_petzKernel_self
    (ρ : A) (hρ : 0 ≤ ρ) (α : ℝ) :
    Commute (stateSurprisal ρ) (petzKernel α ρ ρ) := by
  unfold petzKernel
  exact (stateSurprisal_commutes_rpow ρ hρ α).mul_right
    (stateSurprisal_commutes_rpow ρ hρ (1 - α))

theorem stateSurprisal_commutes_sandwichedCore_self
    (ρ : A) (hρ : 0 ≤ ρ) (α : ℝ) :
    Commute (stateSurprisal ρ) (sandwichedCore α ρ ρ) := by
  unfold sandwichedCore
  have hK := stateSurprisal_isSelfAdjoint ρ
  have hp := stateSurprisal_commutes_rpow ρ hρ (sandwichExponent α)
  have hp' : Commute (star (stateSurprisal ρ))
      (ρ ^ sandwichExponent α) := by
    rw [hK.star_eq]
    exact hp
  have hstar := hp'.star_right
  have hρcomm : Commute (stateSurprisal ρ) ρ := by
    have h := stateSurprisal_commutes_rpow ρ hρ 1
    rw [CFC.rpow_one ρ hρ] at h
    exact h
  exact (hstar.mul_right hρcomm).mul_right hp

theorem stateSurprisal_commutes_sandwichedKernel_self
    (ρ : A) (hρ : 0 ≤ ρ) (α : ℝ) :
    Commute (stateSurprisal ρ) (sandwichedKernel α ρ ρ) := by
  unfold sandwichedKernel
  rw [CFC.rpow_eq_cfc_real (sandwichedCore_nonneg α hρ)]
  exact (stateSurprisal_commutes_sandwichedCore_self ρ hρ α).symm.cfc_real
    (fun x : ℝ => x ^ α) |>.symm

theorem stateSurprisal_commutes_petzKernel_of_rpow_commute
    (ρ σ : A) (hρ : 0 ≤ ρ) (α : ℝ)
    (hσ : Commute ρ (σ ^ (1 - α))) :
    Commute (stateSurprisal ρ) (petzKernel α ρ σ) := by
  unfold petzKernel
  have hcross := hσ.cfc_real Real.log
  have hlog : Commute (cfc Real.log ρ) (σ ^ (1 - α)) := hcross
  have hsurprisal :
      Commute (stateSurprisal ρ) (σ ^ (1 - α)) := by
    unfold stateSurprisal
    exact hlog.neg_left
  exact (stateSurprisal_commutes_rpow ρ hρ α).mul_right hsurprisal

theorem stateSurprisal_commutes_petzKernel_of_commuting_states
    (ρ σ : A) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρσ : Commute ρ σ) (α : ℝ) :
    Commute (stateSurprisal ρ) (petzKernel α ρ σ) := by
  have hcross : Commute ρ (σ ^ (1 - α)) := by
    rw [CFC.rpow_eq_cfc_real hσ]
    exact (hρσ.symm.cfc_real (fun x : ℝ => x ^ (1 - α))).symm
  exact stateSurprisal_commutes_petzKernel_of_rpow_commute ρ σ hρ α hcross

theorem rho_commutes_relativeLogDensity_of_commuting_states
    (ρ σ : A) (hρ : 0 ≤ ρ) (hρσ : Commute ρ σ) :
    Commute ρ (relativeLogDensity ρ σ) := by
  have hρsa : IsSelfAdjoint ρ := IsSelfAdjoint.of_nonneg hρ
  unfold relativeLogDensity
  have hρlogρ : Commute ρ (cfc Real.log ρ) := by
    have h := cfc_commute_cfc (fun x : ℝ => x) Real.log ρ
    have hid : cfc (fun x : ℝ => x) ρ = ρ := cfc_id' ℝ (a := ρ)
    rw [hid] at h
    exact h
  have hρlogσ : Commute ρ (cfc Real.log σ) := by
    exact (hρσ.symm.cfc_real Real.log).symm
  exact hρlogρ.sub_right hρlogσ

omit [PartialOrder A] [StarOrderedRing A] in
theorem relativeLogDensity_isSelfAdjoint (ρ σ : A) :
    IsSelfAdjoint (relativeLogDensity ρ σ) := by
  unfold relativeLogDensity
  exact (IsSelfAdjoint.cfc.sub IsSelfAdjoint.cfc)

theorem rho_commutes_umegakiKernel_of_commuting_states
    (ρ σ : A) (hρ : 0 ≤ ρ) (hρσ : Commute ρ σ) :
    Commute ρ (umegakiKernel ρ σ) := by
  unfold umegakiKernel
  exact (Commute.refl ρ).mul_right
    (rho_commutes_relativeLogDensity_of_commuting_states ρ σ hρ hρσ)

theorem stateSurprisal_commutes_umegakiKernel_of_commuting_states
    (ρ σ : A) (hρ : 0 ≤ ρ) (hρσ : Commute ρ σ) :
    Commute (stateSurprisal ρ) (umegakiKernel ρ σ) := by
  have hlog : Commute (cfc Real.log ρ) (cfc Real.log σ) := by
    have h₁ := hρσ.cfc_real Real.log
    have h₂ := h₁.symm.cfc_real Real.log
    exact h₂.symm
  have hsurp : Commute (stateSurprisal ρ) (relativeLogDensity ρ σ) := by
    unfold stateSurprisal relativeLogDensity
    have hself : Commute (cfc Real.log ρ) (cfc Real.log ρ) := Commute.refl _
    exact hself.neg_left.sub_right hlog.neg_left
  unfold umegakiKernel
  have hρcomm : Commute (stateSurprisal ρ) ρ := by
    have h := stateSurprisal_commutes_rpow ρ hρ 1
    rw [CFC.rpow_one ρ hρ] at h
    exact h
  exact hρcomm.mul_right hsurp

omit [PartialOrder A] [StarOrderedRing A] in
theorem stateSurprisal_commutes_relativeLogDensity_of_commuting_states
    (ρ σ : A) (hρσ : Commute ρ σ) :
    Commute (stateSurprisal ρ) (relativeLogDensity ρ σ) := by
  have hlog : Commute (cfc Real.log ρ) (cfc Real.log σ) := by
    have h₁ := hρσ.cfc_real Real.log
    have h₂ := h₁.symm.cfc_real Real.log
    exact h₂.symm
  unfold stateSurprisal relativeLogDensity
  exact (Commute.refl (cfc Real.log ρ)).neg_left.sub_right hlog.neg_left

theorem umegakiKernel_isSelfAdjoint_of_commuting_states
    (ρ σ : A) (hρ : 0 ≤ ρ) (hρσ : Commute ρ σ) :
    IsSelfAdjoint (umegakiKernel ρ σ) := by
  have hρsa : IsSelfAdjoint ρ := IsSelfAdjoint.of_nonneg hρ
  have hrel : IsSelfAdjoint (relativeLogDensity ρ σ) :=
    relativeLogDensity_isSelfAdjoint ρ σ
  have hcomm : Commute ρ (relativeLogDensity ρ σ) :=
    rho_commutes_relativeLogDensity_of_commuting_states ρ σ hρ hρσ
  unfold umegakiKernel
  exact (IsSelfAdjoint.commute_iff hρsa hrel).mp hcomm

theorem relativeLogDensity_commutes_umegakiKernel_of_commuting_states
    (ρ σ : A) (hρ : 0 ≤ ρ) (hρσ : Commute ρ σ) :
    Commute (relativeLogDensity ρ σ) (umegakiKernel ρ σ) := by
  have hcomm : Commute ρ (relativeLogDensity ρ σ) :=
    rho_commutes_relativeLogDensity_of_commuting_states ρ σ hρ hρσ
  unfold umegakiKernel
  exact hcomm.symm.mul_right (Commute.refl _)

theorem stateSurprisal_commutes_sandwichedKernel_of_commuting_states
    (ρ σ : A) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρσ : Commute ρ σ) (α : ℝ) :
    Commute (stateSurprisal ρ) (sandwichedKernel α ρ σ) := by
  have hγ : Commute ρ (σ ^ sandwichExponent α) := by
    rw [CFC.rpow_eq_cfc_real hσ]
    exact (hρσ.symm.cfc_real
      (fun x : ℝ => x ^ sandwichExponent α)).symm
  have hlogγ : Commute (cfc Real.log ρ) (σ ^ sandwichExponent α) :=
    hγ.cfc_real Real.log
  have hsurpγ : Commute (stateSurprisal ρ) (σ ^ sandwichExponent α) := by
    unfold stateSurprisal
    exact hlogγ.neg_left
  have hK := stateSurprisal_isSelfAdjoint ρ
  have hstar : Commute (stateSurprisal ρ)
      (star (σ ^ sandwichExponent α)) := by
    have haux : Commute (star (stateSurprisal ρ))
        (σ ^ sandwichExponent α) := by
      rw [hK.star_eq]
      exact hsurpγ
    exact haux.star_right
  have hρcomm : Commute (stateSurprisal ρ) ρ := by
    have h := stateSurprisal_commutes_rpow ρ hρ 1
    rw [CFC.rpow_one ρ hρ] at h
    exact h
  have hcore : Commute (stateSurprisal ρ)
      (sandwichedCore α ρ σ) := by
    unfold sandwichedCore
    exact (hstar.mul_right hρcomm).mul_right hsurpγ
  unfold sandwichedKernel
  rw [CFC.rpow_eq_cfc_real (sandwichedCore_nonneg α hρ)]
  exact hcore.symm.cfc_real (fun x : ℝ => x ^ α) |>.symm

theorem sandwichedCore_isSelfAdjoint
    (ρ σ : A) (hρ : 0 ≤ ρ) (α : ℝ) :
    IsSelfAdjoint (sandwichedCore α ρ σ) := by
  exact IsSelfAdjoint.of_nonneg (sandwichedCore_nonneg α hρ)

theorem sandwichedKernel_isSelfAdjoint
    (ρ σ : A) (hρ : 0 ≤ ρ) (α : ℝ) :
    IsSelfAdjoint (sandwichedKernel α ρ σ) := by
  unfold sandwichedKernel
  rw [CFC.rpow_eq_cfc_real (sandwichedCore_nonneg α hρ)]
  exact IsSelfAdjoint.cfc

end InfoGeometry.Canonical.OperatorSurprisalCFCCommute
