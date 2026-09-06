import InfoGeometry.OperatorAlgebra.NoncommutativeRenyi

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
