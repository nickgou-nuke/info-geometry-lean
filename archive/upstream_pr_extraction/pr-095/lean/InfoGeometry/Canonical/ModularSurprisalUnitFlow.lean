import InfoGeometry.OperatorAlgebra.NoncommutativeRenyi

/-!
# Unit-valued conjugation for operator surprisal

This owner keeps conjugation on the bundled unit group.  The ambient
C*-algebra is not assumed to have an inverse operation on every element.
-/

namespace InfoGeometry.Canonical.ModularSurprisalUnitFlow

open InfoGeometry.OperatorAlgebra.NoncommutativeRenyi

variable {A : Type*}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

noncomputable def expUnit (x : A) [NormedAlgebra ℚ A] [CompleteSpace A] : Aˣ :=
  (NormedSpace.isUnit_exp x).unit

omit [PartialOrder A] [StarOrderedRing A] in
theorem expUnit_val (x : A) [NormedAlgebra ℚ A] [CompleteSpace A] :
    (expUnit x : A) = NormedSpace.exp x := by
  exact IsUnit.unit_spec (NormedSpace.isUnit_exp x)

omit [PartialOrder A] [StarOrderedRing A] in
theorem expUnit_conjugation_fixes_of_commute
    (x y : A) [NormedAlgebra ℚ A] [CompleteSpace A]
    (hcomm : Commute x y) :
    (expUnit x : A) * y * (↑(expUnit x)⁻¹ : A) = y := by
  have hexp : Commute (NormedSpace.exp x) y := hcomm.exp_left
  rw [← expUnit_val x] at hexp
  exact (expUnit x).commute_iff_mul_inv_cancel.mp hexp

omit [PartialOrder A] [StarOrderedRing A] in
theorem expUnit_add_of_commute
    (x y : A) [NormedAlgebra ℚ A] [CompleteSpace A]
    (hcomm : Commute x y) :
    expUnit (x + y) = expUnit x * expUnit y := by
  apply Units.ext
  rw [expUnit_val, Units.val_mul, expUnit_val, expUnit_val]
  exact NormedSpace.exp_add_of_commute hcomm

omit [PartialOrder A] [StarOrderedRing A] in
theorem expUnit_zero [NormedAlgebra ℚ A] [CompleteSpace A] :
    expUnit (0 : A) = 1 := by
  apply Units.ext
  rw [expUnit_val]
  simp

omit [PartialOrder A] [StarOrderedRing A] in
theorem expUnit_neg (x : A) [NormedAlgebra ℚ A] [CompleteSpace A] :
    expUnit (-x) = (expUnit x)⁻¹ := by
  have h := expUnit_add_of_commute x (-x) (Commute.neg_right (Commute.refl x))
  rw [add_neg_cancel, expUnit_zero] at h
  apply (mul_left_cancel (a := expUnit x))
  rw [h.symm]
  simp

omit [PartialOrder A] [StarOrderedRing A] in
theorem unit_conjugation_fixes_stateSurprisal
    (ρ : A) (u : Aˣ)
    (hcomm : Commute (u : A) (stateSurprisal ρ)) :
    (u : A) * stateSurprisal ρ * (↑u⁻¹ : A) = stateSurprisal ρ := by
  exact (u.commute_iff_mul_inv_cancel).mp hcomm

omit [PartialOrder A] [StarOrderedRing A] in
theorem unit_conjugation_fixes_cfc_of_commute
    (ρ : A) (u : Aˣ) (f : ℝ → ℝ)
    (hcomm : Commute (u : A) ρ) :
    (u : A) * cfc f ρ * (↑u⁻¹ : A) = cfc f ρ := by
  exact (u.commute_iff_mul_inv_cancel).mp ((hcomm.symm.cfc_real f).symm)

omit [PartialOrder A] [StarOrderedRing A] in
theorem unit_conjugation_fixes_stateSurprisal_of_commute_state
    (ρ : A) (u : Aˣ) (hcomm : Commute (u : A) ρ) :
    (u : A) * stateSurprisal ρ * (↑u⁻¹ : A) = stateSurprisal ρ := by
  apply unit_conjugation_fixes_stateSurprisal ρ u
  unfold stateSurprisal
  exact (hcomm.symm.cfc_real Real.log).symm.neg_right

omit [PartialOrder A] [StarOrderedRing A] in
theorem expUnit_nsmul (x : A) (n : ℕ)
    [NormedAlgebra ℚ A] [CompleteSpace A] :
    expUnit (n • x) = (expUnit x) ^ n := by
  have hn : ∀ m : ℕ, Commute (m • x) x := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
        rw [succ_nsmul]
        exact ihm.add_left (Commute.refl x)
  induction n with
  | zero => simp [expUnit_zero]
  | succ n ih =>
      rw [succ_nsmul, expUnit_add_of_commute (n • x) x
        (hn n), ih, pow_succ]

omit [PartialOrder A] [StarOrderedRing A] in
theorem expUnit_zsmul (x : A) (n : ℤ)
    [NormedAlgebra ℚ A] [CompleteSpace A] :
    expUnit (n • x) = (expUnit x) ^ n := by
  cases n with
  | ofNat n =>
      simpa using expUnit_nsmul x n
  | negSucc n =>
      rw [negSucc_zsmul, expUnit_neg]
      simpa using expUnit_nsmul x (n + 1)

omit [PartialOrder A] [StarOrderedRing A] in
theorem expUnit_conjugation_fixes_stateSurprisal_self
    (ρ : A) [NormedAlgebra ℚ A] [CompleteSpace A] :
    (expUnit (stateSurprisal ρ) : A) * stateSurprisal ρ *
        (↑(expUnit (stateSurprisal ρ))⁻¹ : A) = stateSurprisal ρ := by
  exact expUnit_conjugation_fixes_of_commute
    (stateSurprisal ρ) (stateSurprisal ρ) (Commute.refl _)

omit [PartialOrder A] [StarOrderedRing A] in
theorem expUnit_zsmul_conjugation_fixes_stateSurprisal
    (ρ : A) (n : ℤ) [NormedAlgebra ℚ A] [CompleteSpace A] :
    (expUnit (n • stateSurprisal ρ) : A) * stateSurprisal ρ *
        (↑(expUnit (n • stateSurprisal ρ))⁻¹ : A) = stateSurprisal ρ := by
  exact expUnit_conjugation_fixes_of_commute
    (n • stateSurprisal ρ) (stateSurprisal ρ)
    (Commute.smul_left (Commute.refl _) n)

omit [PartialOrder A] [StarOrderedRing A] in
theorem stateSurprisal_commutes_expUnit_self
    (ρ : A) [NormedAlgebra ℚ A] [CompleteSpace A] :
    Commute (stateSurprisal ρ) (expUnit (stateSurprisal ρ) : A) := by
  rw [expUnit_val]
  exact (Commute.refl (stateSurprisal ρ)).exp_right

end InfoGeometry.Canonical.ModularSurprisalUnitFlow
