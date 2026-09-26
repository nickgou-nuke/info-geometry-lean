import proofs.KleinSixStateProjectiveMonodromy

/-!
# The central defect and its explicit six-state lift

The initially chosen generators satisfy a Pin-refined Klein relation with
central defect `-1`.  This defect obstructs those *particular* lifts from
satisfying the ordinary relation.  In the concrete complex six-state model
the class is nevertheless a coboundary: multiplying the triality generator
by the central phase `i` produces a genuine `U(6)` representation.
-/

noncomputable section
namespace KleinVectorLiftObstruction

open ProjectiveUnitary6 KleinPresentedGroup
open KleinSixStateProjectiveMonodromy

/-- The central defect measured by a chosen pair of lifts. -/
def kleinDefect {G : Type*} [Group G] (A B : G) : G :=
  A * B * A⁻¹ * B

theorem kleinDefect_eq_twist {G : Type*} [Group G] (A B z : G)
    (hpin : A * B * A⁻¹ = z * B⁻¹) :
    kleinDefect A B = z := by
  rw [kleinDefect, hpin]
  simp

/-- A nontrivial defect prevents the originally selected lifts from obeying
the untwisted Klein relation. -/
theorem chosen_lifts_do_not_obey_klein {G : Type*} [Group G]
    (A B z : G) (hz : z ≠ 1)
    (hpin : A * B * A⁻¹ = z * B⁻¹) :
    A * B * A⁻¹ ≠ B⁻¹ := by
  intro h
  have : z * B⁻¹ = 1 * B⁻¹ := hpin.symm.trans (by simpa using h)
  exact hz (mul_right_cancel this)

/-- Abstract phase-correction lemma.  If a central phase `p` squares to the
inverse defect, replacing `B` by `pB` removes the projective cocycle. -/
theorem phase_corrects_central_defect {G : Type*} [Group G]
    (A B z p : G) (hp : p ∈ Subgroup.center G)
    (hp2 : p * p = z⁻¹)
    (hpin : A * B * A⁻¹ = z * B⁻¹) :
    A * (p * B) * A⁻¹ = (p * B)⁻¹ := by
  have hp_comm (g : G) : p * g = g * p :=
    (Subgroup.mem_center_iff.mp hp g).symm
  have hp_inv_comm (g : G) : p⁻¹ * g = g * p⁻¹ :=
    (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hp) g).symm
  have hpz : p * z = p⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    calc
      p * (p * z) = (p * p) * z := (mul_assoc _ _ _).symm
      _ = z⁻¹ * z := by rw [hp2]
      _ = 1 := by simp
  calc
    A * (p * B) * A⁻¹ = p * (A * B * A⁻¹) := by
      rw [← mul_assoc A p B, ← hp_comm A]
      simp only [mul_assoc]
    _ = p * (z * B⁻¹) := by rw [hpin]
    _ = p⁻¹ * B⁻¹ := by rw [← mul_assoc, hpz]
    _ = B⁻¹ * p⁻¹ := hp_inv_comm B⁻¹
    _ = (p * B)⁻¹ := by simp

/-- The central unitary phase `i I₆`. -/
def phaseIU6 : U6 :=
  ⟨Complex.I • (1 : Matrix (Fin 6) (Fin 6) ℂ), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, smul_smul]
    norm_num⟩

theorem phaseIU6_mem_center : phaseIU6 ∈ CenterU6 := by
  rw [Subgroup.mem_center_iff]
  intro A
  apply Subtype.ext
  simp [phaseIU6]

theorem phaseIU6_sq : phaseIU6 * phaseIU6 = centralSignU6⁻¹ := by
  have hsignInv : centralSignU6⁻¹ = centralSignU6 := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    simp [centralSignU6]
  rw [hsignInv]
  apply Subtype.ext
  change (Complex.I • (1 : Matrix (Fin 6) (Fin 6) ℂ)) *
      (Complex.I • 1) = -(1 : Matrix (Fin 6) (Fin 6) ℂ)
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  norm_num

theorem centralSignU6_ne_one : centralSignU6 ≠ 1 := by
  intro h
  have h00 := congrArg (fun A : U6 ↦ A.1 0 0) h
  norm_num [centralSignU6] at h00

/-- The original concrete generators genuinely carry the nontrivial central
defect. -/
theorem concrete_chosen_lifts_twisted (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    thetaU6 omega homega * trialityU6 omega homega *
        (thetaU6 omega homega)⁻¹ ≠
      (trialityU6 omega homega)⁻¹ :=
  chosen_lifts_do_not_obey_klein _ _ centralSignU6 centralSignU6_ne_one
    (concrete_pin_relation omega homega)

/-- Phase-corrected triality generator. -/
def liftedTrialityU6 (omega : ℂ) (homega : omega ^ 2 + omega + 1 = 0) : U6 :=
  phaseIU6 * trialityU6 omega homega

theorem concrete_lifted_klein_relation (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    thetaU6 omega homega * liftedTrialityU6 omega homega *
        (thetaU6 omega homega)⁻¹ =
      (liftedTrialityU6 omega homega)⁻¹ :=
  phase_corrects_central_defect _ _ centralSignU6 phaseIU6
    phaseIU6_mem_center phaseIU6_sq (concrete_pin_relation omega homega)

/-- A genuine unitary representation of the presented Klein group. -/
def concreteKleinUnitaryLift (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    KleinGroup →* U6 :=
  kleinRep (thetaU6 omega homega) (liftedTrialityU6 omega homega)
    (concrete_lifted_klein_relation omega homega)

theorem concreteKleinUnitaryLift_generators (omega : ℂ)
    (homega : omega ^ 2 + omega + 1 = 0) :
    concreteKleinUnitaryLift omega homega (toKlein genA) = thetaU6 omega homega ∧
    concreteKleinUnitaryLift omega homega (toKlein genB) = liftedTrialityU6 omega homega :=
  kleinRep_relator_relation _ _ (concrete_lifted_klein_relation omega homega)

end KleinVectorLiftObstruction
end noncomputable section
