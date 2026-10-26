import InfoGeometry.MassSpectrometry.FragmentationGreenResponse
import InfoGeometry.Singular.Drazin

/-!
# Absorption, Drazin inverses, and the finite compatibility alternative

The transient K, completed T, and generator 1-T have different inverses:
K has Drazin inverse zero, T has Drazin inverse Pi, and 1-T has a finite
centered Green group inverse. None is identified with a metric pseudoinverse.
-/
noncomputable section
namespace InfoGeometry.MassSpectrometry.AbsorbingDrazin
open scoped BigOperators Matrix
open InfoGeometry.Singular.Drazin

section Ring
variable {A : Type*} [Ring A]

/-- Exponent is a valid bound, not necessarily the minimal Drazin index. -/
theorem nilpotent_drazin_zero (K : A) (N : ℕ) (h : K ^ N = 0) :
    IsDrazinInverse K 0 N := by
  refine IsDrazinInverse.mk (by simp) (by simp) ?_
  simpa using h

theorem pow_mul_stationary (T P : A) (h : T * P = P) (k : ℕ) : T ^ k * P = P := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, ih, h]

theorem stationary_mul_pow (T P : A) (h : P * T = P) (k : ℕ) : P * T ^ k = P := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mul_assoc, ih, h]

/-- An eventually constant power determines a Drazin inverse. -/
theorem stabilized_drazin (T P : A) (N : ℕ)
    (hPP : P * P = P) (hTP : T * P = P) (hPT : P * T = P) (hN : T ^ N = P) :
    IsDrazinInverse T P N := by
  refine IsDrazinInverse.mk (by rw [hPT, hPP]) (hTP.trans hPT.symm) ?_
  rw [hN, pow_mul_stationary T P hTP]

/-- Finite Green sum on the complementary stationary sector. -/
def centeredGreen (T P : A) (N : ℕ) : A :=
  ∑ k ∈ Finset.range N, (T ^ k - P)

theorem centeredGreen_left (T P : A) (hTP : T * P = P) (N : ℕ) :
    (1 - T) * centeredGreen T P N = 1 - T ^ N := by
  induction N with
  | zero => simp [centeredGreen]
  | succ N ih =>
      have hs : centeredGreen T P (N+1) = centeredGreen T P N + (T^N-P) := by
        simp only [centeredGreen, Finset.sum_range_succ]
      rw [hs, mul_add, ih]
      have ht : (1-T)*(T^N-P) = T^N-T^(N+1) := by
        rw [mul_sub, sub_mul, sub_mul, one_mul, one_mul, hTP, sub_self, sub_zero,
          ← pow_succ']
      rw [ht]
      abel

theorem centeredGreen_right (T P : A) (hPT : P * T = P) (N : ℕ) :
    centeredGreen T P N * (1 - T) = 1 - T ^ N := by
  induction N with
  | zero => simp [centeredGreen]
  | succ N ih =>
      have hs : centeredGreen T P (N+1) = centeredGreen T P N + (T^N-P) := by
        simp only [centeredGreen, Finset.sum_range_succ]
      rw [hs, add_mul, ih]
      have ht : (T^N-P)*(1-T) = T^N-T^(N+1) := by
        rw [sub_mul, mul_sub, mul_sub, mul_one, mul_one, hPT, sub_self, sub_zero,
          ← pow_succ]
      rw [ht]
      abel

theorem centeredGreen_annihilates (T P : A)
    (hPP : P * P = P) (hTP : T * P = P) (hPT : P * T = P) (N : ℕ) :
    centeredGreen T P N * P = 0 ∧ P * centeredGreen T P N = 0 := by
  constructor
  · unfold centeredGreen
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro k _
    rw [sub_mul, pow_mul_stationary T P hTP, hPP, sub_self]
  · unfold centeredGreen
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [mul_sub, stationary_mul_pow T P hPT, hPP, sub_self]

/-- The generator has group-inverse laws on 1-P, not the inverse of T. -/
theorem generator_group_inverse (T P : A) (N : ℕ)
    (hPP : P * P = P) (hTP : T * P = P) (hPT : P * T = P) (hN : T ^ N = P) :
    IsDrazinInverse (1-T) (centeredGreen T P N) 1 := by
  have hl : (1-T)*centeredGreen T P N = 1-P := by rw [centeredGreen_left T P hTP, hN]
  have hr : centeredGreen T P N*(1-T) = 1-P := by rw [centeredGreen_right T P hPT, hN]
  obtain ⟨_, hpz⟩ := centeredGreen_annihilates T P hPP hTP hPT N
  refine IsDrazinInverse.mk ?_ (hl.trans hr.symm) ?_
  · rw [hr, sub_mul, one_mul, hpz, sub_zero]
  · rw [pow_one]
    change 1 - T = (1-T)^2 * centeredGreen T P N
    rw [pow_two, mul_assoc, hl]
    noncomm_ring [hTP]

/-- The completed operator has an explicit stationary-plus-nilpotent split. -/
theorem residue_power (T P : A)
    (hPP : P*P=P) (hTP : T*P=P) (hPT : P*T=P) (k : ℕ) :
    (T-P)^(k+1) = T^(k+1)-P := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, sub_mul, mul_sub, mul_sub,
        pow_mul_stationary T P hTP, hPT, hPP, ← pow_succ]
      abel

end Ring

section Compatibility
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- Finite Fredholm-type alternative for the completed singular generator. -/
theorem generator_solvable_iff
    (T P : Matrix ι ι R) (N : ℕ)
    (hTP : T*P=P) (hPT : P*T=P) (hN : T^N=P) (b : ι → R) :
    (∃ x, (1-T) *ᵥ x = b) ↔ P *ᵥ b = 0 := by
  have hl : (1-T)*centeredGreen T P N = 1-P := by rw [centeredGreen_left T P hTP, hN]
  constructor
  · rintro ⟨x, rfl⟩
    rw [Matrix.mulVec_mulVec]
    simp [mul_sub, hPT]
  · intro hb
    refine ⟨centeredGreen T P N *ᵥ b, ?_⟩
    rw [Matrix.mulVec_mulVec, hl, Matrix.sub_mulVec, Matrix.one_mulVec, hb, sub_zero]

/-- Every solution consists of the centered Green solution plus its stationary part. -/
theorem generator_solution_decomposition
    (T P : Matrix ι ι R) (N : ℕ) (hPT : P*T=P) (hN : T^N=P)
    (b x : ι → R) (hx : (1-T) *ᵥ x = b) :
    x = centeredGreen T P N *ᵥ b + P *ᵥ x := by
  have hr : centeredGreen T P N*(1-T)=1-P := by rw [centeredGreen_right T P hPT, hN]
  have he := congrArg (fun y => centeredGreen T P N *ᵥ y) hx
  rw [Matrix.mulVec_mulVec, hr, Matrix.sub_mulVec, Matrix.one_mulVec] at he
  exact sub_eq_iff_eq_add.mp he

end Compatibility

namespace StochasticGrammar
variable {n : ℕ} {D : FragmentationDAG n}
open InfoGeometry.Algebra.RankedMatrixPowers

theorem transient_drazin (G : MassSpectrometry.StochasticGrammar D) :
    IsDrazinInverse G.transientMatrix 0 (rankHorizon D.rank) :=
  nilpotent_drazin_zero _ _ G.transient_pow_rankHorizon_eq_zero

theorem completion_drazin (G : MassSpectrometry.StochasticGrammar D) :
    IsDrazinInverse G.absorbingCompletion (absorptionProjection n) (rankHorizon D.rank) :=
  stabilized_drazin _ _ _ (absorptionProjection_idempotent n)
    G.completion_mul_absorptionProjection G.absorptionProjection_mul_completion
    G.absorbingCompletion_pow_rankHorizon

theorem completion_generator_drazin (G : MassSpectrometry.StochasticGrammar D) :
    IsDrazinInverse (1-G.absorbingCompletion)
      (centeredGreen G.absorbingCompletion (absorptionProjection n) (rankHorizon D.rank)) 1 :=
  generator_group_inverse _ _ _ (absorptionProjection_idempotent n)
    G.completion_mul_absorptionProjection G.absorptionProjection_mul_completion
    G.absorbingCompletion_pow_rankHorizon

end StochasticGrammar
end InfoGeometry.MassSpectrometry.AbsorbingDrazin
