import InfoGeometry.Canonical.RealDoubledWaveplate
import InfoGeometry.Canonical.SuperchargeCARCCRBridge

/-!
# The existing doubled CAR pair under the existing phase conjugation

Conventions: `phaseConjugation θ T = R(-θ) T R(θ)` and
`HestenesI = modular_j * spectral_epsilon`.  In particular, at pi/4 the
annihilation/creation operators are `(epsilon +/- HestenesI)/2`.
-/

noncomputable section
namespace InfoGeometry.Canonical.PhaseFlowCARBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.ProjectorEquivariance
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovClosedForms
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.RealDoubledWaveplate

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- The same carrier, with its existing two coordinate projections. -/
def doubledCoordinates : H₂ ≃ₗ[ℝ] E × E where
  toFun x := (WithLp.fst x, WithLp.snd x)
  invFun x := to_doubled x.1 x.2
  left_inv x := by apply DoubledSpace.ext <;> rfl
  right_inv x := by cases x; rfl
  map_add' x y := rfl
  map_smul' r x := rfl

theorem annihilation_eq_half_swap_add_phase :
    concreteCARAnnihilation (E := E) =
      (1 / 2 : ℝ) • (modular_j (E := E) + HestenesI (E := E)) := by
  apply ContinuousLinearMap.ext
  intro x
  have hx : to_doubled (WithLp.fst x) (WithLp.snd x) = x := by
    apply DoubledSpace.ext <;> rfl
  rw [← hx]
  apply DoubledSpace.ext <;>
    simp [concreteCARAnnihilation, cliffordConcreteAnnihilation_apply_to_doubled,
      HestenesI, ContinuousLinearMap.mul_apply, modular_j_apply,
      spectral_epsilon_apply, to_doubled] <;> module

theorem creation_eq_half_swap_sub_phase :
    concreteCARCreation (E := E) =
      (1 / 2 : ℝ) • (modular_j (E := E) - HestenesI (E := E)) := by
  apply ContinuousLinearMap.ext
  intro x
  have hx : to_doubled (WithLp.fst x) (WithLp.snd x) = x := by
    apply DoubledSpace.ext <;> rfl
  rw [← hx]
  apply DoubledSpace.ext <;>
    simp [concreteCARCreation, cliffordConcreteCreation_apply_to_doubled,
      HestenesI, ContinuousLinearMap.mul_apply, modular_j_apply,
      spectral_epsilon_apply, to_doubled] <;> module

/-- The requested plus formula is the transported existing annihilation. -/
theorem annihilation_quarter_turn :
    phaseConjugation (E := E) (Real.pi / 4) (concreteCARAnnihilation (E := E)) =
      (1 / 2 : ℝ) • (spectral_epsilon (E := E) + HestenesI (E := E)) := by
  rw [annihilation_eq_half_swap_add_phase, phaseConjugation_smul,
    phaseConjugation_add, phaseConjugation_HestenesI_pi_div_four]
  change (1 / 2 : ℝ) • (_ + HestenesI (E := E)) = _
  rw [phaseFlow_conj_modular_j_pi_div_four]

/-- The requested minus formula is the transported existing creation. -/
theorem creation_quarter_turn :
    phaseConjugation (E := E) (Real.pi / 4) (concreteCARCreation (E := E)) =
      (1 / 2 : ℝ) • (spectral_epsilon (E := E) - HestenesI (E := E)) := by
  rw [creation_eq_half_swap_sub_phase, phaseConjugation_smul, sub_eq_add_neg,
    phaseConjugation_add, phaseConjugation_neg, phaseConjugation_HestenesI_pi_div_four]
  change (1 / 2 : ℝ) • (_ + -HestenesI (E := E)) = _
  rw [phaseFlow_conj_modular_j_pi_div_four]
  rfl

/-- Square-zero is preserved, not created, by phase conjugation. -/
theorem conjugation_square_zero (θ : ℝ) (T : EndH) (hT : T * T = 0) :
    phaseConjugation θ T * phaseConjugation θ T = 0 := by
  rw [← phaseConjugation_mul, hT]
  simp [phaseConjugation]

/-- A square-one operator remains square-one, rather than becoming nilpotent. -/
theorem conjugation_square_one (θ : ℝ) (T : EndH) (hT : T * T = 1) :
    phaseConjugation θ T * phaseConjugation θ T = 1 := by
  rw [← phaseConjugation_mul, hT]
  exact phaseConjugation_id θ

/-- CAR covariance applies to the actual pair at every angle. -/
theorem phase_conjugated_car_pair (θ : ℝ) :
    IsCARPair (E := E)
      (phaseConjugation θ (concreteCARAnnihilation (E := E)))
      (phaseConjugation θ (concreteCARCreation (E := E))) := by
  rcases concrete_car_pair (E := E) with ⟨haa, hbb, hab⟩
  simp only [anticommutator, superBracket_odd_odd, ← ContinuousLinearMap.mul_def] at haa hbb hab
  simp only [IsCARPair, anticommutator, superBracket_odd_odd, ← ContinuousLinearMap.mul_def]
  have hz : phaseConjugation (E := E) θ 0 = 0 := by simp [phaseConjugation]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [phaseConjugation_add, phaseConjugation_mul, hz] using congrArg (phaseConjugation θ) haa
  · simpa only [phaseConjugation_add, phaseConjugation_mul, hz] using congrArg (phaseConjugation θ) hbb
  · simpa only [phaseConjugation_add, phaseConjugation_mul, phaseConjugation_id] using congrArg (phaseConjugation θ) hab

/-- Both ordered support products, with the pi/4 signs fixed. -/
theorem quarter_turn_supports :
    phaseConjugation (E := E) (Real.pi / 4) (concreteCARAnnihilation (E := E)) *
        phaseConjugation (Real.pi / 4) (concreteCARCreation (E := E)) = gradePlusProj (E := E) ∧
    phaseConjugation (E := E) (Real.pi / 4) (concreteCARCreation (E := E)) *
        phaseConjugation (Real.pi / 4) (concreteCARAnnihilation (E := E)) = gradeMinusProj (E := E) := by
  constructor
  · rw [← phaseConjugation_mul]
    change phaseConjugation _ ((concreteCARAnnihilation (E := E)).comp (concreteCARCreation (E := E))) = _
    rw [concrete_annihilation_comp_creation_eq_spectralMinusProj,
      phaseConjugation_spectralMinusProj_pi_div_four]
  · rw [← phaseConjugation_mul]
    change phaseConjugation _ ((concreteCARCreation (E := E)).comp (concreteCARAnnihilation (E := E))) = _
    rw [concrete_creation_comp_annihilation_eq_spectralPlusProj,
      phaseConjugation_spectralPlusProj_pi_div_four]

end InfoGeometry.Canonical.PhaseFlowCARBridge
