import InfoGeometry.Canonical.SuperchargeTransportBridge
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.RealBdG
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.SuperchargeCARCCRBridge

Carrier/coherence bridge for the supercharge lane and CAR/CCR channels.

This file is intentionally narrow and owner-respecting:
- carrier: doubled Krein space endomorphisms,
- primitive supercharge operators: `J` and `ε`,
- odd-odd CAR channel and even-even CCR channel on the supergraded Fock lane,
- concrete split-`Cl(1,1)` null-mode CAR pair.
-/

namespace SuperchargeCARCCRBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.TomitaTakesaki

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Supergraded Fock endomorphisms are exactly doubled-Krein endomorphisms. -/
@[rep_depth krein, simp] theorem fockEndomorphism_eq_doubledEnd :
    FockEndomorphism E = (DoubledSpace E →L[ℝ] DoubledSpace E) := rfl

/-- Canonical parity supercharge operator on the doubled Krein carrier. -/
@[rep_depth krein]
noncomputable abbrev paritySuperchargeOp : FockEndomorphism E := modular_j (E := E)

@[rep_depth krein, simp] theorem paritySuperchargeOp_eq_modular_j :
    paritySuperchargeOp (E := E) = modular_j (E := E) := rfl

/-- Canonical modular supercharge operator on the doubled Krein carrier. -/
@[rep_depth krein]
noncomputable abbrev modularSuperchargeOp : FockEndomorphism E := spectral_epsilon (E := E)

@[rep_depth krein, simp] theorem modularSuperchargeOp_eq_spectral_epsilon :
    modularSuperchargeOp (E := E) = spectral_epsilon (E := E) := rfl

/-- Canonical CPT supercharge operator `Q = Jε = K` on the doubled Krein carrier. -/
@[rep_depth krein]
noncomputable abbrev cptSuperchargeOp : FockEndomorphism E :=
  (modularCPTSupercharge (E := E)).Q

@[rep_depth krein, simp] theorem cptSuperchargeOp_eq_complex_i :
    cptSuperchargeOp (E := E) = complex_i (E := E) := by
  calc
    cptSuperchargeOp (E := E) = dilationOperator (E := E) := by
      simpa [cptSuperchargeOp] using modularCPTSupercharge_Q_eq_dilationOperator (E := E)
    _ = complex_i (E := E) := dilationOperator_eq_complex_i (E := E)

/-- The derived CPT supercharge is the real doubled phase axis `K = J ∘ ε`. -/
@[rep_depth krein, simp] theorem cptSuperchargeOp_eq_modularK :
    cptSuperchargeOp (E := E) = InfoGeometry.Canonical.RealBdG.modularK (E := E) := by
  rw [cptSuperchargeOp_eq_complex_i, InfoGeometry.Canonical.RealBdG.modularK_eq_complex_i]

/-- The CPT supercharge is Hestenes-linear, i.e. `K`-linear. -/
@[rep_depth krein]
theorem cptSuperchargeOp_isKLinear :
    InfoGeometry.Canonical.RealBdG.KLinear (E := E) (cptSuperchargeOp (E := E)) := by
  simp [InfoGeometry.Canonical.RealBdG.KLinear]

/-- The derived CPT supercharge is exactly the root split axis `J ∘ ε`. -/
@[rep_depth krein, simp] theorem cptSuperchargeOp_eq_modular_j_comp_spectral_epsilon :
    cptSuperchargeOp (E := E) = (modular_j (E := E)).comp (spectral_epsilon (E := E)) := by
  calc
    cptSuperchargeOp (E := E) = complex_i (E := E) := cptSuperchargeOp_eq_complex_i (E := E)
    _ = (modular_j (E := E)).comp (spectral_epsilon (E := E)) := by
      rfl

/-- The odd-odd (CAR) channel on the supergraded Fock lane. -/
@[rep_depth krein]
noncomputable abbrev CARBracket
    (A B : FockEndomorphism E) : FockEndomorphism E :=
  fockAnticommutator (E := E) A B

/-- The even-even (CCR) channel on the supergraded Fock lane. -/
@[rep_depth krein]
noncomputable abbrev CCRBracket
    (A B : FockEndomorphism E) : FockEndomorphism E :=
  fockCommutator (E := E) A B

/-- Primitive supercharge pair closes trivially in the odd-odd channel on the doubled carrier. -/
@[rep_depth krein]
theorem parity_modular_supercharge_car_zero :
    CARBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E))
      = 0 := by
  simpa [CARBracket, paritySuperchargeOp, modularSuperchargeOp] using
    (InfoGeometry.Canonical.SuperchargeTransportBridge.parity_modular_anticommutator_eq_zero
      (E := E))

/-- Root-name form of the primitive odd-odd vanishing CAR channel. -/
@[rep_depth krein]
theorem modular_j_spectral_epsilon_car_zero :
    CARBracket (E := E) (modular_j (E := E)) (spectral_epsilon (E := E)) = 0 := by
  simpa using parity_modular_supercharge_car_zero (E := E)

/-- The parity supercharge is Hestenes-antilinear, i.e. `K`-antilinear. -/
@[rep_depth krein]
theorem paritySuperchargeOp_isKAntilinear :
    InfoGeometry.Canonical.RealBdG.KAntilinear (E := E) (paritySuperchargeOp (E := E)) := by
  simpa [InfoGeometry.Canonical.RealBdG.KAntilinear, paritySuperchargeOp,
    RealBdG.modularK_eq_complex_i] using
    (InfoGeometry.Krein.modular_j_complex_i_anticommute (E := E))

/--
The primitive `J/ε` commutator is exactly `2Q`, where `Q` is the canonical
Tomita CPT supercharge.
-/
@[rep_depth krein]
theorem parity_modular_supercharge_ccr_eq_two_cpt :
    (paritySuperchargeOp (E := E)).comp (modularSuperchargeOp (E := E))
      - (modularSuperchargeOp (E := E)).comp (paritySuperchargeOp (E := E))
      = (2 : ℝ) • cptSuperchargeOp (E := E) := by
  calc
    (paritySuperchargeOp (E := E)).comp (modularSuperchargeOp (E := E))
        - (modularSuperchargeOp (E := E)).comp (paritySuperchargeOp (E := E))
      = (2 : ℝ) • (complex_i (E := E)) := by
          simpa [paritySuperchargeOp, modularSuperchargeOp] using
            clmComm_modular_j_spectral_epsilon (E := E)
    _ = (2 : ℝ) • cptSuperchargeOp (E := E) := by
          rw [cptSuperchargeOp_eq_complex_i]

/-- The primitive `J/ε` commutator is exactly `2K`, where `K = J ∘ ε`. -/
@[rep_depth krein]
theorem parity_modular_supercharge_ccr_eq_two_modularK :
    (paritySuperchargeOp (E := E)).comp (modularSuperchargeOp (E := E))
      - (modularSuperchargeOp (E := E)).comp (paritySuperchargeOp (E := E))
      = (2 : ℝ) • InfoGeometry.Canonical.RealBdG.modularK (E := E) := by
  simpa [cptSuperchargeOp_eq_modularK] using parity_modular_supercharge_ccr_eq_two_cpt (E := E)

/-- Bracket form of the primitive even-even closure `[J, ε] = 2Q`. -/
@[rep_depth krein]
theorem parity_modular_supercharge_ccrBracket_eq_two_cpt :
    CCRBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E))
      = (2 : ℝ) • cptSuperchargeOp (E := E) := by
  simpa [CCRBracket, fockCommutator, superBracket_even_left] using
    (parity_modular_supercharge_ccr_eq_two_cpt (E := E))

/-- Bracket form of the primitive even-even closure `[J, ε] = 2K`. -/
@[rep_depth krein]
theorem parity_modular_supercharge_ccrBracket_eq_two_modularK :
    CCRBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E))
      = (2 : ℝ) • InfoGeometry.Canonical.RealBdG.modularK (E := E) := by
  simpa [CCRBracket, fockCommutator, superBracket_even_left] using
    (parity_modular_supercharge_ccr_eq_two_modularK (E := E))

/-- Root-name form of the primitive even-even commutator closure. -/
@[rep_depth krein]
theorem modular_j_spectral_epsilon_ccr_eq_two_complex_i :
    (modular_j (E := E)).comp (spectral_epsilon (E := E))
        - (spectral_epsilon (E := E)).comp (modular_j (E := E))
      = (2 : ℝ) • complex_i (E := E) := by
  simpa [cptSuperchargeOp_eq_complex_i] using parity_modular_supercharge_ccr_eq_two_cpt (E := E)

/-- The derived CPT supercharge agrees with the canonical dilation generator. -/
@[rep_depth krein, simp] theorem cptSuperchargeOp_eq_dilationOperator :
    cptSuperchargeOp (E := E) = dilationOperator (E := E) := by
  exact modularCPTSupercharge_Q_eq_dilationOperator (E := E)

/-- The CPT supercharge squares to `-Id` on the doubled carrier. -/
@[rep_depth krein, simp] theorem cptSuperchargeOp_sq :
    (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  change ((modularCPTSupercharge (E := E)).Q).comp ((modularCPTSupercharge (E := E)).Q)
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E))
  exact modularCPTSupercharge_hamiltonian (E := E)

/-- Root-name square law for the split phase axis. -/
@[rep_depth krein, simp] theorem complex_i_sq :
    (complex_i (E := E)).comp (complex_i (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  rw [← cptSuperchargeOp_eq_complex_i]
  exact cptSuperchargeOp_sq (E := E)

/-- The CPT supercharge sends the positive chiral sector to the negative one. -/
@[rep_depth krein]
theorem cptSuperchargeOp_maps_plus_to_minus
    {v : DoubledSpace E} (hv : inGradePlus (E := E) v) :
    inGradeMinus (E := E) (cptSuperchargeOp (E := E) v) := by
  change inGradeMinus (E := E) (((modularCPTSupercharge (E := E)).Q) v)
  exact modularCPTSupercharge_maps_plus_to_minus (E := E) hv

/-- Root-name sector flip for the split phase axis. -/
@[rep_depth krein]
theorem complex_i_maps_plus_to_minus
    {v : DoubledSpace E} (hv : inGradePlus (E := E) v) :
    inGradeMinus (E := E) (complex_i (E := E) v) := by
  simpa [cptSuperchargeOp_eq_complex_i] using cptSuperchargeOp_maps_plus_to_minus (E := E) hv

/-- The CPT supercharge sends the negative chiral sector to the positive one. -/
@[rep_depth krein]
theorem cptSuperchargeOp_maps_minus_to_plus
    {v : DoubledSpace E} (hv : inGradeMinus (E := E) v) :
    inGradePlus (E := E) (cptSuperchargeOp (E := E) v) := by
  change inGradePlus (E := E) (((modularCPTSupercharge (E := E)).Q) v)
  exact modularCPTSupercharge_maps_minus_to_plus (E := E) hv

/-- Root-name sector flip for the split phase axis. -/
@[rep_depth krein]
theorem complex_i_maps_minus_to_plus
    {v : DoubledSpace E} (hv : inGradeMinus (E := E) v) :
    inGradePlus (E := E) (complex_i (E := E) v) := by
  simpa [cptSuperchargeOp_eq_complex_i] using cptSuperchargeOp_maps_minus_to_plus (E := E) hv

/-- CAR channel is symmetric. -/
@[rep_depth krein, simp] theorem carBracket_swap
    (A B : FockEndomorphism E) :
    CARBracket (E := E) A B = CARBracket (E := E) B A := by
  unfold CARBracket
  exact fockAnticommutator_symm (E := E) A B

/-- CCR channel is skew under swapping arguments. -/
@[rep_depth krein, simp] theorem ccrBracket_swap
    (A B : FockEndomorphism E) :
    CCRBracket (E := E) A B = -CCRBracket (E := E) B A := by
  unfold CCRBracket
  exact fockCommutator_swap (E := E) A B

/-- Concrete annihilation operator from the split-`Cl(1,1)` null mode `u_-`. -/
@[rep_depth krein]
noncomputable abbrev concreteCARAnnihilation : FockEndomorphism E :=
  cliffordConcreteAnnihilation (E := E)

/-- Concrete creation operator from the split-`Cl(1,1)` null mode `u_+`. -/
@[rep_depth krein]
noncomputable abbrev concreteCARCreation : FockEndomorphism E :=
  cliffordConcreteCreation (E := E)

/-- The concrete split-`Cl(1,1)` null-mode pair is a genuine CAR pair. -/
@[rep_depth krein]
theorem concrete_car_pair :
    IsCARPair (E := E)
      (concreteCARAnnihilation (E := E))
      (concreteCARCreation (E := E)) := by
  simpa [concreteCARAnnihilation, concreteCARCreation] using
    (cliffordConcreteIsCARPair (E := E))

/-- Concrete split-null ladders are nilpotent in the odd-odd CAR channel. -/
@[rep_depth krein]
theorem concrete_car_nilpotency :
    CARBracket (E := E)
        (concreteCARAnnihilation (E := E))
        (concreteCARAnnihilation (E := E))
      = 0
      ∧ CARBracket (E := E)
          (concreteCARCreation (E := E))
          (concreteCARCreation (E := E))
        = 0 := by
  rcases concrete_car_pair (E := E) with ⟨hminus, hplus, _⟩
  refine ⟨?_, ?_⟩
  · change fockAnticommutator (E := E)
      (concreteCARAnnihilation (E := E))
      (concreteCARAnnihilation (E := E)) = 0
    exact hminus
  · change fockAnticommutator (E := E)
      (concreteCARCreation (E := E))
      (concreteCARCreation (E := E)) = 0
    exact hplus

/-- Concrete mixed CAR identity `{u_-, u_+} = 1`. -/
@[rep_depth krein]
theorem concrete_car_minus_plus :
    CARBracket (E := E)
        (concreteCARAnnihilation (E := E))
        (concreteCARCreation (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  rcases concrete_car_pair (E := E) with ⟨_, _, hmp⟩
  change fockAnticommutator (E := E)
      (concreteCARAnnihilation (E := E))
      (concreteCARCreation (E := E))
    = ContinuousLinearMap.id ℝ (DoubledSpace E)
  exact hmp

/-- The concrete split-null product `u₊u₋` is the positive spectral projector. -/
@[rep_depth krein]
theorem concrete_creation_comp_annihilation_eq_spectralPlusProj :
    (concreteCARCreation (E := E)).comp (concreteCARAnnihilation (E := E))
      = spectralPlusProj (E := E) := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hv]
  simp [concreteCARAnnihilation, concreteCARCreation]

/-- The concrete split-null product `u₋u₊` is the negative spectral projector. -/
@[rep_depth krein]
theorem concrete_annihilation_comp_creation_eq_spectralMinusProj :
    (concreteCARAnnihilation (E := E)).comp (concreteCARCreation (E := E))
      = spectralMinusProj (E := E) := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hv]
  simp [concreteCARAnnihilation, concreteCARCreation]

/--
Concrete split-null commutator readout:
`[u₋, u₊] = P₋ - P₊`, the finite grading-sector difference.

This is a finite CAR/product identity, not a Heisenberg current-mode or central
extension statement.
-/
@[rep_depth krein]
theorem concrete_car_ccrBracket_eq_spectralMinus_sub_spectralPlus :
    CCRBracket (E := E)
        (concreteCARAnnihilation (E := E))
        (concreteCARCreation (E := E))
      = spectralMinusProj (E := E) - spectralPlusProj (E := E) := by
  rw [CCRBracket, fockCommutator_eq]
  rw [concrete_annihilation_comp_creation_eq_spectralMinusProj,
    concrete_creation_comp_annihilation_eq_spectralPlusProj]

/-- Reversed concrete split-null commutator recovers the positive-minus-negative grading sign. -/
@[rep_depth krein]
theorem concrete_car_creation_annihilation_ccrBracket_eq_spectralPlus_sub_spectralMinus :
    CCRBracket (E := E)
        (concreteCARCreation (E := E))
        (concreteCARAnnihilation (E := E))
      = spectralPlusProj (E := E) - spectralMinusProj (E := E) := by
  rw [CCRBracket, fockCommutator_eq]
  rw [concrete_creation_comp_annihilation_eq_spectralPlusProj,
    concrete_annihilation_comp_creation_eq_spectralMinusProj]

/--
Concrete split-null sign convention:
`[u₋, u₊] = -ε` for the repository's `ε = P₊ - P₋`.

This is still a finite doubled-carrier commutator identity.
-/
@[rep_depth krein]
theorem concrete_car_ccrBracket_eq_neg_spectral_epsilon :
    CCRBracket (E := E)
        (concreteCARAnnihilation (E := E))
        (concreteCARCreation (E := E))
      = -(spectral_epsilon (E := E)) := by
  rw [concrete_car_ccrBracket_eq_spectralMinus_sub_spectralPlus]
  have hhalf (z : E) : (2 : ℝ)⁻¹ • z + (2 : ℝ)⁻¹ • z = z := by
    have hscalar : ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = (1 : ℝ) := by norm_num
    rw [← add_smul, hscalar, one_smul]
  have hhalf_neg (z : E) : -((2 : ℝ)⁻¹ • z) + -((2 : ℝ)⁻¹ • z) = -z := by
    rw [← neg_add, hhalf]
  apply ContinuousLinearMap.ext
  intro v
  have hv : InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hv]
  apply InfoGeometry.Krein.DoubledSpace.ext <;>
    simp [spectralPlusProj, spectralMinusProj, InfoGeometry.Krein.spectral_epsilon,
      InfoGeometry.Krein.to_doubled, sub_eq_add_neg, hhalf, hhalf_neg]

/--
Reversed concrete split-null sign convention:
`[u₊, u₋] = ε` for the repository's `ε = P₊ - P₋`.
-/
@[rep_depth krein]
theorem concrete_car_creation_annihilation_ccrBracket_eq_spectral_epsilon :
    CCRBracket (E := E)
        (concreteCARCreation (E := E))
        (concreteCARAnnihilation (E := E))
      = spectral_epsilon (E := E) := by
  rw [concrete_car_creation_annihilation_ccrBracket_eq_spectralPlus_sub_spectralMinus]
  have hhalf (z : E) : (2 : ℝ)⁻¹ • z + (2 : ℝ)⁻¹ • z = z := by
    have hscalar : ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) = (1 : ℝ) := by norm_num
    rw [← add_smul, hscalar, one_smul]
  have hhalf_neg (z : E) : -((2 : ℝ)⁻¹ • z) + -((2 : ℝ)⁻¹ • z) = -z := by
    rw [← neg_add, hhalf]
  apply ContinuousLinearMap.ext
  intro v
  have hv : InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hv]
  apply InfoGeometry.Krein.DoubledSpace.ext <;>
    simp [spectralPlusProj, spectralMinusProj, InfoGeometry.Krein.spectral_epsilon,
      InfoGeometry.Krein.to_doubled, sub_eq_add_neg, hhalf, hhalf_neg]

/--
Single-surface oscillator closure package on the canonical doubled carrier:
odd-odd primitive closure, even-even primitive closure, CPT square law,
and concrete split-null CAR nilpotency/mixed identity.
-/
@[rep_depth transport]
theorem harmonic_oscillator_spine :
    CARBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E))
      = 0
      ∧ CCRBracket (E := E)
          (paritySuperchargeOp (E := E))
          (modularSuperchargeOp (E := E))
        = (2 : ℝ) • cptSuperchargeOp (E := E)
      ∧ (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E))
          = -(ContinuousLinearMap.id ℝ (DoubledSpace E))
      ∧ CARBracket (E := E)
          (concreteCARAnnihilation (E := E))
          (concreteCARAnnihilation (E := E))
        = 0
      ∧ CARBracket (E := E)
          (concreteCARCreation (E := E))
          (concreteCARCreation (E := E))
        = 0
      ∧ CARBracket (E := E)
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
        = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  rcases concrete_car_nilpotency (E := E) with ⟨hminusNil, hplusNil⟩
  refine ⟨parity_modular_supercharge_car_zero (E := E), ?_⟩
  refine ⟨parity_modular_supercharge_ccrBracket_eq_two_cpt (E := E), ?_⟩
  refine ⟨cptSuperchargeOp_sq (E := E), ?_⟩
  refine ⟨hminusNil, ?_⟩
  exact ⟨hplusNil, concrete_car_minus_plus (E := E)⟩

end Core

end SuperchargeCARCCRBridge
