import InfoGeometry.Canonical.SuperchargeTransportBridge
import InfoGeometry.Canonical.TomitaTakesaki
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

namespace InfoGeometry.Canonical.SuperchargeCARCCRBridge

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

/-- Canonical modular supercharge operator on the doubled Krein carrier. -/
@[rep_depth krein]
noncomputable abbrev modularSuperchargeOp : FockEndomorphism E := spectral_epsilon (E := E)

/-- Canonical CPT supercharge operator `Q = Jε = K` on the doubled Krein carrier. -/
@[rep_depth krein]
noncomputable abbrev cptSuperchargeOp : FockEndomorphism E :=
  (modularCPTSupercharge (E := E)).Q

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

/--
The primitive `J/ε` commutator is exactly `2Q`, where `Q` is the canonical
Tomita CPT supercharge.
-/
@[rep_depth krein]
theorem parity_modular_supercharge_ccr_eq_two_cpt :
    (paritySuperchargeOp (E := E)).comp (modularSuperchargeOp (E := E))
      - (modularSuperchargeOp (E := E)).comp (paritySuperchargeOp (E := E))
      = (2 : ℝ) • cptSuperchargeOp (E := E) := by
  have hQ : (modularCPTSupercharge (E := E)).Q = complex_i (E := E) := by
    calc
      (modularCPTSupercharge (E := E)).Q = dilationOperator (E := E) := by
        simpa using modularCPTSupercharge_Q_eq_dilationOperator (E := E)
      _ = complex_i (E := E) := dilationOperator_eq_complex_i (E := E)
  calc
    (paritySuperchargeOp (E := E)).comp (modularSuperchargeOp (E := E))
        - (modularSuperchargeOp (E := E)).comp (paritySuperchargeOp (E := E))
      = (2 : ℝ) • (complex_i (E := E)) := by
          simpa [paritySuperchargeOp, modularSuperchargeOp] using
            clmComm_modular_j_spectral_epsilon (E := E)
    _ = (2 : ℝ) • cptSuperchargeOp (E := E) := by
          simpa [cptSuperchargeOp] using congrArg (fun T => (2 : ℝ) • T) hQ.symm

/-- The derived CPT supercharge agrees with the canonical dilation generator. -/
@[rep_depth krein, simp] theorem cptSuperchargeOp_eq_dilationOperator :
    cptSuperchargeOp (E := E) = dilationOperator (E := E) := by
  simpa [cptSuperchargeOp] using modularCPTSupercharge_Q_eq_dilationOperator (E := E)

/-- The CPT supercharge squares to `-Id` on the doubled carrier. -/
@[rep_depth krein, simp] theorem cptSuperchargeOp_sq :
    (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  simpa [cptSuperchargeOp] using modularCPTSupercharge_hamiltonian (E := E)

/-- The CPT supercharge sends the positive chiral sector to the negative one. -/
@[rep_depth krein]
theorem cptSuperchargeOp_maps_plus_to_minus
    {v : DoubledSpace E} (hv : inGradePlus (E := E) v) :
    inGradeMinus (E := E) (cptSuperchargeOp (E := E) v) := by
  change inGradeMinus (E := E) (((modularCPTSupercharge (E := E)).Q) v)
  exact modularCPTSupercharge_maps_plus_to_minus (E := E) hv

/-- The CPT supercharge sends the negative chiral sector to the positive one. -/
@[rep_depth krein]
theorem cptSuperchargeOp_maps_minus_to_plus
    {v : DoubledSpace E} (hv : inGradeMinus (E := E) v) :
    inGradePlus (E := E) (cptSuperchargeOp (E := E) v) := by
  change inGradePlus (E := E) (((modularCPTSupercharge (E := E)).Q) v)
  exact modularCPTSupercharge_maps_minus_to_plus (E := E) hv

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

end Core

end InfoGeometry.Canonical.SuperchargeCARCCRBridge
