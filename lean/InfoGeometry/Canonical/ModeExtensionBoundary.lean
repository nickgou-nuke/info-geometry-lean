import InfoGeometry.Canonical.TomitaKreinNilpotentAtom
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ModeExtensionBoundary

A conservative mode-label boundary for the finite Tomita/Krein split-null atom.

This module does **not** construct a Heisenberg current algebra.  It only gives
the finite atom a mode-indexed *zero-mode seed*:

* label `0` is the proved finite split-null operator;
* every nonzero label is `0`;
* the finite CAR/CCR laws are recovered at label `0`;
* away from label `0`, the seed has no central current term.

This is the honest interface before a real bosonization/current-mode theorem:
it provides names `u_{±,n}` and `ε_n` without pretending that the nonzero modes
or normal-ordering anomaly have been derived.

Repository policy boundary:
this file does not construct the affine current witness
`J : Int → V →ₗ[𝕜] V` with truncation/commutator laws.
-/

namespace InfoGeometry.Canonical.ModeExtensionBoundary

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.TomitaKreinNilpotentAtom

section ZeroModeSeed

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Zero-mode seed for the split-null creation operator: `u₊,0 = u₊`, nonzero modes vanish. -/
@[rep_depth krein]
noncomputable abbrev splitNullCreationModeSeed (n : ℤ) : FockEndomorphism E :=
  if n = 0 then concreteCARCreation (E := E) else 0

/-- Zero-mode seed for the split-null annihilation operator: `u₋,0 = u₋`, nonzero modes vanish. -/
@[rep_depth krein]
noncomputable abbrev splitNullAnnihilationModeSeed (n : ℤ) : FockEndomorphism E :=
  if n = 0 then concreteCARAnnihilation (E := E) else 0

/-- Zero-mode seed for the Krein sign: `ε₀ = ε`, nonzero modes vanish. -/
@[rep_depth krein]
noncomputable abbrev splitEpsilonModeSeed (n : ℤ) : FockEndomorphism E :=
  if n = 0 then spectral_epsilon (E := E) else 0

@[simp, rep_depth krein]
theorem splitNullCreationModeSeed_zero :
    splitNullCreationModeSeed (E := E) 0 = concreteCARCreation (E := E) := by
  simp [splitNullCreationModeSeed]

@[simp, rep_depth krein]
theorem splitNullAnnihilationModeSeed_zero :
    splitNullAnnihilationModeSeed (E := E) 0 = concreteCARAnnihilation (E := E) := by
  simp [splitNullAnnihilationModeSeed]

@[simp, rep_depth krein]
theorem splitEpsilonModeSeed_zero :
    splitEpsilonModeSeed (E := E) 0 = spectral_epsilon (E := E) := by
  simp [splitEpsilonModeSeed]

@[simp, rep_depth krein]
theorem splitNullCreationModeSeed_ne_zero {n : ℤ} (hn : n ≠ 0) :
    splitNullCreationModeSeed (E := E) n = 0 := by
  simp [splitNullCreationModeSeed, hn]

@[simp, rep_depth krein]
theorem splitNullAnnihilationModeSeed_ne_zero {n : ℤ} (hn : n ≠ 0) :
    splitNullAnnihilationModeSeed (E := E) n = 0 := by
  simp [splitNullAnnihilationModeSeed, hn]

@[simp, rep_depth krein]
theorem splitEpsilonModeSeed_ne_zero {n : ℤ} (hn : n ≠ 0) :
    splitEpsilonModeSeed (E := E) n = 0 := by
  simp [splitEpsilonModeSeed, hn]

/-- At label `0`, the mode seed recovers the finite nilpotent/idempotent atom. -/
@[rep_depth krein]
theorem zeroModeSeed_nilpotent_idempotent_atom :
    (splitNullCreationModeSeed (E := E) 0).comp (splitNullCreationModeSeed (E := E) 0) = 0
      ∧ (splitNullAnnihilationModeSeed (E := E) 0).comp
          (splitNullAnnihilationModeSeed (E := E) 0) = 0
      ∧ (splitNullCreationModeSeed (E := E) 0).comp
          (splitNullAnnihilationModeSeed (E := E) 0)
        = spectralPlusProj (E := E)
      ∧ (splitNullAnnihilationModeSeed (E := E) 0).comp
          (splitNullCreationModeSeed (E := E) 0)
        = spectralMinusProj (E := E)
      ∧ CARBracket (E := E)
          (splitNullAnnihilationModeSeed (E := E) 0)
          (splitNullCreationModeSeed (E := E) 0)
        = ContinuousLinearMap.id ℝ (DoubledSpace E)
      ∧ CCRBracket (E := E)
          (splitNullCreationModeSeed (E := E) 0)
          (splitNullAnnihilationModeSeed (E := E) 0)
        = splitEpsilonModeSeed (E := E) 0 := by
  exact ⟨concrete_creation_square_zero (E := E),
    concrete_annihilation_square_zero (E := E),
    concrete_creation_comp_annihilation_eq_spectralPlusProj (E := E),
    concrete_annihilation_comp_creation_eq_spectralMinusProj (E := E),
    concrete_car_minus_plus (E := E),
    concrete_car_creation_annihilation_ccrBracket_eq_spectral_epsilon (E := E)⟩

/--
The zero-mode seed has no Heisenberg anomaly.  Its CCR bracket is the finite
grading sign only when both labels are zero, and vanishes otherwise.
-/
@[rep_depth krein]
theorem zeroModeSeed_ccrBracket (m n : ℤ) :
    CCRBracket (E := E)
        (splitNullCreationModeSeed (E := E) m)
        (splitNullAnnihilationModeSeed (E := E) n)
      = (if m = 0 ∧ n = 0 then spectral_epsilon (E := E) else 0) := by
  by_cases hm : m = 0
  · by_cases hn : n = 0
    · simpa [splitNullCreationModeSeed, splitNullAnnihilationModeSeed, hm, hn]
        using concrete_car_creation_annihilation_ccrBracket_eq_spectral_epsilon (E := E)
    · simp [splitNullCreationModeSeed, splitNullAnnihilationModeSeed, hm, hn, CCRBracket]
  ·
    simp [splitNullCreationModeSeed, splitNullAnnihilationModeSeed, hm, CCRBracket]

/--
The zero-mode seed recovers the finite CAR identity only at the shared zero
label; away from that label it vanishes.  This is still not a current algebra.
-/
@[rep_depth krein]
theorem zeroModeSeed_carBracket (m n : ℤ) :
    CARBracket (E := E)
        (splitNullAnnihilationModeSeed (E := E) m)
        (splitNullCreationModeSeed (E := E) n)
      = (if m = 0 ∧ n = 0 then ContinuousLinearMap.id ℝ (DoubledSpace E) else 0) := by
  by_cases hm : m = 0
  · by_cases hn : n = 0
    · simpa [splitNullCreationModeSeed, splitNullAnnihilationModeSeed, hm, hn]
        using concrete_car_minus_plus (E := E)
    · simp [splitNullCreationModeSeed, splitNullAnnihilationModeSeed, hm, hn,
        CARBracket, fockAnticommutator]
  ·
    simp [splitNullCreationModeSeed, splitNullAnnihilationModeSeed, hm,
      CARBracket, fockAnticommutator]

/-- Off the shared zero label, the zero-mode seed has no CCR bracket. -/
@[rep_depth krein]
theorem zeroModeSeed_ccrBracket_of_not_both_zero {m n : ℤ} (h : ¬ (m = 0 ∧ n = 0)) :
    CCRBracket (E := E)
        (splitNullCreationModeSeed (E := E) m)
        (splitNullAnnihilationModeSeed (E := E) n) = 0 := by
  rw [zeroModeSeed_ccrBracket (E := E) m n, if_neg h]

end ZeroModeSeed

end InfoGeometry.Canonical.ModeExtensionBoundary
