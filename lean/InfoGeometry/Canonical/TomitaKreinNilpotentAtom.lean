import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.RealMajoranaCategory
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.TomitaKreinNilpotentAtom

The finite Tomita/Krein `Cl(1,1)` atom on the canonical doubled real carrier.

This module records the precise theorem-only spine behind the informal atom
`{1, ε, J, Jε}`:

* `J` is the doubled modular swap `modular_j`.
* `ε` is the real fundamental symmetry `spectral_epsilon`.
* `Jε` is the doubled phase axis `complex_i`, and squares to `-id`.
* `P₊` and `P₋` are the idempotent sector projectors of `ε`.
* the concrete split-null CAR operators square to zero and multiply to `P₊`
  and `P₋`.

This is deliberately finite and local.  It does not assert a Heisenberg,
Kac-Moody, Sugawara, or Virasoro current algebra; those require mode labels,
normal ordering, and central extensions on top of this atom.
-/

namespace InfoGeometry.Canonical.TomitaKreinNilpotentAtom

open InfoGeometry.Krein
open InfoGeometry.Canonical.SuperchargeCARCCRBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The doubled real Tomita/Krein atom:
`J² = 1`, `ε² = 1`, `Jε = -εJ`, `I = Jε`, and `I² = -1`.

The last line is the important boundary: `complex_i`/`clockAxis` is a complex
structure, not a Krein involution.
-/
@[rep_depth krein]
theorem tomitaKrein_cl11_atom :
    (modular_j (E := E)).comp (modular_j (E := E))
        = ContinuousLinearMap.id ℝ (DoubledSpace E)
      ∧ (spectral_epsilon (E := E)).comp (spectral_epsilon (E := E))
        = ContinuousLinearMap.id ℝ (DoubledSpace E)
      ∧ (modular_j (E := E)).comp (spectral_epsilon (E := E))
        = -((spectral_epsilon (E := E)).comp (modular_j (E := E)))
      ∧ complex_i (E := E) = (modular_j (E := E)).comp (spectral_epsilon (E := E))
      ∧ (complex_i (E := E)).comp (complex_i (E := E))
        = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  exact ⟨modular_j_involution E, spectral_epsilon_involution E,
    modular_j_spectral_epsilon_anticommute E, rfl, complex_i_sq E⟩

/--
The spectral projectors of `ε` form the finite idempotent sector split:
`P₊² = P₊`, `P₋² = P₋`, `P₊P₋ = P₋P₊ = 0`, and `P₊ + P₋ = 1`.
-/
@[rep_depth krein]
theorem tomitaKrein_projector_atom :
    (spectralPlusProj (E := E)).comp (spectralPlusProj (E := E))
        = spectralPlusProj (E := E)
      ∧ (spectralMinusProj (E := E)).comp (spectralMinusProj (E := E))
        = spectralMinusProj (E := E)
      ∧ (spectralPlusProj (E := E)).comp (spectralMinusProj (E := E)) = 0
      ∧ (spectralMinusProj (E := E)).comp (spectralPlusProj (E := E)) = 0
      ∧ spectralPlusProj (E := E) + spectralMinusProj (E := E)
        = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  exact ⟨spectralPlusProj_idempotent (E := E), spectralMinusProj_idempotent (E := E),
    InfoGeometry.Quantum.RealMajoranaCategory.spectralPlusProj_comp_spectralMinusProj
      (E := E),
    InfoGeometry.Quantum.RealMajoranaCategory.spectralMinusProj_comp_spectralPlusProj
      (E := E),
    spectralProj_sum (E := E)⟩

/-- The concrete split-null creation operator squares to zero. -/
@[rep_depth krein]
theorem concrete_creation_square_zero :
    (concreteCARCreation (E := E)).comp (concreteCARCreation (E := E)) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hv]
  apply DoubledSpace.ext <;> simp [concreteCARCreation]

/-- The concrete split-null annihilation operator squares to zero. -/
@[rep_depth krein]
theorem concrete_annihilation_square_zero :
    (concreteCARAnnihilation (E := E)).comp (concreteCARAnnihilation (E := E)) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hv]
  apply DoubledSpace.ext <;> simp [concreteCARAnnihilation]

/--
The concrete nilpotent/idempotent fit:

* `u₊² = 0` and `u₋² = 0`;
* `u₊u₋ = P₊` and `u₋u₊ = P₋`;
* `{u₋, u₊} = 1`;
* `[u₊, u₋] = ε` and `[u₋, u₊] = -ε`.
-/
@[rep_depth krein]
theorem tomitaKrein_nilpotent_idempotent_atom :
    (concreteCARCreation (E := E)).comp (concreteCARCreation (E := E)) = 0
      ∧ (concreteCARAnnihilation (E := E)).comp
          (concreteCARAnnihilation (E := E)) = 0
      ∧ (concreteCARCreation (E := E)).comp (concreteCARAnnihilation (E := E))
        = spectralPlusProj (E := E)
      ∧ (concreteCARAnnihilation (E := E)).comp (concreteCARCreation (E := E))
        = spectralMinusProj (E := E)
      ∧ CARBracket (E := E)
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
        = ContinuousLinearMap.id ℝ (DoubledSpace E)
      ∧ CCRBracket (E := E)
          (concreteCARCreation (E := E))
          (concreteCARAnnihilation (E := E))
        = spectral_epsilon (E := E)
      ∧ CCRBracket (E := E)
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
        = -(spectral_epsilon (E := E)) := by
  exact ⟨concrete_creation_square_zero (E := E),
    concrete_annihilation_square_zero (E := E),
    concrete_creation_comp_annihilation_eq_spectralPlusProj (E := E),
    concrete_annihilation_comp_creation_eq_spectralMinusProj (E := E),
    concrete_car_minus_plus (E := E),
    concrete_car_creation_annihilation_ccrBracket_eq_spectral_epsilon (E := E),
    concrete_car_ccrBracket_eq_neg_spectral_epsilon (E := E)⟩

/--
Tomita/PHS conjugation on doubled-space endomorphisms:
`T ↦ J ∘ T ∘ J`.

This is the finite boundary reflection used to package the real Majorana swap
at the split-`Cl(1,1)` level.
-/
@[rep_depth krein]
noncomputable def tomitaConjOp
    (T : InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism E) :
    InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism E :=
  (modular_j (E := E)).comp (T.comp (modular_j (E := E)))

/-- Tomita/PHS conjugation swaps the concrete split-null creation operator to annihilation. -/
@[rep_depth krein]
theorem tomitaConj_creation_eq_annihilation :
    tomitaConjOp (concreteCARCreation (E := E))
      = concreteCARAnnihilation (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : InfoGeometry.Krein.to_doubled (WithLp.fst u) (WithLp.snd u) = u := by
    apply DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hu]
  apply DoubledSpace.ext <;>
    simp [tomitaConjOp, concreteCARCreation, concreteCARAnnihilation,
      InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteCreation_apply_to_doubled,
      InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteAnnihilation_apply_to_doubled]

/-- Tomita/PHS conjugation swaps the concrete split-null annihilation operator to creation. -/
@[rep_depth krein]
theorem tomitaConj_annihilation_eq_creation :
    tomitaConjOp (concreteCARAnnihilation (E := E))
      = concreteCARCreation (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : InfoGeometry.Krein.to_doubled (WithLp.fst u) (WithLp.snd u) = u := by
    apply DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hu]
  apply DoubledSpace.ext <;>
    simp [tomitaConjOp, concreteCARCreation, concreteCARAnnihilation,
      InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteCreation_apply_to_doubled,
      InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteAnnihilation_apply_to_doubled]

/-- The real Majorana boundary candidate is fixed by Tomita/PHS conjugation. -/
@[rep_depth krein]
theorem concrete_majorana_swap_is_phs_invariant :
    tomitaConjOp (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E))
      = concreteCARCreation (E := E) + concreteCARAnnihilation (E := E) := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : InfoGeometry.Krein.to_doubled (WithLp.fst u) (WithLp.snd u) = u := by
    apply DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hu]
  unfold tomitaConjOp concreteCARCreation concreteCARAnnihilation
  simp [InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteCreation_apply_to_doubled,
    InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteAnnihilation_apply_to_doubled,
    add_comm]

/--
Single exported finite spine for the doubled real Krein map:
Tomita atom, idempotent projector split, and nilpotent CAR split-null fit.
-/
@[rep_depth krein]
theorem tomitaKrein_finite_atom_spine :
    ((modular_j (E := E)).comp (modular_j (E := E))
        = ContinuousLinearMap.id ℝ (DoubledSpace E)
      ∧ (spectral_epsilon (E := E)).comp (spectral_epsilon (E := E))
        = ContinuousLinearMap.id ℝ (DoubledSpace E)
      ∧ (modular_j (E := E)).comp (spectral_epsilon (E := E))
        = -((spectral_epsilon (E := E)).comp (modular_j (E := E)))
      ∧ complex_i (E := E) = (modular_j (E := E)).comp (spectral_epsilon (E := E))
      ∧ (complex_i (E := E)).comp (complex_i (E := E))
        = -(ContinuousLinearMap.id ℝ (DoubledSpace E)))
      ∧ ((spectralPlusProj (E := E)).comp (spectralPlusProj (E := E))
        = spectralPlusProj (E := E)
      ∧ (spectralMinusProj (E := E)).comp (spectralMinusProj (E := E))
        = spectralMinusProj (E := E)
      ∧ (spectralPlusProj (E := E)).comp (spectralMinusProj (E := E)) = 0
      ∧ (spectralMinusProj (E := E)).comp (spectralPlusProj (E := E)) = 0
      ∧ spectralPlusProj (E := E) + spectralMinusProj (E := E)
        = ContinuousLinearMap.id ℝ (DoubledSpace E))
      ∧ ((concreteCARCreation (E := E)).comp (concreteCARCreation (E := E)) = 0
      ∧ (concreteCARAnnihilation (E := E)).comp
          (concreteCARAnnihilation (E := E)) = 0
      ∧ (concreteCARCreation (E := E)).comp (concreteCARAnnihilation (E := E))
        = spectralPlusProj (E := E)
      ∧ (concreteCARAnnihilation (E := E)).comp (concreteCARCreation (E := E))
        = spectralMinusProj (E := E)
      ∧ CARBracket (E := E)
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
        = ContinuousLinearMap.id ℝ (DoubledSpace E)
      ∧ CCRBracket (E := E)
          (concreteCARCreation (E := E))
          (concreteCARAnnihilation (E := E))
        = spectral_epsilon (E := E)
      ∧ CCRBracket (E := E)
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
        = -(spectral_epsilon (E := E))) := by
  exact ⟨tomitaKrein_cl11_atom (E := E), tomitaKrein_projector_atom (E := E),
    tomitaKrein_nilpotent_idempotent_atom (E := E)⟩

end Core

end InfoGeometry.Canonical.TomitaKreinNilpotentAtom
