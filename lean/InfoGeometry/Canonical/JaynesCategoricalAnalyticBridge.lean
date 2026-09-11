import InfoGeometry.Canonical.JaynesCategoricalInductionBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteJaynesFormalism

/-!
# InfoGeometry.Canonical.JaynesCategoricalAnalyticBridge

Finite analytic readback bridge over the categorical Jaynes induction tower.

This file keeps the boundary strict:

* it uses only finite-stage positivity hypotheses;
* it reuses the existing finite KL/cross/entropy identities;
* it combines them with the categorical propagated centered-score zero law.

No measure-theoretic completion.
No continuum entropy limit theorem.
No global state uniqueness claim.
-/

namespace InfoGeometry.Canonical.JaynesCategoricalAnalyticBridge

open InfoGeometry.Canonical.JaynesCategoricalInductionBridge
open InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge
open InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge.FiniteReferenceStateOps
open InfoGeometry.Canonical.FiniteJaynesFormalism
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/--
Finite positivity package for a Jaynes pair at a fixed stage.
-/
def FiniteStagePositivity (P : FiniteJaynesPair ι) : Prop :=
  (∀ i : ι, 0 < P.observation i) ∧ IsPositive P.reference

namespace FiniteStagePositivity

variable {P : FiniteJaynesPair ι}

/-- Finite KL decomposition under stagewise positivity. -/
theorem cross_eq_entropy_add_kl (h : FiniteStagePositivity P) :
    finiteCrossEntropy P.reference P.observation =
      finiteShannonEntropy P.observation + finiteKLDivergence P.reference P.observation :=
  finiteCrossEntropy_eq_finiteShannonEntropy_add_KL
    (R := P.reference) (obs := P.observation) h.1 h.2

/-- Finite LDDS decomposition under stagewise positivity. -/
theorem ldds_eq_entropy_sub_cross (h : FiniteStagePositivity P) :
    finiteLDDSEntropy P.reference P.observation =
      finiteShannonEntropy P.observation - finiteCrossEntropy P.reference P.observation :=
  finiteLDDSEntropy_eq_entropy_sub_cross_correction
    (R := P.reference) (obs := P.observation) h.1 h.2

end FiniteStagePositivity

section Cone

universe u

variable {Atom : Nat → Type u} [∀ n : Nat, Fintype (Atom n)]
variable {Limit : Type u} [Ring Limit]

variable (P : JaynesCategoricalCone (Atom := Atom) (Limit := Limit))

/--
Finite KL decomposition for stage `n` in a categorical Jaynes cone.
-/
theorem stage_cross_eq_entropy_add_kl
    (n : Nat)
    (hobs : ∀ i : Atom n, 0 < (P.observation n) i)
    (href : IsPositive (P.reference n)) :
    finiteCrossEntropy (P.reference n) (P.observation n) =
      finiteShannonEntropy (P.observation n) +
        finiteKLDivergence (P.reference n) (P.observation n) := by
  exact finiteCrossEntropy_eq_finiteShannonEntropy_add_KL
    (R := P.reference n) (obs := P.observation n) hobs href

/--
Combined finite-stage readback:
(1) an explicitly supplied weighted centered-score zero law, and
(2) the finite KL/cross/entropy decomposition at the same stage.
-/
theorem stage_centered_zero_and_cross_eq_entropy_add_kl
    (n : Nat)
    (hcentered :
      (∑ i : Atom n,
        (P.reference n).weight i *
          centeredRelativeDensity (P.reference n) (P.observation n) i) = 0)
    (hobs : ∀ i : Atom n, 0 < (P.observation n) i)
    (href : IsPositive (P.reference n)) :
    ((∑ i : Atom n,
      (P.reference n).weight i *
        centeredRelativeDensity (P.reference n) (P.observation n) i) = 0) ∧
    (finiteCrossEntropy (P.reference n) (P.observation n) =
      finiteShannonEntropy (P.observation n) +
        finiteKLDivergence (P.reference n) (P.observation n)) := by
  refine ⟨hcentered, ?_⟩
  exact stage_cross_eq_entropy_add_kl (P := P) n hobs href

end Cone

end InfoGeometry.Canonical.JaynesCategoricalAnalyticBridge
