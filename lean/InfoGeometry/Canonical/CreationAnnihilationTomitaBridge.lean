import Mathlib.Tactic
import InfoGeometry.Canonical.TomitaKreinNilpotentAtom

/-!
# InfoGeometry.Canonical.CreationAnnihilationTomitaBridge

Creation/annihilation operators as a Tomita ladder pair.

The algebraic content is small and useful:

* if `J` swaps creation and annihilation, then `creation + annihilation` is
  `J`-even;
* `creation - annihilation` is `J`-odd;
* the completed/central Majorana combination is the even part, while the
  scale-normal modular density is the odd part.

The concrete split-`Cl(1,1)` CAR operators already exist in
`TomitaKreinNilpotentAtom`; this file exposes the same pattern in a reusable
generic form and records the concrete readout.

#### BUCKET 1: CLOSED FINITE THEOREMS
For the concrete split-`Cl(1,1)` CAR pair, Lean proves the Tomita swap
`J c = a`, `J a = c`, the `J`-even Majorana readout `J(c+a)=c+a`, and the
`J`-odd density readout `J(c-a)=-(c-a)`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
For an arbitrary vector space, the same even/odd conclusions require an
explicit `TomitaLadderPair` witness saying that the supplied linear mirror
swaps the supplied creation and annihilation vectors.

#### BUCKET 3: OPEN CLOSURE DEBT
No analytic zeta function, completed xi function, Riemann Hypothesis theorem,
quantum-gravity equivalence, C*-completion, or continuum QFT model is proved in
this file.
-/

noncomputable section

namespace InfoGeometry.Canonical.CreationAnnihilationTomitaBridge

open scoped InnerProductSpace
open InfoGeometry.Canonical.TomitaKreinNilpotentAtom
open InfoGeometry.Canonical.SuperchargeCARCCRBridge

/-! ## Generic Tomita ladder pair -/

/-- A creation/annihilation pair swapped by a linear Tomita involution. -/
structure TomitaLadderPair (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- Linear Tomita/Fourier mirror. -/
  J : V →ₗ[ℝ] V
  /-- Creation operator/state. -/
  creation : V
  /-- Annihilation operator/state. -/
  annihilation : V
  /-- Tomita swaps creation to annihilation. -/
  J_creation : J creation = annihilation
  /-- Tomita swaps annihilation to creation. -/
  J_annihilation : J annihilation = creation

namespace TomitaLadderPair

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (P : TomitaLadderPair V)

/-- The `J`-even Majorana / completed combination. -/
def evenMajorana : V :=
  P.creation + P.annihilation

/-- The `J`-odd imbalance / modular-density combination. -/
def oddDensity : V :=
  P.creation - P.annihilation

/-- The completed Majorana combination is fixed by the Tomita mirror. -/
theorem J_evenMajorana :
    P.J P.evenMajorana = P.evenMajorana := by
  simp [evenMajorana, P.J_creation, P.J_annihilation, add_comm]

/-- The creation/annihilation imbalance is negated by the Tomita mirror. -/
theorem J_oddDensity :
    P.J P.oddDensity = -P.oddDensity := by
  simp [oddDensity, P.J_creation, P.J_annihilation, sub_eq_add_neg]

/-- The even component belongs to the fixed/eigenvalue `+1` sector. -/
def IsEvenSector (x : V) : Prop :=
  P.J x = x

/-- The odd component belongs to the anti-fixed/eigenvalue `-1` sector. -/
def IsOddSector (x : V) : Prop :=
  P.J x = -x

theorem evenMajorana_mem_evenSector :
    P.IsEvenSector P.evenMajorana :=
  P.J_evenMajorana

theorem oddDensity_mem_oddSector :
    P.IsOddSector P.oddDensity :=
  P.J_oddDensity

end TomitaLadderPair

/-! ## Concrete split-Cl(1,1) CAR readout -/

section Concrete

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovFockSuper

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The concrete split-null creation/annihilation operators are Tomita swapped. -/
theorem concrete_tomita_swaps_creation_annihilation :
    tomitaConjOp (E := E) (concreteCARCreation (E := E))
        = concreteCARAnnihilation (E := E)
      ∧ tomitaConjOp (E := E) (concreteCARAnnihilation (E := E))
        = concreteCARCreation (E := E) := by
  exact ⟨tomitaConj_creation_eq_annihilation (E := E),
    tomitaConj_annihilation_eq_creation (E := E)⟩

/-- The concrete Majorana combination `c + a` is Tomita/PHS invariant. -/
theorem concrete_evenMajorana_fixed :
    tomitaConjOp (E := E) (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E))
      = concreteCARCreation (E := E) + concreteCARAnnihilation (E := E) :=
  concrete_majorana_swap_is_phs_invariant (E := E)

/-- The concrete imbalance `c - a` is Tomita/PHS anti-invariant. -/
theorem concrete_oddDensity_anti_fixed :
    tomitaConjOp (E := E) (concreteCARCreation (E := E) - concreteCARAnnihilation (E := E))
      = -(concreteCARCreation (E := E) - concreteCARAnnihilation (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : InfoGeometry.Krein.to_doubled (WithLp.fst u) (WithLp.snd u) = u := by
    apply DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hu]
  unfold tomitaConjOp concreteCARCreation concreteCARAnnihilation
  simp [InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteCreation_apply_to_doubled,
    InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteAnnihilation_apply_to_doubled,
    sub_eq_add_neg]

/--
The concrete creation/annihilation Tomita packet as a theorem-level owner.

This is the closed finite corridor: CAR, Tomita swapping, `J`-even `c+a`, and
`J`-odd `c-a`.
-/
theorem concrete_creation_annihilation_packet :
    IsCARPair (E := E)
      (concreteCARAnnihilation (E := E))
      (concreteCARCreation (E := E))
    ∧
    (tomitaConjOp (E := E) (concreteCARCreation (E := E))
        = concreteCARAnnihilation (E := E)
      ∧ tomitaConjOp (E := E) (concreteCARAnnihilation (E := E))
        = concreteCARCreation (E := E))
    ∧
    tomitaConjOp (E := E) (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E))
      = concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)
    ∧
    tomitaConjOp (E := E) (concreteCARCreation (E := E) - concreteCARAnnihilation (E := E))
      = -(concreteCARCreation (E := E) - concreteCARAnnihilation (E := E)) :=
  ⟨concrete_car_pair (E := E), concrete_tomita_swaps_creation_annihilation (E := E),
    concrete_evenMajorana_fixed (E := E), concrete_oddDensity_anti_fixed (E := E)⟩

/--
The concrete CAR pair, Tomita swap, and even/odd decomposition in one reusable
packet.
-/
structure ConcreteCreationAnnihilationReadout where
  car_pair :
    IsCARPair (E := E)
      (concreteCARAnnihilation (E := E))
      (concreteCARCreation (E := E))
  swapped :
    tomitaConjOp (E := E) (concreteCARCreation (E := E))
        = concreteCARAnnihilation (E := E)
      ∧ tomitaConjOp (E := E) (concreteCARAnnihilation (E := E))
        = concreteCARCreation (E := E)
  even_fixed :
    tomitaConjOp (E := E) (concreteCARCreation (E := E) + concreteCARAnnihilation (E := E))
      = concreteCARCreation (E := E) + concreteCARAnnihilation (E := E)
  odd_anti_fixed :
    tomitaConjOp (E := E) (concreteCARCreation (E := E) - concreteCARAnnihilation (E := E))
      = -(concreteCARCreation (E := E) - concreteCARAnnihilation (E := E))

/-- Constructor for the concrete split-`Cl(1,1)` creation/annihilation readout. -/
def concreteCreationAnnihilationReadout :
    ConcreteCreationAnnihilationReadout (E := E) where
  car_pair := concrete_car_pair (E := E)
  swapped := concrete_tomita_swaps_creation_annihilation (E := E)
  even_fixed := concrete_evenMajorana_fixed (E := E)
  odd_anti_fixed := concrete_oddDensity_anti_fixed (E := E)

end Concrete

end InfoGeometry.Canonical.CreationAnnihilationTomitaBridge
