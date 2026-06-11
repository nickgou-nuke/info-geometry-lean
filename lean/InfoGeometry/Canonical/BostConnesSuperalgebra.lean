import InfoGeometry.Canonical.BostConnesSuperalgebraConstructive

/-!
# Bost--Connes Superalgebra: Finite Constructive API

This module is the public theorem-safe entry point for the finite algebraic
Bost--Connes/Witten-parity corridor.

It deliberately proves only the closed algebraic layer:
* a single regulated Euler factor is inverted by the local Witten factor;
* supertrace is evaluation after a supplied parity involution;
* invariant states vanish on explicitly parity-odd elements;
* a supplied parity-equivariant abstract Cuntz carrier gives a parity-odd CAR
  generator with zero invariant-state supertrace.

No infinite UHF algebra, profinite topology, KMS phase transition, BEC theorem,
Galois action, Tate adelic theorem, zeta analytic continuation, or RH consequence
is asserted here.

#### BUCKET 1: CLOSED FINITE THEOREMS
`local_boson_mul_wittenFactor`, `wittenFactor_mul_local_boson`, and the
public readbacks of the constructive supertrace/parity cancellation theorems.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The Cuntz/CAR supertrace theorem depends on an explicit
`ParityEquivariantCuntzCarrier` and an explicit parity-invariant algebraic
state.

#### BUCKET 3: OPEN CLOSURE DEBT
Infinite Cuntz/UHF C*-completion, Bost--Connes KMS simplex, Galois symmetry,
Tate adelic functional equation, thermodynamic phase transition, and zeta/RH
interpretations.
-/

noncomputable section

namespace InfoGeometry.Canonical.BostConnesSuperalgebra

open InfoGeometry.Canonical.BostConnesSuperalgebraConstructive

/-! ## Public aliases for the constructive parity API -/

abbrev StarWittenParity (A : Type*) [Ring A] [StarRing A] :=
  InfoGeometry.Canonical.BostConnesSuperalgebraConstructive.StarWittenParity A

abbrev AlgebraicState (A : Type*) [Ring A] :=
  InfoGeometry.Canonical.BostConnesSuperalgebraConstructive.AlgebraicState A

abbrev ParityEquivariantCuntzCarrier (A : Type*) [Ring A] [StarRing A] :=
  InfoGeometry.Canonical.BostConnesSuperalgebraConstructive.ParityEquivariantCuntzCarrier A

def supertrace
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A) (x : A) : ℂ :=
  InfoGeometry.Canonical.BostConnesSuperalgebraConstructive.supertrace P φ x

def StateParityInvariant
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A) : Prop :=
  InfoGeometry.Canonical.BostConnesSuperalgebraConstructive.StateParityInvariant P φ

def StateParityAntiinvariant
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A) : Prop :=
  InfoGeometry.Canonical.BostConnesSuperalgebraConstructive.StateParityAntiinvariant P φ

def ParityEven
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (x : A) : Prop :=
  InfoGeometry.Canonical.BostConnesSuperalgebraConstructive.ParityEven P x

def ParityOdd
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (x : A) : Prop :=
  InfoGeometry.Canonical.BostConnesSuperalgebraConstructive.ParityOdd P x

/-! ## Local finite Euler/Witten factor -/

/-- Local bosonic Euler factor `(1 - x)⁻¹`. -/
def localBosonFactor {R : Type*} [Field R] (x : R) : R :=
  (1 - x)⁻¹

/-- Local Witten/Möbius signed factor `1 - x`. -/
def localWittenFactor {R : Type*} [Field R] (x : R) : R :=
  1 - x

/-- The regulated local boson factor is inverted by the Witten factor. -/
theorem local_boson_mul_wittenFactor
    {R : Type*} [Field R] (x : R) (h : 1 - x ≠ 0) :
    localBosonFactor x * localWittenFactor x = 1 := by
  simp [localBosonFactor, localWittenFactor, inv_mul_cancel₀ h]

/-- Same local inverse identity with factors reversed. -/
theorem wittenFactor_mul_local_boson
    {R : Type*} [Field R] (x : R) (h : 1 - x ≠ 0) :
    localWittenFactor x * localBosonFactor x = 1 := by
  simp [localBosonFactor, localWittenFactor, mul_inv_cancel₀ h]

/-! ## Public supertrace cancellation readbacks -/

theorem supertrace_eq_state_of_invariant
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A)
    (hφ : StateParityInvariant P φ) (x : A) :
    supertrace P φ x = φ x :=
  InfoGeometry.Canonical.BostConnesSuperalgebraConstructive.supertrace_eq_state_of_invariant
    P φ hφ x

theorem supertrace_eq_neg_state_of_antiinvariant
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A)
    (hφ : StateParityAntiinvariant P φ) (x : A) :
    supertrace P φ x = -φ x :=
  InfoGeometry.Canonical.BostConnesSuperalgebraConstructive.supertrace_eq_neg_state_of_antiinvariant
    P φ hφ x

/-- A parity-invariant state vanishes on explicitly parity-odd elements. -/
theorem invariant_state_vanishes_on_parity_odd
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A)
    (hφ : StateParityInvariant P φ) {x : A} (hx : ParityOdd P x) :
    φ x = 0 :=
  InfoGeometry.Canonical.BostConnesSuperalgebraConstructive.state_vanishes_on_parity_odd
    P φ hφ hx

/-- Supertrace cancellation for parity-invariant states on parity-odd elements. -/
theorem invariant_state_supertrace_parity_odd_eq_zero
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A)
    (hφ : StateParityInvariant P φ) {x : A} (hx : ParityOdd P x) :
    supertrace P φ x = 0 :=
  InfoGeometry.Canonical.BostConnesSuperalgebraConstructive.supertrace_eq_zero_of_invariant_state_on_odd
    P φ hφ hx

/-- The Cuntz-derived CAR generator is parity-odd under an explicit branch grading. -/
theorem cuntz_carFromCuntz_parity_odd
    {Op : Type*} [Ring Op] [StarRing Op]
    (E : ParityEquivariantCuntzCarrier Op) :
    ParityOdd E.parity (carFromCuntz E.cuntz) :=
  InfoGeometry.Canonical.BostConnesSuperalgebraConstructive.ParityEquivariantCuntzCarrier.carFromCuntz_parity_odd E

/-- The Cuntz-derived CAR generator has zero supertrace for invariant states. -/
theorem invariant_state_supertrace_carFromCuntz_eq_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (E : ParityEquivariantCuntzCarrier Op)
    (φ : AlgebraicState Op) (hφ : StateParityInvariant E.parity φ) :
    supertrace E.parity φ (carFromCuntz E.cuntz) = 0 :=
  InfoGeometry.Canonical.BostConnesSuperalgebraConstructive.ParityEquivariantCuntzCarrier.invariant_state_supertrace_carFromCuntz_eq_zero
    E φ hφ

end InfoGeometry.Canonical.BostConnesSuperalgebra

end noncomputable section
