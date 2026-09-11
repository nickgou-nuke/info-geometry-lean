import InfoGeometry.Canonical.CantorBoundaryCuntzShift
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Constructive Bost--Connes Superalgebra Interface

This module gives the theorem-safe algebraic core of the proposed
Bost--Connes/Cuntz/Witten-parity interface.

The proof boundary is explicit:

* no concrete infinite UHF algebra is postulated;
* no KMS phase transition, BEC statement, or Riemann-hypothesis consequence is
  claimed;
* the algebra carrier, Witten parity, state, and Cuntz equivariance are
  proof-carrying data;
* supertrace cancellation is proved only from the stated parity hypotheses.

#### BUCKET 1: CLOSED FINITE THEOREMS
Parity-state readbacks, invariant/anti-invariant cancellation on parity
odd/even elements, Cuntz-derived CAR nilpotence and anticommutator readbacks,
and invariant-state supertrace cancellation for the Cuntz-derived CAR generator.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The Cuntz/CAR parity theorem depends on a supplied
`ParityEquivariantCuntzCarrier`; state cancellation depends on explicitly
supplied parity-invariance or anti-invariance premises.

#### BUCKET 3: OPEN CLOSURE DEBT
Infinite UHF/C*-completion, Bost--Connes KMS phase transition, Galois action,
BEC interpretation, Tate adelic functional equation, zeta continuation, and
Riemann-hypothesis consequences.
-/

noncomputable section

namespace InfoGeometry.Canonical.BostConnesSuperalgebraConstructive

open InfoGeometry.Topology
open InfoGeometry.Canonical

/-- A star-compatible Witten parity involution on an algebraic carrier. -/
structure StarWittenParity (A : Type*) [Ring A] [StarRing A] where
  parity : A →+* A
  involutive : ∀ x : A, parity (parity x) = x
  map_star : ∀ x : A, parity (star x) = star (parity x)

/-- A normalized additive algebraic state. -/
structure AlgebraicState (A : Type*) [Ring A] where
  val : A →+ ℂ
  map_one : val 1 = 1

instance {A : Type*} [Ring A] : CoeFun (AlgebraicState A) (fun _ => A → ℂ) where
  coe φ := φ.val

/-- The Witten supertrace readout associated to a parity involution. -/
def supertrace
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A) (x : A) : ℂ :=
  φ (P.parity x)

/-- A state is parity-invariant when its readout is unchanged by parity. -/
def StateParityInvariant
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A) : Prop :=
  ∀ x : A, φ (P.parity x) = φ x

/-- A state is parity-anti-invariant when parity flips the readout sign. -/
def StateParityAntiinvariant
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A) : Prop :=
  ∀ x : A, φ (P.parity x) = -φ x

/-- An element is parity-even if it is fixed by the Witten parity. -/
def ParityEven
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (x : A) : Prop :=
  P.parity x = x

/-- An element is parity-odd if parity negates it. -/
def ParityOdd
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (x : A) : Prop :=
  P.parity x = -x

theorem supertrace_eq_state_of_invariant
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A)
    (hφ : StateParityInvariant P φ) (x : A) :
    supertrace P φ x = φ x :=
  hφ x

theorem supertrace_eq_neg_state_of_antiinvariant
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A)
    (hφ : StateParityAntiinvariant P φ) (x : A) :
    supertrace P φ x = -φ x :=
  hφ x

/-- A parity-invariant state vanishes on parity-odd elements. -/
theorem state_vanishes_on_parity_odd
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A)
    (hφ : StateParityInvariant P φ) {x : A} (hx : ParityOdd P x) :
    φ x = 0 := by
  have hneg : φ x = -φ x := by
    calc
      φ x = φ (P.parity x) := (hφ x).symm
      _ = φ (-x) := by rw [hx]
      _ = -φ x := φ.val.map_neg x
  have htwo : (2 : ℂ) * φ x = 0 := by
    calc
      (2 : ℂ) * φ x = φ x + φ x := by ring
      _ = -φ x + φ x := congrArg (fun y => y + φ x) hneg
      _ = 0 := by ring
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- A parity-anti-invariant state vanishes on parity-even elements. -/
theorem state_vanishes_on_parity_even_for_antiinvariant
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A)
    (hφ : StateParityAntiinvariant P φ) {x : A} (hx : ParityEven P x) :
    φ x = 0 := by
  have hneg : φ x = -φ x := by
    calc
      φ x = φ (P.parity x) := by rw [hx]
      _ = -φ x := hφ x
  have htwo : (2 : ℂ) * φ x = 0 := by
    calc
      (2 : ℂ) * φ x = φ x + φ x := by ring
      _ = -φ x + φ x := congrArg (fun y => y + φ x) hneg
      _ = 0 := by ring
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Supertrace cancellation for a parity-invariant state on a parity-odd element. -/
theorem supertrace_eq_zero_of_invariant_state_on_odd
    {A : Type*} [Ring A] [StarRing A]
    (P : StarWittenParity A) (φ : AlgebraicState A)
    (hφ : StateParityInvariant P φ) {x : A} (hx : ParityOdd P x) :
    supertrace P φ x = 0 := by
  rw [supertrace_eq_state_of_invariant P φ hφ x]
  exact state_vanishes_on_parity_odd P φ hφ hx

/--
Proof-carrying Cuntz carrier with Witten parity equivariance.

The left branch is declared parity-even and the right branch parity-odd.  This
is model data, not derived from bare Cuntz relations.
-/
structure ParityEquivariantCuntzCarrier
    (Op : Type*) [Ring Op] [StarRing Op] where
  parity : StarWittenParity Op
  cuntz : CantorCuntzO2Carrier Op
  left_even : ParityEven parity cuntz.S_left
  right_odd : ParityOdd parity cuntz.S_right

namespace ParityEquivariantCuntzCarrier

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (E : ParityEquivariantCuntzCarrier Op)

/-- The Cuntz-derived CAR generator is parity-odd under the supplied branch grading. -/
theorem carFromCuntz_parity_odd :
    ParityOdd E.parity (carFromCuntz E.cuntz) := by
  unfold ParityOdd carFromCuntz
  rw [map_mul, E.parity.map_star, E.left_even, E.right_odd]
  simp

/-- Re-export: the Cuntz-derived CAR generator is nilpotent. -/
theorem carFromCuntz_sq_zero :
    carFromCuntz E.cuntz * carFromCuntz E.cuntz = 0 :=
  InfoGeometry.Canonical.carFromCuntz_sq_eq_zero E.cuntz

/-- Re-export: the Cuntz-derived CAR generator satisfies `{a,a*}=1`. -/
theorem carFromCuntz_anticommutator_star_eq_one :
    cantorAnticommutator (carFromCuntz E.cuntz) (star (carFromCuntz E.cuntz)) = 1 :=
  InfoGeometry.Canonical.carFromCuntz_anticommutator_star_eq_one E.cuntz

/--
If the state is invariant under the supplied Witten parity, then the
Cuntz-derived odd CAR generator has zero supertrace.
-/
theorem invariant_state_supertrace_carFromCuntz_eq_zero
    (φ : AlgebraicState Op) (hφ : StateParityInvariant E.parity φ) :
    supertrace E.parity φ (carFromCuntz E.cuntz) = 0 :=
  supertrace_eq_zero_of_invariant_state_on_odd
    E.parity φ hφ (E.carFromCuntz_parity_odd)

end ParityEquivariantCuntzCarrier

end InfoGeometry.Canonical.BostConnesSuperalgebraConstructive

end noncomputable section
