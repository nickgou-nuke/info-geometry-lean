/-
InfoGeometry/Canonical/SpectralGeneratorProxy.lean

Bounded proxy sockets for unbounded spectral generators.

This file does not fake an unbounded closed-operator API.  It records bounded
data extracted from a spectral generator and proves the algebraic consequences
that can be proved at this layer.
-/

import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.Canonical.SpectralGeneratorProxy

universe u

/-- Bounded real endomorphisms of the carrier. -/
abbrev EndR (H : Type u) [NormedAddCommGroup H] [NormedSpace ℝ H] : Type u :=
  H →L[ℝ] H

variable {H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

/-! ## 1. Phase-linearity -/

/--
A bounded operator is phase-linear if it commutes with the phase axis `K`.
-/
def PhaseLinear
    (K T : EndR H) : Prop :=
  T.comp K = K.comp T

namespace PhaseLinear

variable {K S T : EndR H}

/-- Pointwise form of phase-linearity. -/
theorem apply
    (hT : PhaseLinear K T)
    (v : H) :
    T (K v) = K (T v) := by
  change (T.comp K) v = (K.comp T) v
  rw [hT]

/-- The phase axis is phase-linear with itself. -/
theorem axis
    (K : EndR H) :
    PhaseLinear K K := by
  rfl

/-- The identity is phase-linear. -/
theorem id
    (K : EndR H) :
    PhaseLinear K (ContinuousLinearMap.id ℝ H) := by
  ext v
  rfl

/-- The zero operator is phase-linear. -/
theorem zero
    (K : EndR H) :
    PhaseLinear K (0 : EndR H) := by
  ext v
  simp

/-- Sum of phase-linear operators is phase-linear. -/
theorem add
    (hS : PhaseLinear K S)
    (hT : PhaseLinear K T) :
    PhaseLinear K (S + T) := by
  ext v
  change S (K v) + T (K v) = K (S v + T v)
  rw [apply hS v, apply hT v]
  simp

/-- Negative of a phase-linear operator is phase-linear. -/
theorem neg
    (hT : PhaseLinear K T) :
    PhaseLinear K (-T) := by
  ext v
  change -T (K v) = K (-T v)
  rw [apply hT v]
  simp

/-- Difference of phase-linear operators is phase-linear. -/
theorem sub
    (hS : PhaseLinear K S)
    (hT : PhaseLinear K T) :
    PhaseLinear K (S - T) := by
  simpa [sub_eq_add_neg] using add hS (neg hT)

/-- Scalar multiple of a phase-linear operator is phase-linear. -/
theorem smul
    (a : ℝ)
    (hT : PhaseLinear K T) :
    PhaseLinear K (a • T) := by
  ext v
  change a • T (K v) = K (a • T v)
  rw [apply hT v]
  simp

/-- Composition of phase-linear operators is phase-linear. -/
theorem comp
    (hS : PhaseLinear K S)
    (hT : PhaseLinear K T) :
    PhaseLinear K (S.comp T) := by
  ext v
  change S (T (K v)) = K (S (T v))
  rw [apply hT v, apply hS (T v)]

end PhaseLinear

/-! ## 2. Phase-resolvent / Cayley datum -/

/--
Bounded resolvent data for the Cayley transform.

This is a bounded proxy for the unbounded expression

`U = (D - K) (D + K)⁻¹`.

The inverse is supplied as bounded data.  No spectral theorem or unbounded
domain calculus is asserted here.
-/
structure PhaseResolventDatum
    (K : EndR H) where
  /-- Bounded proxy for the spectral generator. -/
  D : EndR H

  /-- Bounded inverse of `D + K`. -/
  denomInv : EndR H

  /-- `D` commutes with the phase axis. -/
  D_phase_linear :
    PhaseLinear K D

  /-- Right inverse law. -/
  denom_right_inverse :
    (D + K).comp denomInv = ContinuousLinearMap.id ℝ H

  /-- Left inverse law. -/
  denom_left_inverse :
    denomInv.comp (D + K) = ContinuousLinearMap.id ℝ H

namespace PhaseResolventDatum

variable {K : EndR H}
variable (R : PhaseResolventDatum K)

/-- Numerator of the bounded Cayley transform: `D - K`. -/
def numerator : EndR H :=
  R.D - K

/-- Denominator of the bounded Cayley transform: `D + K`. -/
def denominator : EndR H :=
  R.D + K

/-- Bounded Cayley transform: `U = (D - K) (D + K)⁻¹`. -/
def boundedCayley : EndR H :=
  R.numerator.comp R.denomInv

/-- The Cayley numerator is phase-linear. -/
theorem numerator_phase_linear :
    PhaseLinear K R.numerator := by
  exact PhaseLinear.sub R.D_phase_linear (PhaseLinear.axis K)

/-- The Cayley denominator is phase-linear. -/
theorem denominator_phase_linear :
    PhaseLinear K R.denominator := by
  exact PhaseLinear.add R.D_phase_linear (PhaseLinear.axis K)

/--
The supplied inverse commutes with the phase axis.

This is not a hypothesis: it follows from denominator phase-linearity and the
left/right inverse laws.
-/
theorem denomInv_phase_linear :
    PhaseLinear K R.denomInv := by
  have hDenom : PhaseLinear K R.denominator := R.denominator_phase_linear
  have hRight : R.denominator.comp R.denomInv = ContinuousLinearMap.id ℝ H := by
    simpa [denominator] using R.denom_right_inverse
  have hLeft : R.denomInv.comp R.denominator = ContinuousLinearMap.id ℝ H := by
    simpa [denominator] using R.denom_left_inverse
  ext v
  calc
    R.denomInv (K v)
        = R.denomInv (K (R.denominator (R.denomInv v))) := by
            have hv : R.denominator (R.denomInv v) = v := by
              change (R.denominator.comp R.denomInv) v = v
              rw [hRight]
              rfl
            rw [hv]
    _ = R.denomInv (R.denominator (K (R.denomInv v))) := by
          rw [← PhaseLinear.apply hDenom (R.denomInv v)]
    _ = K (R.denomInv v) := by
          change (R.denomInv.comp R.denominator) (K (R.denomInv v)) = K (R.denomInv v)
          rw [hLeft]
          rfl

/--
The bounded Cayley transform is phase-linear.

This is derived from the phase-linearity of the numerator and the supplied
inverse laws for the phase-linear denominator.
-/
theorem boundedCayley_phase_linear :
    PhaseLinear K R.boundedCayley := by
  exact PhaseLinear.comp R.numerator_phase_linear R.denomInv_phase_linear

end PhaseResolventDatum

/-! ## 3. Bounded transform proxy -/

/--
Baaj-Julg-style bounded transform proxy.

This records a bounded transform `F`, morally

`F = D (1 + D²)^(-1/2)`,

without asserting a concrete functional calculus in this file.
-/
structure BoundedTransformDatum
    (K : EndR H) where
  /-- Bounded transform of a spectral generator. -/
  F : EndR H

  /-- The bounded transform commutes with the phase axis. -/
  F_phase_linear :
    PhaseLinear K F

namespace BoundedTransformDatum

variable {K : EndR H}
variable (B : BoundedTransformDatum K)

end BoundedTransformDatum

/-! ## 4. Abstract adjoint and compact-defect sockets -/

/--
Abstract adjoint datum on bounded endomorphisms.

This avoids hard-wiring a particular Hilbert-space adjoint API into the roadmap
layer while keeping every downstream compact-defect statement bounded.
-/
abbrev OperatorAdjointDatum := EndR H → EndR H

namespace OperatorAdjointDatum

abbrev adj (a : OperatorAdjointDatum (H := H)) : EndR H → EndR H :=
  a

end OperatorAdjointDatum

/--
Bounded Kasparov/Fredholm-cycle socket.

This is intentionally witness-gated.  Compactness, Fredholmness, and
commutator compactness are not consequences of the bounded transform alone.
-/
structure BoundedKasparovCycle
    (A : Type*)
    (K : EndR H) where
  /-- Representation of the coefficient algebra by bounded operators. -/
  rep : A → EndR H

  /-- Bounded transform. -/
  F : EndR H

  /-- Adjoint datum. -/
  adjoint : OperatorAdjointDatum (H := H)

  /-- Compact-operator ideal/socket. -/
  compactIdeal : Set (EndR H)

  /-- The representation preserves the phase axis. -/
  rep_phase_linear :
    ∀ a : A, PhaseLinear K (rep a)

  /-- The bounded transform preserves the phase axis. -/
  F_phase_linear :
    PhaseLinear K F

  /-- Self-adjointness modulo compacts: `F - F* ∈ K(H)`. -/
  selfadjoint_mod_compact :
    F - adjoint.adj F ∈ compactIdeal

  /-- Unit/idempotence modulo compacts: `F² - 1 ∈ K(H)`. -/
  square_mod_compact :
    F.comp F - ContinuousLinearMap.id ℝ H ∈ compactIdeal

  /-- Commutator compactness: `[F, ρ(a)] ∈ K(H)`. -/
  commutator_mod_compact :
    ∀ a : A,
      F.comp (rep a) - (rep a).comp F ∈ compactIdeal

/-! ## 5. Bridge from bounded transform to Kasparov socket -/

/--
Admissibility data for promoting a bounded transform to a bounded Kasparov
cycle.

This collects the compact-defect proofs separately from the construction of the
bounded transform itself.
-/
structure KasparovAdmissibility
    (A : Type*)
    (K : EndR H)
    (B : BoundedTransformDatum K) where
  /-- Representation of the coefficient algebra by bounded operators. -/
  rep : A → EndR H

  /-- Adjoint datum. -/
  adjoint : OperatorAdjointDatum (H := H)

  /-- Compact-operator ideal/socket. -/
  compactIdeal : Set (EndR H)

  /-- The representation preserves the phase axis. -/
  rep_phase_linear :
    ∀ a : A, PhaseLinear K (rep a)

  /-- Self-adjointness defect is compact. -/
  selfadjoint_mod_compact :
    B.F - adjoint.adj B.F ∈ compactIdeal

  /-- Square defect is compact. -/
  square_mod_compact :
    B.F.comp B.F - ContinuousLinearMap.id ℝ H ∈ compactIdeal

  /-- Commutator defects are compact. -/
  commutator_mod_compact :
    ∀ a : A,
      B.F.comp (rep a) - (rep a).comp B.F ∈ compactIdeal

namespace KasparovAdmissibility

variable {A : Type*}
variable {K : EndR H}
variable {B : BoundedTransformDatum K}
variable (Adm : KasparovAdmissibility (H := H) A K B)

/--
Construct a bounded Kasparov cycle once the compact-defect admissibility data
are supplied.
-/
def toBoundedKasparovCycle :
    BoundedKasparovCycle (H := H) A K where
  rep := Adm.rep
  F := B.F
  adjoint := Adm.adjoint
  compactIdeal := Adm.compactIdeal
  rep_phase_linear := Adm.rep_phase_linear
  F_phase_linear := B.F_phase_linear
  selfadjoint_mod_compact := Adm.selfadjoint_mod_compact
  square_mod_compact := Adm.square_mod_compact
  commutator_mod_compact := Adm.commutator_mod_compact

end KasparovAdmissibility

attribute [rep_depth operator]
  EndR
  PhaseLinear
  PhaseLinear.apply
  PhaseLinear.axis
  PhaseLinear.id
  PhaseLinear.zero
  PhaseLinear.add
  PhaseLinear.neg
  PhaseLinear.sub
  PhaseLinear.smul
  PhaseLinear.comp
  PhaseResolventDatum
  PhaseResolventDatum.numerator
  PhaseResolventDatum.denominator
  PhaseResolventDatum.boundedCayley
  PhaseResolventDatum.numerator_phase_linear
  PhaseResolventDatum.denominator_phase_linear
  PhaseResolventDatum.boundedCayley_phase_linear
  BoundedTransformDatum
  OperatorAdjointDatum
  BoundedKasparovCycle
  KasparovAdmissibility
  KasparovAdmissibility.toBoundedKasparovCycle

end InfoGeometry.Canonical.SpectralGeneratorProxy
