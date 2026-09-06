import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.CliffordAlgebra.Star
import Mathlib.Tactic
import InfoGeometry.Canonical.HodgeDrazinEnvelope
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.VarlamovClifford

Theorem-safe Varlamov/Drazin Clifford socket.

The finite Clifford automorphism side of Varlamov's paper is not rewrapped
here.  It is imported directly from mathlib:

* `CliffordAlgebra.involute` for the grade involution;
* `CliffordAlgebra.reverse` for reversion;
* `star = reverse ∘ involute` from `CliffordAlgebra.Star`;
* `CliffordAlgebra.SpinGroup` for the canonical spin group substrate.

This module formalizes the algebraic part only:

* a degenerate Clifford-style carrier with a nilpotent distinguished direction;
* a Varlamov-style Drazin adjoint `bar x = J * star x * JD`;
* covariance of the Hodge-Drazin envelope under this adjoint, when the required
  commutation witnesses are supplied;
* the universal exterior-derivative law for idempotents:
  `p * d p * p = 0`.

It does not assert a concrete PGA/Clifford algebra instance or a full analytic
BRST/Fredholm/PDE theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.VarlamovClifford

open InfoGeometry.Canonical.HodgeDrazinEnvelope

/--
Degenerate Clifford-style generators for a toy `Cl(n,0,1)` chart.

The concrete multiplication table is supplied as fields.  This is a local
algebraic socket, not a global Clifford algebra construction.
-/
@[rep_depth operator]
structure DegenerateCliffordChart
    (Op : Type*) [Ring Op] where
  e0 : Op
  e1 : Op
  e2 : Op
  e3 : Op

  e0_square : e0 * e0 = 0
  e1_square : e1 * e1 = 1
  e2_square : e2 * e2 = 1
  e3_square : e3 * e3 = 1

  anti_e01 : e0 * e1 = - (e1 * e0)
  anti_e02 : e0 * e2 = - (e2 * e0)
  anti_e03 : e0 * e3 = - (e3 * e0)
  anti_e12 : e1 * e2 = - (e2 * e1)
  anti_e13 : e1 * e3 = - (e3 * e1)
  anti_e23 : e2 * e3 = - (e3 * e2)

namespace DegenerateCliffordChart

variable {Op : Type*} [Ring Op]
variable (C : DegenerateCliffordChart Op)

/-- Nilpotent light-front bivector `A = e0 e1`. -/
@[rep_depth operator]
def nilpotentSignal : Op :=
  C.e0 * C.e1

/-- The nilpotent light-front signal squares to zero. -/
@[rep_depth operator]
theorem nilpotentSignal_sq_eq_zero :
    C.nilpotentSignal * C.nilpotentSignal = 0 := by
  unfold nilpotentSignal
  have h10 : C.e1 * C.e0 = - (C.e0 * C.e1) := by
    simpa using (congrArg Neg.neg C.anti_e01).symm
  calc
    (C.e0 * C.e1) * (C.e0 * C.e1)
        = C.e0 * (C.e1 * C.e0) * C.e1 := by noncomm_ring
    _ = C.e0 * (-(C.e0 * C.e1)) * C.e1 := by rw [h10]
    _ = -((C.e0 * C.e0) * (C.e1 * C.e1)) := by noncomm_ring
    _ = 0 := by rw [C.e0_square]; simp

/-- Regularized signal `A = 1 + e0 e1`. -/
@[rep_depth operator]
def regularizedSignal : Op :=
  1 + C.e0 * C.e1

/-- If `N^2 = 0`, then `(1 + N) * (1 - N) = 1`. -/
@[rep_depth operator]
theorem regularizedSignal_mul_inverseCandidate :
    C.regularizedSignal * (1 - C.e0 * C.e1) = 1 := by
  have hN : (C.e0 * C.e1) * (C.e0 * C.e1) = 0 := C.nilpotentSignal_sq_eq_zero
  unfold regularizedSignal
  noncomm_ring [hN]

/-- If `N^2 = 0`, then `(1 - N) * (1 + N) = 1`. -/
@[rep_depth operator]
theorem inverseCandidate_mul_regularizedSignal :
    (1 - C.e0 * C.e1) * C.regularizedSignal = 1 := by
  have hN : (C.e0 * C.e1) * (C.e0 * C.e1) = 0 := C.nilpotentSignal_sq_eq_zero
  unfold regularizedSignal
  noncomm_ring [hN]

end DegenerateCliffordChart

/--
Varlamov/Drazin carrier over the Hodge-Drazin double filtration.

`J` and `JD` are the metric-adjoint operator and its Drazin-style inverse data.
The signal and harmonic projectors are inherited from the theorem-safe
Hodge-Drazin carrier.
-/
@[rep_depth operator]
structure VarlamovCarrier
    (Op : Type*) [Ring Op] [StarRing Op] where
  carrier : HodgeDrazinCarrier Op

  J : Op
  JD : Op

  J_commute : J * JD = JD * J
  J_Drazin_reflexive : JD * J * JD = JD

namespace VarlamovCarrier

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (C : VarlamovCarrier Op)

/-- Signal/Drazin horizon projector `p_A`. -/
@[rep_depth operator]
def p_A : Op :=
  C.carrier.signal.p

/-- Frequency harmonic/generalized-zero projector `H_L`. -/
@[rep_depth operator]
def H_L : Op :=
  C.carrier.frequency.P_harm

/-- Hodge-Drazin physical envelope `H_L p_A x p_A H_L`. -/
@[rep_depth operator]
def physicalEnvelope (x : Op) : Op :=
  C.H_L * (C.p_A * x * C.p_A) * C.H_L

/-- Varlamov-style Drazin adjoint: `bar x = J * star x * JD`. -/
@[rep_depth operator]
def varlamovAdjoint (x : Op) : Op :=
  C.J * star x * C.JD

/-- The Drazin horizon projector is idempotent. -/
@[rep_depth operator]
theorem p_A_idempotent :
    C.p_A * C.p_A = C.p_A :=
  C.carrier.signal.p_idempotent

/-- The harmonic projector is idempotent. -/
@[rep_depth operator]
theorem H_L_idempotent :
    C.H_L * C.H_L = C.H_L :=
  C.carrier.frequency.P_harm_idempotent

/-- The Drazin horizon projector is self-adjoint. -/
@[rep_depth operator]
theorem p_A_self_adjoint :
    star C.p_A = C.p_A :=
  C.carrier.signal.p_self_adjoint

/-- The harmonic projector is self-adjoint. -/
@[rep_depth operator]
theorem H_L_self_adjoint :
    star C.H_L = C.H_L :=
  C.carrier.frequency.P_harm_self_adjoint

/--
Witness packet for covariance of the Varlamov adjoint through the Hodge-Drazin
envelope.

For a concrete Clifford/PGA model this can be proved from the relevant
commutation and anti-involution laws.  The abstract noncommutative carrier keeps
that compatibility explicit.
-/
@[rep_depth operator]
structure EnvelopeVarlamovCovariance where
  covariance : ∀ x : Op,
    C.varlamovAdjoint (C.physicalEnvelope x) =
      C.physicalEnvelope (C.varlamovAdjoint x)

/-- Re-export of the supplied Varlamov/envelope covariance law. -/
@[rep_depth operator]
theorem physicalEnvelope_varlamov_covariant
    (W : C.EnvelopeVarlamovCovariance)
    (x : Op) :
    C.varlamovAdjoint (C.physicalEnvelope x) =
      C.physicalEnvelope (C.varlamovAdjoint x) :=
  W.covariance x

end VarlamovCarrier

/-- Exterior derivative on an operator ring, represented by Leibniz witnesses. -/
@[rep_depth operator]
structure ExteriorDerivative
    (Op : Type*) [Ring Op] where
  d : Op → Op
  d_add : ∀ x y, d (x + y) = d x + d y
  d_mul : ∀ x y, d (x * y) = d x * y + x * d y

namespace ExteriorDerivative

variable {Op : Type*} [Ring Op]
variable (D : ExteriorDerivative Op)

/-- Differentiating an idempotent gives `d p = d p * p + p * d p`. -/
@[rep_depth operator]
theorem d_idempotent_eq
    {p : Op}
    (hp : p * p = p) :
    D.d p = D.d p * p + p * D.d p := by
  have h := D.d_mul p p
  have hleft : D.d (p * p) = D.d p := by rw [hp]
  exact hleft ▸ h

/-- The differential of an idempotent is off-diagonal: `p * d p * p = 0`. -/
@[rep_depth operator]
theorem idempotent_d_off_diagonal
    {p : Op}
    (hp : p * p = p) :
    p * D.d p * p = 0 := by
  have hd : D.d p = D.d p * p + p * D.d p := D.d_idempotent_eq hp
  let X : Op := p * D.d p * p
  have htwo : X = X + X := by
    dsimp [X]
    calc
      p * D.d p * p
          = p * (D.d p * p + p * D.d p) * p := by
              exact congrArg (fun y => p * y * p) hd
      _ = (p * (D.d p * p) + p * (p * D.d p)) * p := by
              rw [mul_add]
      _ = p * (D.d p * p) * p + p * (p * D.d p) * p := by
              rw [add_mul]
      _ = p * D.d p * (p * p) + (p * p) * D.d p * p := by
              simp [mul_assoc]
      _ = p * D.d p * p + p * D.d p * p := by
              rw [hp]
  have hcancel := congrArg (fun y : Op => y - X) htwo
  have hzero : (0 : Op) = X := by
    simpa [sub_eq_add_neg, add_assoc] using hcancel
  exact hzero.symm

end ExteriorDerivative

/-- Differential off-diagonality for the Varlamov/Drazin horizon projector. -/
@[rep_depth operator]
theorem d_pA_off_diagonal
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : VarlamovCarrier Op)
    (D : ExteriorDerivative Op) :
    C.p_A * D.d C.p_A * C.p_A = 0 :=
  D.idempotent_d_off_diagonal C.p_A_idempotent

/-- Differential off-diagonality for the harmonic/generalized-zero projector. -/
@[rep_depth operator]
theorem d_HL_off_diagonal
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : VarlamovCarrier Op)
    (D : ExteriorDerivative Op) :
    C.H_L * D.d C.H_L * C.H_L = 0 :=
  D.idempotent_d_off_diagonal C.H_L_idempotent

end InfoGeometry.Canonical.VarlamovClifford
