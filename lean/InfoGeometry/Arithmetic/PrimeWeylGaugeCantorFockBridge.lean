import Mathlib
import InfoGeometry.Arithmetic.ProjectiveWeylGauge
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeBooleanCube
import InfoGeometry.Arithmetic.PrimeExteriorRepresentation

/-!
# InfoGeometry.Arithmetic.PrimeWeylGaugeCantorFockBridge

Weyl-gauge normalized bridge from raw causal-cone operators to the finite
Cantor/Fock readout lane.

This module does not assert raw CAR/CCR laws before normalization.
It does not prove the infinite Cantor/Fock equivalence theorem.
It does not claim zeta analytic continuation or RH.

What it does provide is the coherence data that:

* raw causal-cone tilt/switch operators are first Weyl/projectively normalized;
* the normalized operators satisfy the local split-`Cl(1,1)` atom;
* square-free Boolean states transport to the exterior/Fock readout;
* the finite Boolean-cube Möbius/Witten readout remains delegated to the
  existing owner surfaces.
-/

noncomputable section

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.Arithmetic.PrimeWeylGaugeCantorFockBridge

open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.PrimeBooleanCube
open InfoGeometry.Arithmetic.PrimeExteriorRepresentation

/--
Raw causal-cone switch data before Weyl/projective normalization.

The raw operators are intentionally not asserted to satisfy Clifford/CAR laws.
-/
@[rep_depth thermo]
structure RawCausalConeSwitchSystem
    (Idx Raw : Type*) where
  Traw : Idx → Raw
  Sraw : Idx → Raw

/--
Weyl-gauge normalization from raw causal-cone switches to normalized
tilt/switch operators.

This is the finite analogue of the projective Weyl normalization pattern
already used in `ProjectiveWeylGauge.lean`.
-/
@[rep_depth thermo]
structure WeylGaugeTiltSwitchNormalization
    (Idx Raw Op : Type*) [Ring Op] where
  raw : RawCausalConeSwitchSystem Idx Raw
  normalize : Raw → Op

  T : Idx → Op
  S : Idx → Op

  T_eq_normalize : ∀ p, T p = normalize (raw.Traw p)
  S_eq_normalize : ∀ p, S p = normalize (raw.Sraw p)

  T_sq : ∀ p, T p * T p = 1
  S_sq : ∀ p, S p * S p = 1

  T_comm : ∀ p q, p ≠ q → T p * T q = T q * T p
  S_comm : ∀ p q, p ≠ q → S p * S q = S q * S p
  T_S_comm_ne : ∀ p q, p ≠ q → T p * S q = S q * T p

  T_S_anticomm : ∀ p, T p * S p = - (S p * T p)

namespace WeylGaugeTiltSwitchNormalization

variable {Idx Raw Op : Type*} [Ring Op]
variable (N : WeylGaugeTiltSwitchNormalization Idx Raw Op)

/-- Local positive split-Majorana component. -/
@[rep_depth thermo]
def c (p : Idx) : Op :=
  N.S p

/-- Local negative split-Majorana component. -/
@[rep_depth thermo]
def d (p : Idx) : Op :=
  N.S p * N.T p

/-- `c_p² = 1`. -/
@[rep_depth thermo]
theorem c_sq (p : Idx) :
    N.c p * N.c p = 1 :=
  N.S_sq p

/-- `d_p² = -1`. -/
@[rep_depth thermo]
theorem d_sq (p : Idx) :
    N.d p * N.d p = -1 := by
  unfold d
  calc
    (N.S p * N.T p) * (N.S p * N.T p)
        = N.S p * (N.T p * N.S p) * N.T p := by
            noncomm_ring
    _ = N.S p * (-(N.S p * N.T p)) * N.T p := by
            rw [N.T_S_anticomm p]
    _ = -((N.S p * N.S p) * (N.T p * N.T p)) := by
            noncomm_ring
    _ = -(1 * 1) := by
            rw [N.S_sq p, N.T_sq p]
    _ = -1 := by
            simp

/-- Same-site split-Majorana anticommutation. -/
@[rep_depth thermo]
theorem c_d_anticomm_same (p : Idx) :
    N.c p * N.d p + N.d p * N.c p = 0 := by
  unfold c d
  calc
    N.S p * (N.S p * N.T p) + (N.S p * N.T p) * N.S p
        = (N.S p * N.S p) * N.T p + N.S p * (N.T p * N.S p) := by
            noncomm_ring
    _ = 1 * N.T p + N.S p * (-(N.S p * N.T p)) := by
            rw [N.S_sq p, N.T_S_anticomm p]
    _ = N.T p - (N.S p * N.S p) * N.T p := by
            noncomm_ring
    _ = N.T p - 1 * N.T p := by
            rw [N.S_sq p]
    _ = 0 := by
            simp

/-- The normalized local parity readout is the tilt generator. -/
@[rep_depth thermo]
theorem localParity_eq_tilt (p : Idx) :
    N.c p * N.d p = N.T p := by
  unfold c d
  rw [← mul_assoc, N.S_sq]
  simp

/-- Distinct-site current commutes with the positive split-Majorana component. -/
@[rep_depth thermo]
theorem localParity_commutes_c_offdiag
    (p q : Idx) (hpq : p ≠ q) :
    (N.c p * N.d p) * N.c q = N.c q * (N.c p * N.d p) := by
  calc
    (N.c p * N.d p) * N.c q
        = N.T p * N.c q := by rw [N.localParity_eq_tilt p]
    _ = N.c q * N.T p := by
        unfold c
        exact N.T_S_comm_ne p q hpq
    _ = N.c q * (N.c p * N.d p) := by rw [N.localParity_eq_tilt p]

/-- Distinct-site current commutes with the negative split-Majorana component. -/
@[rep_depth thermo]
theorem localParity_commutes_d_offdiag
    (p q : Idx) (hpq : p ≠ q) :
    (N.c p * N.d p) * N.d q = N.d q * (N.c p * N.d p) := by
  calc
    (N.c p * N.d p) * N.d q
        = N.T p * N.d q := by rw [N.localParity_eq_tilt p]
    _ = N.d q * N.T p := by
        unfold d
        calc
          N.T p * (N.S q * N.T q)
              = (N.T p * N.S q) * N.T q := by rw [mul_assoc]
          _ = (N.S q * N.T p) * N.T q := by rw [N.T_S_comm_ne p q hpq]
          _ = N.S q * (N.T p * N.T q) := by rw [mul_assoc]
          _ = N.S q * (N.T q * N.T p) := by rw [N.T_comm p q hpq]
          _ = (N.S q * N.T q) * N.T p := by rw [mul_assoc]
    _ = N.d q * (N.c p * N.d p) := by rw [N.localParity_eq_tilt p]

end WeylGaugeTiltSwitchNormalization

/--
Boolean cube to square-free exterior carrier.

The Boolean vertex is already a square-free finite subset of the ambient prime
register, so the exterior carrier is just the underlying finite set.
-/
@[rep_depth thermo]
def toSquareFreePrimeState
    {P : PrimeRegister} (v : Vertex P) :
    SquareFreePrimeState ℕ :=
  v.val

/-- The transported exterior state has the same fermion number. -/
@[rep_depth thermo]
theorem toSquareFreePrimeState_fermionNumber_eq
    {P : PrimeRegister} (v : Vertex P) :
    SquareFreePrimeState.fermionNumber (toSquareFreePrimeState v) = v.val.card :=
  rfl

/-- The transported exterior state has the same local parity sign. -/
@[rep_depth thermo]
theorem toSquareFreePrimeState_localParitySign_eq
    {P : PrimeRegister} (v : Vertex P) (p : ℕ) :
    SquareFreePrimeState.localParitySign p (toSquareFreePrimeState v) =
      PrimeBooleanCube.localParity p v.val := by
  by_cases hp : p ∈ v.val <;>
    simp [toSquareFreePrimeState, SquareFreePrimeState.localParitySign,
      PrimeBooleanCube.localParity, PrimeBooleanCube.occupationInt, hp]

/-- The transported exterior state has the same global chirality readout. -/
@[rep_depth thermo]
theorem toSquareFreePrimeState_Gamma_eq_globalChirality
    {P : PrimeRegister} (v : Vertex P) :
    SquareFreePrimeState.Gamma (toSquareFreePrimeState v) =
      PrimeBooleanCube.globalChirality P v.val := by
  rw [SquareFreePrimeState.Gamma_eq_negOne_pow_fermionNumber]
  rw [PrimeBooleanCube.globalChirality_vertex_eq_fermionParity P v]
  rfl

end InfoGeometry.Arithmetic.PrimeWeylGaugeCantorFockBridge
