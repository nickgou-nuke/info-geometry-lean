import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Arithmetic.PrimeMajoranaBitFlip
import InfoGeometry.Arithmetic.PrimeBooleanCube

/-!
# InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation

Finite tilt/switch Fock representation on the prime-indexed Cantor cube.

This module gives the native finite representation layer:

* `switchOp p` is the prime-axis Majorana bit flip;
* `tiltOp p` is the Rademacher sign / occupation-parity operator;
* `tiltOp p` and `switchOp p` anticommute;
* `switchOp p` and `tiltOp p` both square to the identity;
* `splitDOp p = switchOp p ∘ tiltOp p` squares to `-1`;
* `switchOp p ∘ splitDOp p = tiltOp p`.

This is the finite Fock/Cantor representation of the local `Cl(1,1)` atom.

No infinite CAR algebra.
No CCR algebra.
No analytic continuation.
No Hilbert-Polya/RH claim.
-/

noncomputable section

open scoped BigOperators

namespace PrimeCantorTiltFockRepresentation

open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.PrimeMajoranaBitFlip
open InfoGeometry.Arithmetic.PrimeBooleanCube

/-! ## 1. Fields on the finite Cantor cube -/

/-- Real-valued fields on the finite Boolean/Cantor cube. -/
@[rep_depth thermo]
abbrev CubeField (P : PrimeRegister) (R : Type*) :=
  Vertex P → R

/-- Operator composition on cube fields. -/
@[rep_depth thermo]
def compOp {P : PrimeRegister} {R : Type*}
    (A B : CubeField P R → CubeField P R) :
    CubeField P R → CubeField P R :=
  fun f => A (B f)

/-- Identity operator on cube fields. -/
@[rep_depth thermo]
def idOp {P : PrimeRegister} {R : Type*} :
    CubeField P R → CubeField P R :=
  fun f => f

/-- Additive negative of an operator on cube fields. -/
@[rep_depth thermo]
def negOp {P : PrimeRegister} {R : Type*} [Neg R]
    (A : CubeField P R → CubeField P R) :
    CubeField P R → CubeField P R :=
  fun f v => - A f v


/-! ## 2. Switch and tilt operators -/

/--
Prime-axis switch operator.

This is pullback along the existing Majorana bit flip:

`(S_p f)(v) = f(flip_p(v))`.
-/
@[rep_depth thermo]
def switchOp {P : PrimeRegister} {R : Type*} [DecidableEq ℕ]
    (p : ℕ) (hp : p ∈ P.primes) :
    CubeField P R → CubeField P R :=
  fun f v => f (flipVertex (P := P) p hp v)

/--
Prime-axis tilt/Rademacher operator.

`(T_p f)(v) = -f(v)` if `p ∈ v`, and `f(v)` otherwise.
-/
@[rep_depth thermo]
def tiltOp {P : PrimeRegister} {R : Type*} [Neg R]
    (p : ℕ) :
    CubeField P R → CubeField P R :=
  fun f v => if p ∈ v.val then - f v else f v

/--
The switch operator squares to the identity.
-/
@[bridge_target_tag, rep_depth thermo]
theorem switchOp_sq
    {P : PrimeRegister} {R : Type*} [DecidableEq ℕ]
    (p : ℕ) (hp : p ∈ P.primes) :
    compOp (switchOp (P := P) (R := R) p hp)
      (switchOp (P := P) (R := R) p hp)
      =
    idOp := by
  funext f v
  simp [compOp, switchOp, idOp, PrimeBooleanCube.flipVertex_involutive,
    hp]

/--
The tilt operator squares to the identity.
-/
@[bridge_target_tag, rep_depth thermo]
theorem tiltOp_sq
    {P : PrimeRegister} {R : Type*} [AddGroup R]
    (p : ℕ) :
    compOp (tiltOp (P := P) (R := R) p)
      (tiltOp (P := P) (R := R) p)
      =
    idOp := by
  funext f v
  by_cases h : p ∈ v.val <;>
    simp [compOp, tiltOp, idOp, h]

/--
Tilt and switch anticommute:

`T_p S_p = - S_p T_p`.
-/
@[bridge_target_tag, rep_depth thermo]
theorem tilt_switch_anticomm
    {P : PrimeRegister} {R : Type*} [AddGroup R] [DecidableEq ℕ]
    (p : ℕ) (hp : p ∈ P.primes) :
    compOp (tiltOp (P := P) (R := R) p)
      (switchOp (P := P) (R := R) p hp)
      =
    negOp
      (compOp (switchOp (P := P) (R := R) p hp)
        (tiltOp (P := P) (R := R) p)) := by
  funext f v
  by_cases h : p ∈ v.val <;>
    simp [compOp, tiltOp, switchOp, negOp, h,
      PrimeBooleanCube.mem_flipVertex_self (P := P) (p := p) (hp := hp) v]


/-! ## 3. Local split-Clifford atom from tilt/switch -/

/--
The elliptic split-Majorana operator

`d_p = switch_p ∘ tilt_p`.

With `c_p = switch_p`, this gives a finite `Cl(1,1)` atom.
-/
@[rep_depth thermo]
def splitDOp {P : PrimeRegister} {R : Type*} [Neg R] [DecidableEq ℕ]
    (p : ℕ) (hp : p ∈ P.primes) :
    CubeField P R → CubeField P R :=
  compOp (switchOp (P := P) (R := R) p hp)
    (tiltOp (P := P) (R := R) p)

/--
The split operator `d_p = S_p T_p` squares to `-1`.
-/
@[bridge_target_tag, rep_depth thermo]
theorem splitDOp_sq
    {P : PrimeRegister} {R : Type*} [AddGroup R] [DecidableEq ℕ]
    (p : ℕ) (hp : p ∈ P.primes) :
    compOp (splitDOp (P := P) (R := R) p hp)
      (splitDOp (P := P) (R := R) p hp)
      =
    negOp idOp := by
  funext f v
  by_cases h : p ∈ v.val <;>
    simp [splitDOp, compOp, switchOp, tiltOp, negOp, idOp, h,
      PrimeBooleanCube.mem_flipVertex_self (P := P) (p := p) (hp := hp) v,
      PrimeBooleanCube.flipVertex_involutive (P := P) (p := p) (hp := hp) v]

/--
The local parity `c_p d_p` is exactly the tilt operator.
-/
@[bridge_target_tag, rep_depth thermo]
theorem switch_splitDOp_eq_tilt
    {P : PrimeRegister} {R : Type*} [AddGroup R] [DecidableEq ℕ]
    (p : ℕ) (hp : p ∈ P.primes) :
    compOp (switchOp (P := P) (R := R) p hp)
      (splitDOp (P := P) (R := R) p hp)
      =
    tiltOp (P := P) (R := R) p := by
  funext f v
  by_cases h : p ∈ v.val <;>
    simp [splitDOp, compOp, switchOp, tiltOp, h,
      PrimeBooleanCube.mem_flipVertex_self (P := P) (p := p) (hp := hp) v,
      PrimeBooleanCube.flipVertex_involutive (P := P) (p := p) (hp := hp) v]


end PrimeCantorTiltFockRepresentation
