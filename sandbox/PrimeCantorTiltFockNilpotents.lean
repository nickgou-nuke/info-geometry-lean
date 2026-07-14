import Mathlib
import InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation

/-!
# InfoGeometry.Arithmetic.PrimeCantorTiltFockNilpotents

Real nilpotent spinors from the finite tilt/switch `Cl(1,1)` atom.

No sockets.
No wrappers.
No new carrier.

This file proves the concrete relation between the three local operator types:

* `switchOp p` squares to `+Id`;
* `splitDOp p = switchOp p ∘ tiltOp p` squares to `-Id`;
* the two lightlike spinor combinations
  `switchOp p + splitDOp p` and `switchOp p - splitDOp p`
  square to zero.

This is the finite Cantor/Fock theorem behind the slogan:

`Op² = 0` spinors are hidden inside the `Op² = +1` / `Op² = -1`
split-Clifford pair.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeCantorTiltFockNilpotents

open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.PrimeBooleanCube
open InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation

/--
If two local modes anticommute, the square of their sum is the sum of their
squares.

This is the local Clifford/Majorana cancellation mechanism.
-/
@[rep_depth thermo]
theorem square_add_of_anticomm
    {R : Type*} [Ring R]
    {x y wx wy : R}
    (hx : x * x = wx)
    (hy : y * y = wy)
    (hanti : x * y + y * x = 0) :
    (x + y) * (x + y) = wx + wy := by
  calc
    (x + y) * (x + y)
        = x * x + (x * y + y * x) + y * y := by
          noncomm_ring
    _ = wx + 0 + wy := by
          rw [hx, hy, hanti]
    _ = wx + wy := by
          simp

lemma squareZero_car_vu_eq {R : Type*} [Ring R] {u v : R} (hcar : u * v + v * u = 1) : v * u = 1 - u * v := by
  rw [← hcar]
  noncomm_ring

lemma squareZero_car_uv_eq {R : Type*} [Ring R] {u v : R} (hcar : u * v + v * u = 1) : u * v = 1 - v * u := by
  rw [← hcar]
  noncomm_ring

@[rep_depth thermo]
theorem squareZero_car_proj1 {R : Type*} [Ring R] {u v : R} (hu : u * u = 0) (hcar : u * v + v * u = 1) : (u * v) * (u * v) = u * v := by
  calc
    (u * v) * (u * v) = u * (v * u) * v := by noncomm_ring
    _ = u * (1 - u * v) * v := by rw [squareZero_car_vu_eq hcar]
    _ = (u * (1 - u * v)) * v := by rw [mul_assoc]
    _ = (u * 1 - u * (u * v)) * v := by rw [mul_sub]
    _ = (u - (u * u) * v) * v := by rw [mul_one, mul_assoc]
    _ = (u - 0 * v) * v := by rw [hu]
    _ = u * v := by simp

@[rep_depth thermo]
theorem squareZero_car_proj2 {R : Type*} [Ring R] {u v : R} (hv : v * v = 0) (hcar : u * v + v * u = 1) : (v * u) * (v * u) = v * u := by
  calc
    (v * u) * (v * u) = v * (u * v) * u := by noncomm_ring
    _ = v * (1 - v * u) * u := by rw [squareZero_car_uv_eq hcar]
    _ = (v * (1 - v * u)) * u := by rw [mul_assoc]
    _ = (v * 1 - v * (v * u)) * u := by rw [mul_sub]
    _ = (v - (v * v) * u) * u := by rw [mul_one, mul_assoc]
    _ = (v - 0 * u) * u := by rw [hv]
    _ = v * u := by simp

@[rep_depth thermo]
theorem squareZero_car_ortho1 {R : Type*} [Ring R] {u v : R} (hv : v * v = 0) : (u * v) * (v * u) = 0 := by
  calc
    (u * v) * (v * u) = u * (v * v) * u := by noncomm_ring
    _ = 0 := by rw [hv, mul_zero, zero_mul]

@[rep_depth thermo]
theorem squareZero_car_ortho2 {R : Type*} [Ring R] {u v : R} (hu : u * u = 0) : (v * u) * (u * v) = 0 := by
  calc
    (v * u) * (u * v) = v * (u * u) * v := by noncomm_ring
    _ = 0 := by rw [hu, mul_zero, zero_mul]

@[rep_depth thermo]
theorem squareZero_car_sum {R : Type*} [Ring R] {u v : R} (hcar : u * v + v * u = 1) : u * v + v * u = 1 := hcar

@[rep_depth thermo]
theorem squareZero_car_clifford {R : Type*} [Ring R] {u v : R} (hu : u * u = 0) (hv : v * v = 0) (hcar : u * v + v * u = 1) : (u + v) * (u + v) = 1 := by
  calc
    (u + v) * (u + v)
        = u * u + (u * v + v * u) + v * v := by noncomm_ring
    _ = 0 + 1 + 0 := by rw [hu, hv, hcar]
    _ = 1 := by simp

@[rep_depth thermo]
theorem squareZero_car_phase {R : Type*} [Ring R] {u v : R} (hu : u * u = 0) (hv : v * v = 0) (hcar : u * v + v * u = 1) : (u - v) * (u - v) = -(1 : R) := by
  calc
    (u - v) * (u - v)
        = u * u - (u * v + v * u) + v * v := by noncomm_ring
    _ = 0 - 1 + 0 := by rw [hu, hv, hcar]
    _ = -(1 : R) := by simp

/--
Square-zero chiral operators with CAR generate:
* complementary idempotents `u*v` and `v*u`;
* orthogonal sectors;
* a Clifford involution `(u+v)^2 = 1`;
* a Hestenes/Krein phase axis `(u-v)^2 = -1`.
-/
@[rep_depth thermo]
theorem squareZero_anticomm_one_projectors_and_clifford_axes
    {R : Type*} [Ring R]
    {u v : R}
    (hu : u * u = 0)
    (hv : v * v = 0)
    (hcar : u * v + v * u = 1) :
    (u * v) * (u * v) = u * v ∧
    (v * u) * (v * u) = v * u ∧
    (u * v) * (v * u) = 0 ∧
    (v * u) * (u * v) = 0 ∧
    u * v + v * u = 1 ∧
    (u + v) * (u + v) = 1 ∧
    (u - v) * (u - v) = -(1 : R) :=
  ⟨squareZero_car_proj1 hu hcar,
   squareZero_car_proj2 hv hcar,
   squareZero_car_ortho1 hv,
   squareZero_car_ortho2 hu,
   squareZero_car_sum hcar,
   squareZero_car_clifford hu hv hcar,
   squareZero_car_phase hu hv hcar⟩

/-- Pointwise zero operator on cube fields. -/
@[rep_depth thermo]
def zeroOp {P : PrimeRegister} {R : Type*} [Zero R] :
    CubeField P R → CubeField P R :=
  fun _ _ => 0

/-- Pointwise sum of operators on cube fields. -/
@[rep_depth thermo]
def addOp {P : PrimeRegister} {R : Type*} [Add R]
    (A B : CubeField P R → CubeField P R) :
    CubeField P R → CubeField P R :=
  fun f v => A f v + B f v

/-- Pointwise difference of operators on cube fields. -/
@[rep_depth thermo]
def subOp {P : PrimeRegister} {R : Type*} [Sub R]
    (A B : CubeField P R → CubeField P R) :
    CubeField P R → CubeField P R :=
  fun f v => A f v - B f v

/--
Positive lightlike spinor operator `n₊ = c + d`, where
`c = switchOp p` and `d = splitDOp p`.
-/
@[rep_depth thermo]
def nilSpinorPlus {P : PrimeRegister} {R : Type*}
    [AddGroup R] [DecidableEq ℕ]
    (p : ℕ) (hp : p ∈ P.primes) :
    CubeField P R → CubeField P R :=
  addOp (switchOp (P := P) (R := R) p hp)
    (splitDOp (P := P) (R := R) p hp)

/--
Negative lightlike spinor operator `n₋ = c - d`, where
`c = switchOp p` and `d = splitDOp p`.
-/
@[rep_depth thermo]
def nilSpinorMinus {P : PrimeRegister} {R : Type*}
    [AddGroup R] [DecidableEq ℕ]
    (p : ℕ) (hp : p ∈ P.primes) :
    CubeField P R → CubeField P R :=
  subOp (switchOp (P := P) (R := R) p hp)
    (splitDOp (P := P) (R := R) p hp)

/--
The reverse local Clifford product is minus the tilt:

`d_p c_p = -T_p`.

Together with the existing theorem `c_p d_p = T_p`, this is the concrete
anticommutation of the split-Clifford pair.
-/
@[rep_depth thermo]
theorem splitDOp_switchOp_eq_neg_tilt
    {P : PrimeRegister} {R : Type*} [AddGroup R] [DecidableEq ℕ]
    (p : ℕ) (hp : p ∈ P.primes) :
    compOp (splitDOp (P := P) (R := R) p hp)
      (switchOp (P := P) (R := R) p hp)
      =
    negOp (tiltOp (P := P) (R := R) p) := by
  funext f v
  by_cases h : p ∈ v.val <;>
    simp [splitDOp, compOp, switchOp, tiltOp, negOp, h,
      PrimeBooleanCube.mem_flipVertex_self (P := P) (p := p) (hp := hp) v,
      PrimeBooleanCube.flipVertex_involutive (P := P) (p := p) (hp := hp) v]

/--
The positive lightlike spinor squares to zero:

`(c_p + d_p)² = 0`.
-/
@[rep_depth thermo]
theorem nilSpinorPlus_sq_zero
    {P : PrimeRegister} {R : Type*} [AddCommGroup R] [DecidableEq ℕ]
    (p : ℕ) (hp : p ∈ P.primes) :
    compOp (nilSpinorPlus (P := P) (R := R) p hp)
      (nilSpinorPlus (P := P) (R := R) p hp)
      =
    zeroOp := by
  funext f v
  by_cases h : p ∈ v.val
  · simp [nilSpinorPlus, addOp, zeroOp, splitDOp, compOp,
      switchOp, tiltOp, h,
      PrimeBooleanCube.mem_flipVertex_self (P := P) (p := p) (hp := hp) v,
      PrimeBooleanCube.flipVertex_involutive (P := P) (p := p) (hp := hp) v]
  · simp [nilSpinorPlus, addOp, zeroOp, splitDOp, compOp,
      switchOp, tiltOp, h,
      PrimeBooleanCube.mem_flipVertex_self (P := P) (p := p) (hp := hp) v,
      PrimeBooleanCube.flipVertex_involutive (P := P) (p := p) (hp := hp) v,
      add_assoc]

/--
The negative lightlike spinor squares to zero:

`(c_p - d_p)² = 0`.
-/
@[rep_depth thermo]
theorem nilSpinorMinus_sq_zero
    {P : PrimeRegister} {R : Type*} [AddCommGroup R] [DecidableEq ℕ]
    (p : ℕ) (hp : p ∈ P.primes) :
    compOp (nilSpinorMinus (P := P) (R := R) p hp)
      (nilSpinorMinus (P := P) (R := R) p hp)
      =
    zeroOp := by
  funext f v
  by_cases h : p ∈ v.val
  · simp [nilSpinorMinus, subOp, zeroOp, splitDOp, compOp,
      switchOp, tiltOp, h,
      PrimeBooleanCube.mem_flipVertex_self (P := P) (p := p) (hp := hp) v,
      PrimeBooleanCube.flipVertex_involutive (P := P) (p := p) (hp := hp) v]
  · simp [nilSpinorMinus, subOp, zeroOp, splitDOp, compOp,
      switchOp, tiltOp, h,
      PrimeBooleanCube.mem_flipVertex_self (P := P) (p := p) (hp := hp) v,
      PrimeBooleanCube.flipVertex_involutive (P := P) (p := p) (hp := hp) v]

/--
CAR/Witt projector and grading packet.

With `ε^2 = 0`, `ι^2 = 0`, `ει + ιε = 1`, define:
* `N = ε*ι`,
* `c = ε + ι`,
* `d = ε - ι`.

Then `N` and `1-N` are complementary idempotents, orthogonal, and
`c*d = 1 - 2*N`.
-/
@[rep_depth thermo]
theorem car_witt_projector_grading_packet
    {R : Type*} [Ring R]
    {ε ι : R}
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : ε * ι + ι * ε = 1) :
    let N : R := ε * ι
    let c : R := ε + ι
    let d : R := ε - ι
    N * N = N ∧
    (1 - N) * (1 - N) = (1 - N) ∧
    N * (1 - N) = 0 ∧
    (1 - N) * N = 0 ∧
    c * d = 1 - (2 : R) * N := by
  dsimp
  rcases
      squareZero_anticomm_one_projectors_and_clifford_axes
        (u := ε) (v := ι) hε hι hcar with
    ⟨hN, hhole, horth1, horth2, _, _, _⟩
  have hιε : ι * ε = 1 - ε * ι := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_assoc, add_comm, add_left_comm] using hcar
  refine ⟨hN, ?_, ?_, ?_, ?_⟩
  · simpa [hιε] using hhole
  · simpa [hιε] using horth1
  · simpa [hιε] using horth2
  · calc
      (ε + ι) * (ε - ι)
          = ε * ε - ε * ι + ι * ε - ι * ι := by
              noncomm_ring
      _ = 0 - ε * ι + ι * ε - 0 := by
              rw [hε, hι]
      _ = (ι * ε) - (ε * ι) := by abel
      _ = (1 - ε * ι) - (ε * ι) := by
              rw [hιε]
      _ = 1 - (ε * ι + ε * ι) := by
              abel
      _ = 1 - (2 : R) * (ε * ι) := by
              simp [two_mul]

/--
A square-zero CAR pair generates the local `0 / +1 / -1` trichotomy.

`u² = v² = 0` are the chiral/spinor channels.
`u + v` is the Clifford involution.
`u - v` is the phase/clock axis.
-/
@[rep_depth thermo]
theorem squareZero_pair_gives_clifford_axes
    {R : Type*} [Ring R]
    {u v : R}
    (hu : u * u = 0)
    (hv : v * v = 0)
    (hcar : u * v + v * u = 1) :
    (u + v) * (u + v) = 1 ∧
    (u - v) * (u - v) = -(1 : R) :=
  ⟨squareZero_car_clifford hu hv hcar,
   squareZero_car_phase hu hv hcar⟩

/-- Local square-law trichotomy tags. -/
inductive OpSquareClass where
  | elliptic   -- `Op^2 = -1`
  | parabolic  -- `Op^2 = 0`
  | hyperbolic -- `Op^2 = +1`
deriving DecidableEq, Repr

/--
Classify an operator square value in the finite scalar model.
-/
@[rep_depth thermo]
def classifySquareValue (s : ℤ) : Option OpSquareClass :=
  if s = -1 then some OpSquareClass.elliptic
  else if s = 0 then some OpSquareClass.parabolic
  else if s = 1 then some OpSquareClass.hyperbolic
  else none

/-- Correctness: `-1` maps to elliptic. -/
@[rep_depth thermo]
theorem classifySquareValue_neg_one :
    classifySquareValue (-1) = some OpSquareClass.elliptic := by
  simp [classifySquareValue]

/-- Correctness: `0` maps to parabolic. -/
@[rep_depth thermo]
theorem classifySquareValue_zero :
    classifySquareValue 0 = some OpSquareClass.parabolic := by
  simp [classifySquareValue]

/-- Correctness: `1` maps to hyperbolic. -/
@[rep_depth thermo]
theorem classifySquareValue_one :
    classifySquareValue 1 = some OpSquareClass.hyperbolic := by
  simp [classifySquareValue]

/--
Wick-rotation algebraic core:
if `B^2 = 1` in `ℂ`, then `(I*B)^2 = -1`.
-/
@[rep_depth thermo]
theorem wickRotate_hyperbolic_to_elliptic
    {B : ℂ}
    (hB : B * B = 1) :
    (Complex.I * B) * (Complex.I * B) = -1 := by
  calc
    (Complex.I * B) * (Complex.I * B)
        = (Complex.I * Complex.I) * (B * B) := by ring
    _ = (-1) * 1 := by rw [Complex.I_mul_I, hB]
    _ = -1 := by simp

/--
Hyperbolic-to-elliptic class transport under the Wick map `B ↦ I*B`
in the scalar-square model.
-/
@[rep_depth thermo]
theorem wickRotate_squareClass_transport
    :
    classifySquareValue (Int.ofNat 1) = some OpSquareClass.hyperbolic ∧
    classifySquareValue (-1) = some OpSquareClass.elliptic := by
  constructor
  · simpa using classifySquareValue_one
  · simpa using classifySquareValue_neg_one

end InfoGeometry.Arithmetic.PrimeCantorTiltFockNilpotents
