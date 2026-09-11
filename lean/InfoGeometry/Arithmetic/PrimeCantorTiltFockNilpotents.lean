import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation
import InfoGeometry.Canonical.OperatorSurgery

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
    (u - v) * (u - v) = -(1 : R) := by
  have hvu : v * u = 1 - u * v := by
    rw [← hcar]
    noncomm_ring
  have huv : u * v = 1 - v * u := by
    rw [← hcar]
    noncomm_ring
  refine ⟨?_, ?_, ?_, ?_, hcar, ?_, ?_⟩
  · calc
      (u * v) * (u * v) = u * (v * u) * v := by
        noncomm_ring
      _ = u * (1 - u * v) * v := by
        rw [hvu]
      _ = (u * (1 - u * v)) * v := by
        rw [mul_assoc]
      _ = (u * 1 - u * (u * v)) * v := by
        rw [mul_sub]
      _ = (u - (u * u) * v) * v := by
        rw [mul_one, mul_assoc]
      _ = (u - 0 * v) * v := by
        rw [hu]
      _ = u * v := by
        simp
  · calc
      (v * u) * (v * u) = v * (u * v) * u := by
        noncomm_ring
      _ = v * (1 - v * u) * u := by
        rw [huv]
      _ = (v * (1 - v * u)) * u := by
        rw [mul_assoc]
      _ = (v * 1 - v * (v * u)) * u := by
        rw [mul_sub]
      _ = (v - (v * v) * u) * u := by
        rw [mul_one, mul_assoc]
      _ = (v - 0 * u) * u := by
        rw [hv]
      _ = v * u := by
        simp
  · calc
      (u * v) * (v * u) = u * (v * v) * u := by
        noncomm_ring
      _ = 0 := by
        rw [hv]
        simp
  · calc
      (v * u) * (u * v) = v * (u * u) * v := by
        noncomm_ring
      _ = 0 := by
        rw [hu]
        simp
  · calc
      (u + v) * (u + v)
          = u * u + (u * v + v * u) + v * v := by
            noncomm_ring
      _ = 0 + 1 + 0 := by
            rw [hu, hv, hcar]
      _ = 1 := by
            simp
  · calc
      (u - v) * (u - v)
          = u * u - (u * v + v * u) + v * v := by
            noncomm_ring
      _ = 0 - 1 + 0 := by
            rw [hu, hv, hcar]
      _ = -(1 : R) := by
            simp

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
    (u - v) * (u - v) = -(1 : R) := by
  constructor
  · calc
      (u + v) * (u + v)
          = u * u + (u * v + v * u) + v * v := by
            noncomm_ring
      _ = 0 + 1 + 0 := by
            rw [hu, hv, hcar]
      _ = 1 := by
            simp
  · calc
      (u - v) * (u - v)
          = u * u - (u * v + v * u) + v * v := by
            noncomm_ring
      _ = 0 - 1 + 0 := by
            rw [hu, hv, hcar]
      _ = -(1 : R) := by
            simp

/-! The archived Cantor/Fock surface exposed these generic Drazin laws under
this namespace. Their owner is the native operator-surgery module; these
projections preserve the old theorem names without rebuilding a second Drazin
packet here. -/

theorem drazin_indexOne_projector_idempotent
    {R : Type*} [Ring R]
    {A D : R}
    (hDAD : D * A * D = D) :
    (A * D) * (A * D) = A * D :=
  InfoGeometry.Canonical.OperatorSurgery.drazin_indexOne_projector_idempotent_ring hDAD

theorem drazin_indexOne_annihilates_right_defect
    {R : Type*} [Ring R]
    {A D : R}
    (hADA : A * D * A = A)
    (hcomm : A * D = D * A) :
    A * (1 - A * D) = 0 :=
  InfoGeometry.Canonical.OperatorSurgery.drazin_indexOne_annihilates_right_defect_ring
    hADA hcomm

theorem drazin_indexOne_annihilates_left_defect
    {R : Type*} [Ring R]
    {A D : R}
    (hADA : A * D * A = A) :
    (1 - A * D) * A = 0 :=
  InfoGeometry.Canonical.OperatorSurgery.drazin_indexOne_annihilates_left_defect_ring hADA

end InfoGeometry.Arithmetic.PrimeCantorTiltFockNilpotents
