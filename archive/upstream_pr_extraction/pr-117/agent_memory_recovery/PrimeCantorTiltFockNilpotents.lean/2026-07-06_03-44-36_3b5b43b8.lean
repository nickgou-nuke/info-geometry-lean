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

/--
Nilpotent supercharges generate a Dirac operator whose square is the
super-Laplacian.

`D = Q + Q♯`, `Δ = Q Q♯ + Q♯ Q`, and `D² = Δ`.
-/
@[rep_depth thermo]
theorem superDirac_sq_eq_superLaplacian
    {R : Type*} [Ring R]
    {Q Qsharp : R}
    (hQ : Q * Q = 0)
    (hQsharp : Qsharp * Qsharp = 0) :
    (Q + Qsharp) * (Q + Qsharp) =
      Q * Qsharp + Qsharp * Q := by
  calc
    (Q + Qsharp) * (Q + Qsharp)
        = Q * Q + (Q * Qsharp + Qsharp * Q) + Qsharp * Qsharp := by
          noncomm_ring
    _ = 0 + (Q * Qsharp + Qsharp * Q) + 0 := by
          rw [hQ, hQsharp]
    _ = Q * Qsharp + Qsharp * Q := by
          simp

/--
The left supercharge commutes with the super-Laplacian: `[Q, Δ] = 0`.
-/
@[rep_depth thermo]
theorem supercharge_commutes_superLaplacian
    {R : Type*} [Ring R]
    {Q Qsharp : R}
    (hQ : Q * Q = 0) :
    Q * (Q * Qsharp + Qsharp * Q) =
      (Q * Qsharp + Qsharp * Q) * Q := by
  calc
    Q * (Q * Qsharp + Qsharp * Q)
        = (Q * Q) * Qsharp + Q * Qsharp * Q := by
          noncomm_ring
    _ = 0 * Qsharp + Q * Qsharp * Q := by
          rw [hQ]
    _ = Q * Qsharp * Q := by
          simp
    _ = Q * Qsharp * Q + Qsharp * (Q * Q) := by
          rw [hQ]
          simp
    _ = (Q * Qsharp + Qsharp * Q) * Q := by
          noncomm_ring

/--
The dual supercharge commutes with the super-Laplacian: `[Q♯, Δ] = 0`.
-/
@[rep_depth thermo]
theorem dualSupercharge_commutes_superLaplacian
    {R : Type*} [Ring R]
    {Q Qsharp : R}
    (hQsharp : Qsharp * Qsharp = 0) :
    Qsharp * (Q * Qsharp + Qsharp * Q) =
      (Q * Qsharp + Qsharp * Q) * Qsharp := by
  calc
    Qsharp * (Q * Qsharp + Qsharp * Q)
        = Qsharp * Q * Qsharp + (Qsharp * Qsharp) * Q := by
          noncomm_ring
    _ = Qsharp * Q * Qsharp + 0 * Q := by
          rw [hQsharp]
    _ = Qsharp * Q * Qsharp := by
          simp
    _ = Q * (Qsharp * Qsharp) + Qsharp * Q * Qsharp := by
          rw [hQsharp]
          simp
    _ = (Q * Qsharp + Qsharp * Q) * Qsharp := by
          noncomm_ring

/--
The Dirac operator commutes with its super-Laplacian: `[D, Δ] = 0`.
-/
@[rep_depth thermo]
theorem superDirac_commutes_superLaplacian
    {R : Type*} [Ring R]
    {Q Qsharp : R}
    (hQ : Q * Q = 0)
    (hQsharp : Qsharp * Qsharp = 0) :
    (Q + Qsharp) * (Q * Qsharp + Qsharp * Q) =
      (Q * Qsharp + Qsharp * Q) * (Q + Qsharp) := by
  calc
    (Q + Qsharp) * (Q * Qsharp + Qsharp * Q)
        =
      Q * (Q * Qsharp + Qsharp * Q) +
        Qsharp * (Q * Qsharp + Qsharp * Q) := by
          noncomm_ring
    _ =
      (Q * Qsharp + Qsharp * Q) * Q +
        (Q * Qsharp + Qsharp * Q) * Qsharp := by
          rw [
            supercharge_commutes_superLaplacian (Q := Q) (Qsharp := Qsharp) hQ,
            dualSupercharge_commutes_superLaplacian (Q := Q) (Qsharp := Qsharp) hQsharp
          ]
    _ =
      (Q * Qsharp + Qsharp * Q) * (Q + Qsharp) := by
          noncomm_ring

/--
Supergraded Dirac/Laplacian closure package at one degree:

* `D = Q + Q♯`
* `Δ = Q Q♯ + Q♯ Q`
* `D² = Δ`
* `[Q,Δ]=0`, `[Q♯,Δ]=0`, `[D,Δ]=0`.
-/
@[rep_depth thermo]
def SupergradedClosureAt {R : Type*} [Ring R] (Q Qsharp : R) : Prop :=
  (Q + Qsharp) * (Q + Qsharp) = (Q * Qsharp + Qsharp * Q) ∧
  Q * (Q * Qsharp + Qsharp * Q) = (Q * Qsharp + Qsharp * Q) * Q ∧
  Qsharp * (Q * Qsharp + Qsharp * Q) = (Q * Qsharp + Qsharp * Q) * Qsharp ∧
  (Q + Qsharp) * (Q * Qsharp + Qsharp * Q) =
    (Q * Qsharp + Qsharp * Q) * (Q + Qsharp)

/--
Nilpotent supercharges imply full supergraded Dirac/Laplacian closure.
-/
@[rep_depth thermo]
theorem supergradedClosureAt_of_nilpotent
    {R : Type*} [Ring R]
    {Q Qsharp : R}
    (hQ : Q * Q = 0)
    (hQsharp : Qsharp * Qsharp = 0) :
    SupergradedClosureAt (R := R) Q Qsharp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact superDirac_sq_eq_superLaplacian (Q := Q) (Qsharp := Qsharp) hQ hQsharp
  · exact supercharge_commutes_superLaplacian (Q := Q) (Qsharp := Qsharp) hQ
  · exact dualSupercharge_commutes_superLaplacian (Q := Q) (Qsharp := Qsharp) hQsharp
  · exact superDirac_commutes_superLaplacian (Q := Q) (Qsharp := Qsharp) hQ hQsharp

/--
Bott-periodic recurrence on even degrees:
if a property is closed under `n ↦ n+2`, then it propagates along all even
degrees from degree `0`.
-/
@[rep_depth thermo]
theorem bott_periodic_induction_even
    (P : ℕ → Prop)
    (h0 : P 0)
    (hstep : ∀ n, P n → P (n + 2)) :
    ∀ k, P (2 * k) := by
  intro k
  induction k with
  | zero =>
      simpa using h0
  | succ k ih =>
      have hk : P (2 * k) := ih
      have hnext : P (2 * k + 2) := hstep (2 * k) hk
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext

/--
Full Bott-periodic recurrence:
if a property is closed under `n ↦ n+2`, then seeds at degrees `0` and `1`
propagate to all degrees.
-/
@[rep_depth thermo]
theorem bott_periodic_induction_all
    (P : ℕ → Prop)
    (h0 : P 0)
    (h1 : P 1)
    (hstep : ∀ n, P n → P (n + 2)) :
    ∀ n, P n := by
  intro n
  rcases Nat.even_or_odd n with hEven | hOdd
  · rcases hEven with ⟨k, hk⟩
    rw [hk]
    simpa [two_mul] using bott_periodic_induction_even P h0 hstep k
  · rcases hOdd with ⟨k, hk⟩
    rw [hk]
    have hoddStep : ∀ m, P (m + 1) → P (m + 1 + 2) := by
      intro m hm
      simpa [Nat.add_assoc] using hstep (m + 1) hm
    have hprop : ∀ k, P (2 * k + 1) := by
      intro k
      induction k with
      | zero =>
          simpa using h1
      | succ k ih =>
          have hnext : P (2 * k + 1 + 2) := hoddStep (2 * k) (by simpa [Nat.add_assoc] using ih)
          simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
    simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hprop k

/--
The square of a recursively extended odd supercharge.

For `Qnext = Q + R`, the new square is the old square plus the
odd--odd cross bracket plus the new square.
-/
@[rep_depth thermo]
theorem recursive_supercharge_square
    {A : Type*} [Ring A]
    (Q R : A) :
    (Q + R) * (Q + R) =
      Q * Q + (Q * R + R * Q) + R * R := by
  noncomm_ring

/--
If both odd layers are nilpotent, the recursive supercharge square is exactly
the odd--odd anticommutator.
-/
@[rep_depth thermo]
theorem recursive_nilpotent_supercharge_square_eq_anticommutator
    {A : Type*} [Ring A]
    {Q R : A}
    (hQ : Q * Q = 0)
    (hR : R * R = 0) :
    (Q + R) * (Q + R) = Q * R + R * Q := by
  calc
    (Q + R) * (Q + R)
        = Q * Q + (Q * R + R * Q) + R * R := by
          exact recursive_supercharge_square Q R
    _ = 0 + (Q * R + R * Q) + 0 := by
          rw [hQ, hR]
    _ = Q * R + R * Q := by
          simp

/--
Central-charge extraction from two nilpotent recursive supercharges.
-/
@[rep_depth thermo]
theorem recursive_nilpotent_supercharge_square_eq_centralCharge
    {A : Type*} [Ring A]
    {Q R Z : A}
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hZ : Q * R + R * Q = Z) :
    (Q + R) * (Q + R) = Z := by
  rw [recursive_nilpotent_supercharge_square_eq_anticommutator hQ hR]
  exact hZ

/--
If the odd--odd cross bracket is a central element `Z`, then the recursive
supercharge square is central.
-/
@[rep_depth thermo]
theorem recursive_supercharge_square_is_central
    {A : Type*} [Ring A]
    {Q R Z : A}
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hZ : Q * R + R * Q = Z)
    (hCentral : ∀ X : A, Z * X = X * Z) :
    ∀ X : A, ((Q + R) * (Q + R)) * X = X * ((Q + R) * (Q + R)) := by
  intro X
  rw [recursive_nilpotent_supercharge_square_eq_centralCharge hQ hR hZ]
  exact hCentral X

/--
Finite three-layer expansion: next step toward recursive supercharge towers.
-/
@[rep_depth thermo]
theorem three_supercharge_square
    {A : Type*} [Ring A]
    (Q₁ Q₂ Q₃ : A) :
    (Q₁ + Q₂ + Q₃) * (Q₁ + Q₂ + Q₃) =
      Q₁ * Q₁ + Q₂ * Q₂ + Q₃ * Q₃
      + (Q₁ * Q₂ + Q₂ * Q₁)
      + (Q₁ * Q₃ + Q₃ * Q₁)
      + (Q₂ * Q₃ + Q₃ * Q₂) := by
  noncomm_ring

/--
Odd-odd anticommutator.
-/
@[rep_depth thermo]
def oddAnticomm {A : Type*} [Ring A] (X Y : A) : A := X * Y + Y * X

/--
Finite four-layer supercharge square expansion.

This is the explicit cutoff-4 recursive tower identity:
diagonal squares plus all pairwise odd-odd anticommutators.
-/
@[rep_depth thermo]
theorem four_supercharge_square
    {A : Type*} [Ring A]
    (Q₁ Q₂ Q₃ Q₄ : A) :
    (Q₁ + Q₂ + Q₃ + Q₄) * (Q₁ + Q₂ + Q₃ + Q₄) =
      (Q₁ * Q₁ + Q₂ * Q₂ + Q₃ * Q₃ + Q₄ * Q₄)
      + (Q₁ * Q₂ + Q₂ * Q₁)
      + (Q₁ * Q₃ + Q₃ * Q₁)
      + (Q₁ * Q₄ + Q₄ * Q₁)
      + (Q₂ * Q₃ + Q₃ * Q₂)
      + (Q₂ * Q₄ + Q₄ * Q₂)
      + (Q₃ * Q₄ + Q₄ * Q₃) := by
  noncomm_ring

/--
Finite four-layer nilpotent reduction:
if `Qᵢ^2=0` for all four odd generators, the square is exactly the sum of
pairwise odd-odd anticommutators.
-/
@[rep_depth thermo]
theorem four_nilpotent_supercharge_square_eq_pairwise_oddAnticomm
    {A : Type*} [Ring A]
    {Q₁ Q₂ Q₃ Q₄ : A}
    (h₁ : Q₁ * Q₁ = 0)
    (h₂ : Q₂ * Q₂ = 0)
    (h₃ : Q₃ * Q₃ = 0)
    (h₄ : Q₄ * Q₄ = 0) :
    (Q₁ + Q₂ + Q₃ + Q₄) * (Q₁ + Q₂ + Q₃ + Q₄) =
      oddAnticomm Q₁ Q₂
      + oddAnticomm Q₁ Q₃
      + oddAnticomm Q₁ Q₄
      + oddAnticomm Q₂ Q₃
      + oddAnticomm Q₂ Q₄
      + oddAnticomm Q₃ Q₄ := by
  calc
    (Q₁ + Q₂ + Q₃ + Q₄) * (Q₁ + Q₂ + Q₃ + Q₄)
        =
      (Q₁ * Q₁ + Q₂ * Q₂ + Q₃ * Q₃ + Q₄ * Q₄)
      + (Q₁ * Q₂ + Q₂ * Q₁)
      + (Q₁ * Q₃ + Q₃ * Q₁)
      + (Q₁ * Q₄ + Q₄ * Q₁)
      + (Q₂ * Q₃ + Q₃ * Q₂)
      + (Q₂ * Q₄ + Q₄ * Q₂)
      + (Q₃ * Q₄ + Q₄ * Q₃) := by
          exact four_supercharge_square Q₁ Q₂ Q₃ Q₄
    _ =
      (0 + 0 + 0 + 0)
      + (Q₁ * Q₂ + Q₂ * Q₁)
      + (Q₁ * Q₃ + Q₃ * Q₁)
      + (Q₁ * Q₄ + Q₄ * Q₁)
      + (Q₂ * Q₃ + Q₃ * Q₂)
      + (Q₂ * Q₄ + Q₄ * Q₂)
      + (Q₃ * Q₄ + Q₄ * Q₃) := by
          rw [h₁, h₂, h₃, h₄]
    _ =
      oddAnticomm Q₁ Q₂
      + oddAnticomm Q₁ Q₃
      + oddAnticomm Q₁ Q₄
      + oddAnticomm Q₂ Q₃
      + oddAnticomm Q₂ Q₄
      + oddAnticomm Q₃ Q₄ := by
          simp [oddAnticomm, add_assoc, add_left_comm, add_comm]

/--
Finite `N=2` graded-SUSY closure:
for odd charges `Q₁,Q₂` with `Qᵢ²=0`, the extended square is exactly the
odd-odd anticommutator.
-/
@[rep_depth thermo]
theorem n2_supercharge_square_eq_oddAnticomm
    {A : Type*} [Ring A]
    {Q₁ Q₂ : A}
    (hQ₁ : Q₁ * Q₁ = 0)
    (hQ₂ : Q₂ * Q₂ = 0) :
    (Q₁ + Q₂) * (Q₁ + Q₂) = oddAnticomm Q₁ Q₂ := by
  simpa [oddAnticomm] using
    recursive_nilpotent_supercharge_square_eq_anticommutator (Q := Q₁) (R := Q₂) hQ₁ hQ₂

/--
Finite `N=2` closure with explicit even/central split in the odd-odd bracket:
if `{Q₁,Q₂} = H + Z`, then `(Q₁+Q₂)^2 = H + Z`.
-/
@[rep_depth thermo]
theorem n2_supercharge_square_eq_hamiltonian_plus_central
    {A : Type*} [Ring A]
    {Q₁ Q₂ H Z : A}
    (hQ₁ : Q₁ * Q₁ = 0)
    (hQ₂ : Q₂ * Q₂ = 0)
    (hsplit : oddAnticomm Q₁ Q₂ = H + Z) :
    (Q₁ + Q₂) * (Q₁ + Q₂) = H + Z := by
  calc
    (Q₁ + Q₂) * (Q₁ + Q₂) = oddAnticomm Q₁ Q₂ := by
      exact n2_supercharge_square_eq_oddAnticomm (Q₁ := Q₁) (Q₂ := Q₂) hQ₁ hQ₂
    _ = H + Z := hsplit

/--
Duality transport of odd-odd anticommutators across a ring equivalence.
-/
@[rep_depth thermo]
theorem duality_transport_oddAnticomm
    {A B : Type*} [Ring A] [Ring B]
    (Dual : A ≃+* B) (X Y : A) :
    Dual (oddAnticomm X Y) = oddAnticomm (Dual X) (Dual Y) := by
  simp [oddAnticomm, map_add, map_mul]

/--
Duality transport of finite `N=2` square closure:
if `(Q₁+Q₂)^2 = H + Z` in `A`, then the transported charges satisfy
the same closure in `B`.
-/
@[rep_depth thermo]
theorem duality_transport_n2_square_closure
    {A B : Type*} [Ring A] [Ring B]
    (Dual : A ≃+* B)
    {Q₁ Q₂ H Z : A}
    (hclosure : (Q₁ + Q₂) * (Q₁ + Q₂) = H + Z) :
    (Dual Q₁ + Dual Q₂) * (Dual Q₁ + Dual Q₂) = Dual H + Dual Z := by
  simpa [map_add, map_mul] using congrArg Dual hclosure

/--
Duality transport preserves centrality of the transported central term.
-/
@[rep_depth thermo]
theorem duality_transport_centrality
    {A B : Type*} [Ring A] [Ring B]
    (Dual : A ≃+* B)
    {Z : A}
    (hCentral : ∀ X : A, Z * X = X * Z) :
    ∀ Y : B, Dual Z * Y = Y * Dual Z := by
  intro Y
  rcases Dual.surjective Y with ⟨X, rfl⟩
  simpa [map_mul] using congrArg Dual (hCentral X)

/--
Dimension doubling identity for the finite Bott ladder:
`2^(n+1) = 2 * 2^n`.
-/
@[rep_depth thermo]
theorem two_pow_succ (n : ℕ) :
    2 ^ (n + 1) = 2 * 2 ^ n := by
  simpa [pow_succ, Nat.mul_comm] using (pow_succ 2 n).symm

/--
Two Bott steps: `2^(n+2) = 4 * 2^n`.
-/
@[rep_depth thermo]
theorem two_pow_add_two (n : ℕ) :
    2 ^ (n + 2) = 4 * 2 ^ n := by
  calc
    2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by simpa [Nat.add_assoc] using two_pow_succ (n + 1)
    _ = 2 * (2 * 2 ^ n) := by rw [two_pow_succ n]
    _ = 4 * 2 ^ n := by ring

/--
Factorwise odd-odd anticommutator on product rings.

This is the finite tensor surrogate:
`{(x₁,x₂),(y₁,y₂)} = ({x₁,y₁},{x₂,y₂})`.
-/
@[rep_depth thermo]
theorem oddAnticomm_prod_factorwise
    {A B : Type*} [Ring A] [Ring B]
    (x₁ y₁ : A) (x₂ y₂ : B) :
    oddAnticomm (A := A × B) (x₁, x₂) (y₁, y₂) =
      (oddAnticomm (A := A) x₁ y₁, oddAnticomm (A := B) x₂ y₂) := by
  simp [oddAnticomm, Prod.snd_mul, Prod.fst_mul, Prod.snd_add, Prod.fst_add]

/--
Finite Bott/tensor step for `N=2` closure:
if closure holds in `A` and in `B`, it holds in `A × B`.
-/
@[rep_depth thermo]
theorem supergradedClosureAt_prod
    {A B : Type*} [Ring A] [Ring B]
    {QA QAsharp : A} {QB QBsharp : B}
    (hA : SupergradedClosureAt (R := A) QA QAsharp)
    (hB : SupergradedClosureAt (R := B) QB QBsharp) :
    SupergradedClosureAt (R := A × B) (QA, QB) (QAsharp, QBsharp) := by