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
  rcases hA with ⟨hA1, hA2, hA3, hA4⟩
  rcases hB with ⟨hB1, hB2, hB3, hB4⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext <;> simp [SupergradedClosureAt, hA1, hA2, hA3, hA4, hB1, hB2, hB3, hB4]

/--
Central-charge transport under finite tensor/product step:
if each side has an odd-odd split `{Q,Q♯}=H+Z`, the product side has
componentwise split.
-/
@[rep_depth thermo]
theorem n2_hamiltonian_central_split_prod
    {A B : Type*} [Ring A] [Ring B]
    {QA QAsharp HA ZA : A}
    {QB QBsharp HB ZB : B}
    (hA : oddAnticomm (A := A) QA QAsharp = HA + ZA)
    (hB : oddAnticomm (A := B) QB QBsharp = HB + ZB) :
    oddAnticomm (A := A × B) (QA, QB) (QAsharp, QBsharp) =
      (HA, HB) + (ZA, ZB) := by
  ext
  · simpa [oddAnticomm] using hA
  · simpa [oddAnticomm] using hB

/--
Indexed formal inductive chain (`A₀ → A₁ → A₂ → …`) via bonding maps.
-/
@[rep_depth thermo]
structure IndexedInductiveChain where
  Stage : ℕ → Type*
  step : ∀ n, Stage n → Stage (n + 1)

namespace IndexedInductiveChain

variable (C : IndexedInductiveChain)

/--
Iterated embedding from stage `0` to stage `n`.
-/
@[rep_depth thermo]
def iterEmbed : ∀ n, C.Stage 0 → C.Stage n
  | 0, x => x
  | n + 1, x => C.step n (iterEmbed n x)

/--
Stepwise preservation of a symmetry-adapted local invariant.
-/
@[rep_depth thermo]
def Preserves (Inv : ∀ n, C.Stage n → Prop) : Prop :=
  ∀ n x, Inv n x → Inv (n + 1) (C.step n x)

/--
If an invariant is true at stage `0` and preserved by each bonding map,
it is true along the full finite inductive chain.
-/
@[rep_depth thermo]
theorem invariant_along_chain
    (Inv : ∀ n, C.Stage n → Prop)
    (hPres : C.Preserves Inv)
    {x0 : C.Stage 0}
    (h0 : Inv 0 x0) :
    ∀ n, Inv n (C.iterEmbed n x0) := by
  intro n
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      exact hPres n (C.iterEmbed n x0) ih

/--
Two invariants preserved stepwise are preserved jointly along the chain.
-/
@[rep_depth thermo]
theorem invariant_pair_along_chain
    (Inv₁ Inv₂ : ∀ n, C.Stage n → Prop)
    (hPres₁ : C.Preserves Inv₁)
    (hPres₂ : C.Preserves Inv₂)
    {x0 : C.Stage 0}
    (h0₁ : Inv₁ 0 x0)
    (h0₂ : Inv₂ 0 x0) :
    ∀ n, Inv₁ n (C.iterEmbed n x0) ∧ Inv₂ n (C.iterEmbed n x0) := by
  intro n
  constructor
  · exact C.invariant_along_chain Inv₁ hPres₁ h0₁ n
  · exact C.invariant_along_chain Inv₂ hPres₂ h0₂ n

end IndexedInductiveChain

/-- Invariant packet at one finite stage of an inductive operator chain. -/
structure SupergradedInvariantAt (A : Type*) [Ring A] where
  is_odd : A → Prop
  is_even : A → Prop
  is_central : A → Prop
  odd_nilpotency : ∀ x, is_odd x → x * x = 0
  odd_odd_closure : ∀ x y, is_odd x → is_odd y → is_even (x * y + y * x)
  central_lane : ∀ c x, is_central c → c * x = x * c
  projector_identity : ∃ P, is_even P ∧ P * P = P

/--
Bonding intertwiner between two stages; transports the grading/central lanes.
-/
structure BondingIntertwiner
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedInvariantAt A) (invB : SupergradedInvariantAt B) where
  map : A →+* B
  preserves_odd : ∀ x, invA.is_odd x → invB.is_odd (map x)
  preserves_even : ∀ x, invA.is_even x → invB.is_even (map x)
  preserves_central : ∀ c, invA.is_central c → invB.is_central (map c)

/--
Core transport lemma: odd nilpotency is stable under a valid bonding intertwiner.
-/
@[rep_depth thermo]
theorem invariant_transport_stable
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedInvariantAt A)
    (invB : SupergradedInvariantAt B)
    (f : BondingIntertwiner invA invB)
    (x : A) (hx : invA.is_odd x) :
    (f.map x) * (f.map x) = 0 := by
  have h_odd_map : invB.is_odd (f.map x) := f.preserves_odd x hx
  exact invB.odd_nilpotency (f.map x) h_odd_map

/--
Transport of odd-odd closure through a bonding intertwiner.
-/
@[rep_depth thermo]
theorem oddOdd_closure_transport
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedInvariantAt A)
    (invB : SupergradedInvariantAt B)
    (f : BondingIntertwiner invA invB)
    (x y : A) (hx : invA.is_odd x) (hy : invA.is_odd y) :
    invB.is_even ((f.map x) * (f.map y) + (f.map y) * (f.map x)) := by
  have hx' : invB.is_odd (f.map x) := f.preserves_odd x hx
  have hy' : invB.is_odd (f.map y) := f.preserves_odd y hy
  simpa [map_add, map_mul] using invB.odd_odd_closure (f.map x) (f.map y) hx' hy'

/--
Transport of central-lane commutation through a bonding intertwiner.
-/
@[rep_depth thermo]
theorem central_lane_transport
    {A B : Type*} [Ring A] [Ring B]
    (invA : SupergradedInvariantAt A)
    (invB : SupergradedInvariantAt B)
    (f : BondingIntertwiner invA invB)
    (c x : A) (hc : invA.is_central c) :
    (f.map c) * (f.map x) = (f.map x) * (f.map c) := by
  have hc' : invB.is_central (f.map c) := f.preserves_central c hc
  exact invB.central_lane (f.map c) (f.map x) hc'

/--
Finite chain packet: each stage has an invariant packet and each edge is a
bonding intertwiner.
-/
structure FiniteInvariantChain where
  Stage : ℕ → Type*
  stageRing : ∀ n, Ring (Stage n)
  Invariant : ∀ n, SupergradedInvariantAt (Stage n)
  Bonding :
    ∀ n,
      @BondingIntertwiner
        (Stage n) (Stage (n + 1))
        (stageRing n) (stageRing (n + 1))
        (Invariant n) (Invariant (n + 1))

attribute [instance] FiniteInvariantChain.stageRing

namespace FiniteInvariantChain

variable (C : FiniteInvariantChain)

/-- Iterated embedding map from stage `0` into stage `n`. -/
def iterMap : ∀ n, C.Stage 0 → C.Stage n
  | 0, x => x
  | n + 1, x => (C.Bonding n).map (iterMap n x)

/-- Stagewise odd invariance along the inductive chain. -/
@[rep_depth thermo]
theorem odd_preserved_along_chain
    {x0 : C.Stage 0}
    (hx0 : (C.Invariant 0).is_odd x0) :
    ∀ n, (C.Invariant n).is_odd (C.iterMap n x0) := by
  intro n
  induction n with
  | zero =>
      simpa using hx0
  | succ n ih =>
      exact (C.Bonding n).preserves_odd _ ih

/-- Stagewise odd nilpotency along the inductive chain. -/
@[rep_depth thermo]
theorem odd_nilpotent_along_chain
    {x0 : C.Stage 0}
    (hx0 : (C.Invariant 0).is_odd x0) :
    ∀ n, (C.iterMap n x0) * (C.iterMap n x0) = 0 := by
  intro n
  have hodd : (C.Invariant n).is_odd (C.iterMap n x0) := C.odd_preserved_along_chain hx0 n
  exact (C.Invariant n).odd_nilpotency (C.iterMap n x0) hodd

/-- Stagewise even-lane preservation along the inductive chain. -/
@[rep_depth thermo]
theorem even_preserved_along_chain
    {x0 : C.Stage 0}
    (hx0 : (C.Invariant 0).is_even x0) :
    ∀ n, (C.Invariant n).is_even (C.iterMap n x0) := by
  intro n
  induction n with
  | zero =>
      simpa using hx0
  | succ n ih =>
      exact (C.Bonding n).preserves_even _ ih

/-- Stagewise central-lane preservation along the inductive chain. -/
@[rep_depth thermo]
theorem central_preserved_along_chain
    {c0 : C.Stage 0}
    (hc0 : (C.Invariant 0).is_central c0) :
    ∀ n, (C.Invariant n).is_central (C.iterMap n c0) := by
  intro n
  induction n with
  | zero =>
      simpa using hc0
  | succ n ih =>
      exact (C.Bonding n).preserves_central _ ih

/--
An idempotent even witness at stage `0` transports to an idempotent even
witness at every stage.
-/
@[rep_depth thermo]
theorem transported_projector_witness
    {P0 : C.Stage 0}
    (hP0_even : (C.Invariant 0).is_even P0)
    (hP0_idem : P0 * P0 = P0) :
    ∀ n, (C.Invariant n).is_even (C.iterMap n P0) ∧
      (C.iterMap n P0) * (C.iterMap n P0) = C.iterMap n P0 := by
  intro n
  constructor
  · exact C.even_preserved_along_chain hP0_even n
  · induction n with
    | zero =>
        simpa using hP0_idem
    | succ n ih =>
        simpa [iterMap, map_mul] using congrArg (C.Bonding n).map ih

/--
Each stage has a concrete projector witness induced from the stage-`0`
projector via the bonding chain.
-/
@[rep_depth thermo]
theorem projector_exists_along_chain_from_zero :
    ∃ P0, (C.Invariant 0).is_even P0 ∧ P0 * P0 = P0 ∧
      ∀ n, (C.Invariant n).is_even (C.iterMap n P0) ∧
        (C.iterMap n P0) * (C.iterMap n P0) = C.iterMap n P0 := by
  rcases (C.Invariant 0).projector_identity with ⟨P0, hEven0, hIdem0⟩
  exact ⟨P0, hEven0, hIdem0, C.transported_projector_witness hEven0 hIdem0⟩

/--
Two-step functorial law for odd-odd anticommutator transport:
transporting from stage `n` to `n+2` equals transporting to `n+1` then to `n+2`.
-/
@[rep_depth thermo]
theorem oddAnticomm_transport_two_steps
    {n : ℕ}
    (x y : C.Stage n) :
    (C.Bonding (n + 1)).map
      (oddAnticomm ((C.Bonding n).map x) ((C.Bonding n).map y))
      =
    oddAnticomm
      ((C.Bonding (n + 1)).map ((C.Bonding n).map x))
      ((C.Bonding (n + 1)).map ((C.Bonding n).map y)) := by
  simp [oddAnticomm, map_add, map_mul]

/--
Functorial odd-odd transport along the iterated embedding map from stage `0`.
-/
@[rep_depth thermo]
theorem oddAnticomm_iterMap_transport
    {x0 y0 : C.Stage 0} :
    ∀ n,
      C.iterMap n (oddAnticomm x0 y0) =
        oddAnticomm (C.iterMap n x0) (C.iterMap n y0) := by
  intro n
  induction n with
  | zero =>
      simp [iterMap]
  | succ n ih =>
      simpa [iterMap, oddAnticomm, map_add, map_mul] using congrArg (C.Bonding n).map ih

/--
If two stage-`0` elements are odd, their transported odd-odd anticommutator
lies in the even lane at every stage.
-/
@[rep_depth thermo]
theorem oddOdd_even_along_chain
    {x0 y0 : C.Stage 0}
    (hx0 : (C.Invariant 0).is_odd x0)
    (hy0 : (C.Invariant 0).is_odd y0) :
    ∀ n, (C.Invariant n).is_even (oddAnticomm (C.iterMap n x0) (C.iterMap n y0)) := by
  intro n
  have hx : (C.Invariant n).is_odd (C.iterMap n x0) := C.odd_preserved_along_chain hx0 n
  have hy : (C.Invariant n).is_odd (C.iterMap n y0) := C.odd_preserved_along_chain hy0 n
  exact (C.Invariant n).odd_odd_closure _ _ hx hy

/--
If `c0` is central at stage `0`, it commutes at each stage with any transported
element from stage `0`.
-/
@[rep_depth thermo]
theorem central_commutes_with_iterMap
    {c0 x0 : C.Stage 0}
    (hc0 : (C.Invariant 0).is_central c0) :
    ∀ n, (C.iterMap n c0) * (C.iterMap n x0) = (C.iterMap n x0) * (C.iterMap n c0) := by
  intro n
  have hc : (C.Invariant n).is_central (C.iterMap n c0) := C.central_preserved_along_chain hc0 n
  exact (C.Invariant n).central_lane _ _ hc

/--
Stagewise even closure can be read as transport of the stage-`0`
odd-odd anticommutator through `iterMap`.
-/
@[rep_depth thermo]
theorem oddOdd_even_along_chain_via_transport
    {x0 y0 : C.Stage 0}
    (hx0 : (C.Invariant 0).is_odd x0)
    (hy0 : (C.Invariant 0).is_odd y0) :
    ∀ n, (C.Invariant n).is_even (C.iterMap n (oddAnticomm x0 y0)) := by
  intro n
  have hEven : (C.Invariant n).is_even (oddAnticomm (C.iterMap n x0) (C.iterMap n y0)) :=
    C.oddOdd_even_along_chain hx0 hy0 n
  simpa [C.oddAnticomm_iterMap_transport (x0 := x0) (y0 := y0) n] using hEven

/--
If `c0` is central at stage `0`, then at every stage it commutes with the
transported odd-odd anticommutator of two transported stage-`0` odd elements.
-/
@[rep_depth thermo]
theorem central_commutes_with_oddAnticomm_iterMap
    {c0 x0 y0 : C.Stage 0}
    (hc0 : (C.Invariant 0).is_central c0) :
    ∀ n,
      (C.iterMap n c0) * oddAnticomm (C.iterMap n x0) (C.iterMap n y0)
        =
      oddAnticomm (C.iterMap n x0) (C.iterMap n y0) * (C.iterMap n c0) := by
  intro n
  rw [← C.oddAnticomm_iterMap_transport (x0 := x0) (y0 := y0) n]
  exact C.central_commutes_with_iterMap (c0 := c0) (x0 := oddAnticomm x0 y0) hc0 n

end FiniteInvariantChain

/-- Local number operator `N = ε*ι`. -/
@[rep_depth thermo]
def localNumber {R : Type*} [Ring R] (ε ι : R) : R := ε * ι

/-- Local parity/tilt operator `Π = (ε+ι)(ε-ι)`. -/
@[rep_depth thermo]
def localParity {R : Type*} [Ring R] (ε ι : R) : R := (ε + ι) * (ε - ι)

/-- `N^2 = N` for `N = ε*ι` under local CAR/Witt laws. -/
@[rep_depth thermo]
theorem localNumber_idempotent
    {R : Type*} [Ring R]
    {ε ι : R}
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : ε * ι + ι * ε = 1) :
    let N := localNumber ε ι
    N * N = N := by
  dsimp [localNumber]
  exact (car_witt_projector_grading_packet (ε := ε) (ι := ι) hε hι hcar).1

/-- `Π = 1 - 2N` with `Π = (ε+ι)(ε-ι)` and `N = ε*ι`. -/
@[rep_depth thermo]
theorem localParity_eq_one_sub_two_number
    {R : Type*} [Ring R]
    {ε ι : R}
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : ε * ι + ι * ε = 1) :
    localParity ε ι = 1 - (2 : R) * localNumber ε ι := by
  dsimp [localParity, localNumber]
  exact (car_witt_projector_grading_packet (ε := ε) (ι := ι) hε hι hcar).2.2.2.2

/-- Vacuum projector `(1-N)` is idempotent. -/
@[rep_depth thermo]
theorem localVacuumProjector_idempotent
    {R : Type*} [Ring R]
    {ε ι : R}
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : ε * ι + ι * ε = 1) :
    let N := localNumber ε ι
    (1 - N) * (1 - N) = 1 - N := by
  dsimp [localNumber]
  exact (car_witt_projector_grading_packet (ε := ε) (ι := ι) hε hι hcar).2.1

/-- Vacuum and occupied projectors are orthogonal: `(1-N)*N = 0`. -/
@[rep_depth thermo]
theorem localVacuum_mul_number_eq_zero
    {R : Type*} [Ring R]
    {ε ι : R}
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : ε * ι + ι * ε = 1) :
    let N := localNumber ε ι
    (1 - N) * N = 0 := by
  dsimp [localNumber]
  exact (car_witt_projector_grading_packet (ε := ε) (ι := ι) hε hι hcar).2.2.2.1

/-- Nambu doubled odd operator `E = (ε, ι)`. -/
@[rep_depth thermo]
def nambuOddE {R : Type*} [Ring R] (ε ι : R) : R × R := (ε, ι)

/-- Nambu doubled odd operator `I = (ι, ε)`. -/
@[rep_depth thermo]
def nambuOddI {R : Type*} [Ring R] (ε ι : R) : R × R := (ι, ε)

/--
Nambu doubled nilpotency:
if `ε²=0` and `ι²=0`, then both doubled odd lanes square to zero.
-/
@[rep_depth thermo]
theorem nambuOdd_sq_zero
    {R : Type*} [Ring R]
    {ε ι : R}
    (hε : ε * ε = 0)
    (hι : ι * ι = 0) :
    nambuOddE ε ι * nambuOddE ε ι = (0, 0) ∧
    nambuOddI ε ι * nambuOddI ε ι = (0, 0) := by
  constructor <;> ext <;> simp [nambuOddE, nambuOddI, hε, hι]

/--
Nambu doubled CAR closure:
if `ει + ιε = 1`, then `{E,I} = (1,1)`.
-/
@[rep_depth thermo]
theorem nambuOdd_anticomm_one
    {R : Type*} [Ring R]
    {ε ι : R}
    (hcar : ε * ι + ι * ε = 1) :
    oddAnticomm (nambuOddE ε ι) (nambuOddI ε ι) = (1, 1) := by
  ext
  · simp [oddAnticomm, nambuOddE, nambuOddI, hcar]
  · simpa [oddAnticomm, nambuOddE, nambuOddI, add_comm] using hcar

/-- Nambu doubled Majorana `C = E + I = (ε+ι, ε+ι)`. -/
@[rep_depth thermo]
def nambuMajoranaC {R : Type*} [Ring R] (ε ι : R) : R × R :=
  nambuOddE ε ι + nambuOddI ε ι

/-- Nambu doubled Krein partner `D = E - I = (ε-ι, ι-ε)`. -/
@[rep_depth thermo]
def nambuMajoranaD {R : Type*} [Ring R] (ε ι : R) : R × R :=
  nambuOddE ε ι - nambuOddI ε ι

/--
Nambu doubled square laws:
from local CAR/Witt laws, `C² = (1,1)` and `D² = (-1,-1)`.
-/
@[rep_depth thermo]
theorem nambuMajorana_square_laws
    {R : Type*} [Ring R]
    {ε ι : R}
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : ε * ι + ι * ε = 1) :
    nambuMajoranaC ε ι * nambuMajoranaC ε ι = (1, 1) ∧
    nambuMajoranaD ε ι * nambuMajoranaD ε ι = (-1, -1) := by
  constructor
  · ext
    · simpa [nambuMajoranaC, nambuOddE, nambuOddI] using
        (squareZero_pair_gives_clifford_axes (u := ε) (v := ι) hε hι hcar).1
    · simpa [nambuMajoranaC, nambuOddE, nambuOddI, add_comm] using
        (squareZero_pair_gives_clifford_axes (u := ε) (v := ι) hε hι hcar).1
  · ext
    · simpa [nambuMajoranaD, nambuOddE, nambuOddI] using
        (squareZero_pair_gives_clifford_axes (u := ε) (v := ι) hε hι hcar).2
    ·
      have hcar' : ι * ε + ε * ι = 1 := by simpa [add_comm] using hcar
      simpa [nambuMajoranaD, nambuOddE, nambuOddI, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using (squareZero_pair_gives_clifford_axes (u := ι) (v := ε) hι hε hcar').2

/-- Finite doubled carrier for BdG/Nambu block dynamics. -/
@[rep_depth thermo]
abbrev Nambu2 (R : Type*) := R × R

/-- Diagonal BdG block action on the doubled carrier. -/
@[rep_depth thermo]
def bdgDiag {R : Type*} [Ring R] (a d : R) : Nambu2 R → Nambu2 R
  | (x, y) => (a * x, d * y)

/-- Off-diagonal BdG block action on the doubled carrier. -/
@[rep_depth thermo]
def bdgOff {R : Type*} [Ring R] (b c : R) : Nambu2 R → Nambu2 R
  | (x, y) => (b * y, c * x)

/-- Full finite BdG operator: diagonal plus off-diagonal blocks. -/
@[rep_depth thermo]
def bdgOp {R : Type*} [Ring R] (a b c d : R) : Nambu2 R → Nambu2 R :=
  fun v => ((bdgDiag a d v).1 + (bdgOff b c v).1, (bdgDiag a d v).2 + (bdgOff b c v).2)

/-- Explicit BdG action formula. -/
@[rep_depth thermo]
theorem bdgOp_apply
    {R : Type*} [Ring R] (a b c d : R) (x y : R) :
    bdgOp a b c d (x, y) = (a * x + b * y, c * x + d * y) := by
  simp [bdgOp, bdgDiag, bdgOff, add_comm]

/-- Diagonal block preserves each lane (no mixing). -/
@[rep_depth thermo]
theorem bdgDiag_preserves_lanes
    {R : Type*} [Ring R] (a d : R) (x y : R) :
    bdgDiag a d (x, y) = (a * x, d * y) := by
  simp [bdgDiag]

/-- Off-diagonal block is pure lane-mixing (particle-hole coupling). -/
@[rep_depth thermo]
theorem bdgOff_is_lane_mixing
    {R : Type*} [Ring R] (b c : R) (x y : R) :
    bdgOff b c (x, y) = (b * y, c * x) := by
  simp [bdgOff]

/-- The full BdG block decomposes exactly as diagonal plus off-diagonal actions. -/
@[rep_depth thermo]
theorem bdgOp_decompose
    {R : Type*} [Ring R] (a b c d : R) (v : Nambu2 R) :
    bdgOp a b c d v =
      ((bdgDiag a d v).1 + (bdgOff b c v).1, (bdgDiag a d v).2 + (bdgOff b c v).2) := by
  rfl

/--
Two-step off-diagonal composition is diagonal:
`Off(b,c) ∘ Off(b',c') = Diag(b*c', c*b')`.
-/
@[rep_depth thermo]
theorem bdgOff_comp_bdgOff_eq_diag
    {R : Type*} [Ring R]
    (b c b' c' : R) (x y : R) :
    bdgOff b c (bdgOff b' c' (x, y)) = bdgDiag (b * c') (c * b') (x, y) := by
  simp [bdgOff, bdgDiag, mul_assoc]

/--
Two-step finite BdG dynamics in explicit coordinate form.
-/
@[rep_depth thermo]
theorem bdgOp_comp_apply
    {R : Type*} [Ring R]
    (a b c d a' b' c' d' : R) (x y : R) :
    bdgOp a b c d (bdgOp a' b' c' d' (x, y))
      =
    (a * (a' * x + b' * y) + b * (c' * x + d' * y),
     c * (a' * x + b' * y) + d * (c' * x + d' * y)) := by
  simp [bdgOp_apply]

/--
Off-diagonal block nilpotency criterion on the doubled carrier:
if `b*c = 0` and `c*b = 0`, then `Off(b,c)^2 = 0`.
-/
@[rep_depth thermo]
theorem bdgOff_sq_zero_of_mul_zero
    {R : Type*} [Ring R]
    {b c : R}
    (hbc : b * c = 0)
    (hcb : c * b = 0) :
    ∀ v : Nambu2 R, bdgOff b c (bdgOff b c v) = (0, 0) := by
  intro v
  rcases v with ⟨x, y⟩
  ext
  · calc
      b * (c * x) = (b * c) * x := by rw [mul_assoc]
      _ = 0 * x := by rw [hbc]
      _ = 0 := by simp
  · calc
      c * (b * y) = (c * b) * y := by rw [mul_assoc]
      _ = 0 * y := by rw [hcb]
      _ = 0 := by simp

/--
Exact square law for the off-diagonal BdG block:
`Off(b,c)^2 = Diag(b*c, c*b)`.
-/
@[rep_depth thermo]
theorem bdgOff_sq_eq_diag
    {R : Type*} [Ring R]
    (b c : R) :
    ∀ v : Nambu2 R, bdgOff b c (bdgOff b c v) = bdgDiag (b * c) (c * b) v := by
  intro v
  rcases v with ⟨x, y⟩
  ext
  · calc
      b * (c * x) = (b * c) * x := by rw [mul_assoc]
      _ = (bdgDiag (b * c) (c * b) (x, y)).1 := by rfl
  · calc
      c * (b * y) = (c * b) * y := by rw [mul_assoc]
      _ = (bdgDiag (b * c) (c * b) (x, y)).2 := by rfl

/--
Composition law for two finite BdG blocks.
If `M = [[a,b],[c,d]]` and `M' = [[a',b'],[c',d']]`, then
`bdgOp M ∘ bdgOp M' = bdgOp (M*M')` with explicit coefficients.
-/
@[rep_depth thermo]
theorem bdgOp_comp_eq_bdgOp_mulCoeffs
    {R : Type*} [Ring R]
    (a b c d a' b' c' d' : R) :
    ∀ v : Nambu2 R,
      bdgOp a b c d (bdgOp a' b' c' d' v)
        =
      bdgOp
        (a * a' + b * c')
        (a * b' + b * d')
        (c * a' + d * c')
        (c * b' + d * d')
        v := by
  intro v
  rcases v with ⟨x, y⟩
  ext
  · calc
      (bdgOp a b c d (bdgOp a' b' c' d' (x, y))).1
          = a * (a' * x + b' * y) + b * (c' * x + d' * y) := by
              simpa [bdgOp_comp_apply]
      _ = (a * a' + b * c') * x + (a * b' + b * d') * y := by
              noncomm_ring
      _ = (bdgOp
            (a * a' + b * c')
            (a * b' + b * d')
            (c * a' + d * c')
            (c * b' + d * d')
            (x, y)).1 := by
              simp [bdgOp_apply]
  · calc
      (bdgOp a b c d (bdgOp a' b' c' d' (x, y))).2
          = c * (a' * x + b' * y) + d * (c' * x + d' * y) := by
              simpa [bdgOp_comp_apply]
      _ = (c * a' + d * c') * x + (c * b' + d * d') * y := by
              noncomm_ring
      _ = (bdgOp
            (a * a' + b * c')
            (a * b' + b * d')
            (c * a' + d * c')
            (c * b' + d * d')
            (x, y)).2 := by
              simp [bdgOp_apply]

/--
Diagonal BdG blocks compose by coefficient multiplication.
-/
@[rep_depth thermo]
theorem bdgDiag_comp_eq_diag_mul
    {R : Type*} [Ring R]
    (a d a' d' : R) :
    ∀ v : Nambu2 R,
      bdgDiag a d (bdgDiag a' d' v) = bdgDiag (a * a') (d * d') v := by
  intro v
  rcases v with ⟨x, y⟩
  ext <;> simp [bdgDiag, mul_assoc]

/--
Left diagonal / right off-diagonal composition formula.
-/
@[rep_depth thermo]
theorem bdgDiag_comp_bdgOff
    {R : Type*} [Ring R]
    (a d b c : R) :
    ∀ v : Nambu2 R,
      bdgDiag a d (bdgOff b c v) = bdgOff (a * b) (d * c) v := by
  intro v
  rcases v with ⟨x, y⟩
  ext <;> simp [bdgDiag, bdgOff, mul_assoc]

/--
Left off-diagonal / right diagonal composition formula.
-/
@[rep_depth thermo]
theorem bdgOff_comp_bdgDiag
    {R : Type*} [Ring R]
    (b c a d : R) :
    ∀ v : Nambu2 R,
      bdgOff b c (bdgDiag a d v) = bdgOff (b * d) (c * a) v := by
  intro v
  rcases v with ⟨x, y⟩
  ext <;> simp [bdgDiag, bdgOff, mul_assoc]

/--
Diagonal and off-diagonal blocks commute under coefficient constraints
`a*b=b*d` and `d*c=c*a`.
-/
@[rep_depth thermo]
theorem bdgDiag_bdgOff_commute_of_coeff_constraints
    {R : Type*} [Ring R]
    {a d b c : R}
    (habd : a * b = b * d)
    (hdca : d * c = c * a) :
    ∀ v : Nambu2 R, bdgDiag a d (bdgOff b c v) = bdgOff b c (bdgDiag a d v) := by
  intro v
  calc
    bdgDiag a d (bdgOff b c v) = bdgOff (a * b) (d * c) v := by
      simpa using bdgDiag_comp_bdgOff (a := a) (d := d) (b := b) (c := c) v
    _ = bdgOff (b * d) (c * a) v := by
      simp [habd, hdca]
    _ = bdgOff b c (bdgDiag a d v) := by
      symm
      simpa using bdgOff_comp_bdgDiag (b := b) (c := c) (a := a) (d := d) v

/--
Exact square coefficient law for a finite BdG block.
-/
@[rep_depth thermo]
theorem bdgOp_sq_eq_bdgOp_coeffs
    {R : Type*} [Ring R]
    (a b c d : R) :
    ∀ v : Nambu2 R,
      bdgOp a b c d (bdgOp a b c d v)
        =
      bdgOp
        (a * a + b * c)
        (a * b + b * d)
        (c * a + d * c)
        (c * b + d * d)
        v := by
  intro v
  simpa using
    bdgOp_comp_eq_bdgOp_mulCoeffs
      (a := a) (b := b) (c := c) (d := d)
      (a' := a) (b' := b) (c' := c) (d' := d) v

/--
Diagonal/off-diagonal BdG commutator in explicit coefficient form.
-/
@[rep_depth thermo]
theorem bdgDiag_bdgOff_commutator
    {R : Type*} [Ring R]
    (a d b c : R) :
    ∀ v : Nambu2 R,
      bdgDiag a d (bdgOff b c v) = bdgOff b c (bdgDiag a d v) ↔
      bdgOff (a * b) (d * c) v = bdgOff (b * d) (c * a) v := by
  intro v
  constructor
  · intro h
    calc
      bdgOff (a * b) (d * c) v = bdgDiag a d (bdgOff b c v) := by
        symm
        simpa using bdgDiag_comp_bdgOff (a := a) (d := d) (b := b) (c := c) v
      _ = bdgOff b c (bdgDiag a d v) := h
      _ = bdgOff (b * d) (c * a) v := by
        simpa using bdgOff_comp_bdgDiag (b := b) (c := c) (a := a) (d := d) v
  · intro h
    calc
      bdgDiag a d (bdgOff b c v) = bdgOff (a * b) (d * c) v := by
        simpa using bdgDiag_comp_bdgOff (a := a) (d := d) (b := b) (c := c) v
      _ = bdgOff (b * d) (c * a) v := h
      _ = bdgOff b c (bdgDiag a d v) := by
        simpa using (bdgOff_comp_bdgDiag (b := b) (c := c) (a := a) (d := d) v).symm

/--
Function-level commutation of diagonal/off-diagonal BdG blocks under
coefficient constraints.
-/
@[rep_depth thermo]
theorem bdgDiag_bdgOff_commute_funext_of_coeff_constraints
    {R : Type*} [Ring R]
    {a d b c : R}
    (habd : a * b = b * d)
    (hdca : d * c = c * a) :
    (fun v => bdgDiag a d (bdgOff b c v)) = (fun v => bdgOff b c (bdgDiag a d v)) := by
  funext v
  exact bdgDiag_bdgOff_commute_of_coeff_constraints (a := a) (d := d) (b := b) (c := c) habd hdca v

/--
Pure off-diagonal BdG block (`a=d=0`) squares to a diagonal block.
-/
@[rep_depth thermo]
theorem bdgOp_pureOff_sq_eq_diag
    {R : Type*} [Ring R]
    (b c : R) :
    ∀ v : Nambu2 R,
      bdgOp (0 : R) b c (0 : R) (bdgOp (0 : R) b c (0 : R) v)
        =
      bdgDiag (b * c) (c * b) v := by
  intro v
  calc
    bdgOp (0 : R) b c (0 : R) (bdgOp (0 : R) b c (0 : R) v)
        =
      bdgOp
        ((0 : R) * (0 : R) + b * c)
        ((0 : R) * b + b * (0 : R))
        (c * (0 : R) + (0 : R) * c)
        (c * b + (0 : R) * (0 : R))
        v := by
          simpa using bdgOp_sq_eq_bdgOp_coeffs (a := (0 : R)) (b := b) (c := c) (d := (0 : R)) v
    _ = bdgOp (b * c) (0 : R) (0 : R) (c * b) v := by
          simp
    _ = bdgDiag (b * c) (c * b) v := by
          rcases v with ⟨x, y⟩
          simp [bdgOp_apply, bdgDiag]

/--
Pure diagonal BdG block square law.
-/
@[rep_depth thermo]
theorem bdgOp_pureDiag_sq_eq_diag
    {R : Type*} [Ring R]
    (a d : R) :
    ∀ v : Nambu2 R,
      bdgOp a (0 : R) (0 : R) d (bdgOp a (0 : R) (0 : R) d v)
        =
      bdgDiag (a * a) (d * d) v := by
  intro v
  calc
    bdgOp a (0 : R) (0 : R) d (bdgOp a (0 : R) (0 : R) d v)
        =
      bdgOp
        (a * a + (0 : R) * (0 : R))
        (a * (0 : R) + (0 : R) * d)
        ((0 : R) * a + d * (0 : R))
        ((0 : R) * (0 : R) + d * d)
        v := by
          simpa using bdgOp_sq_eq_bdgOp_coeffs (a := a) (b := (0 : R)) (c := (0 : R)) (d := d) v
    _ = bdgOp (a * a) (0 : R) (0 : R) (d * d) v := by
          simp
    _ = bdgDiag (a * a) (d * d) v := by
          rcases v with ⟨x, y⟩
          simp [bdgOp_apply, bdgDiag]

/--
Square decomposition of a BdG block into explicit diagonal/off-diagonal
coefficient blocks.
-/
@[rep_depth thermo]
theorem bdgOp_sq_decompose_diag_off
    {R : Type*} [Ring R]
    (a b c d : R) :
    ∀ v : Nambu2 R,
      bdgOp a b c d (bdgOp a b c d v)
        = (
      (bdgDiag (a * a + b * c) (c * b + d * d) v).1
        + (bdgOff (a * b + b * d) (c * a + d * c) v).1,
      (bdgDiag (a * a + b * c) (c * b + d * d) v).2
        + (bdgOff (a * b + b * d) (c * a + d * c) v).2) := by
  intro v
  change
    bdgOp a b c d (bdgOp a b c d v)
      =
    bdgOp
      (a * a + b * c)
      (a * b + b * d)
      (c * a + d * c)
      (c * b + d * d)
      v
  simpa using bdgOp_sq_eq_bdgOp_coeffs (a := a) (b := b) (c := c) (d := d) v

/--
Index-1 Drazin-style algebra packet:
if `D` satisfies reflexive inverse identities for `A` and commutes with `A`,
then `P = A*D` is an idempotent projector.
-/
@[rep_depth thermo]
theorem drazin_indexOne_projector_idempotent
    {R : Type*} [Ring R]
    {A D : R}
    (hDAD : D * A * D = D)
    :
    (A * D) * (A * D) = A * D := by
  calc
    (A * D) * (A * D) = A * (D * A * D) := by noncomm_ring
    _ = A * D := by rw [hDAD]

/--
For the same index-1 Drazin-style packet, `A` annihilates the defect lane
`1 - A*D` on the right.
-/
@[rep_depth thermo]
theorem drazin_indexOne_annihilates_right_defect
    {R : Type*} [Ring R]
    {A D : R}
    (hADA : A * D * A = A)
    (hcomm : A * D = D * A) :
    A * (1 - A * D) = 0 := by
  have hAeq : A = A * (A * D) := by
    calc
      A = A * D * A := by symm; exact hADA
      _ = A * (D * A) := by rw [mul_assoc]
      _ = A * (A * D) := by rw [hcomm]
  have hAeq' : A * (A * D) = A := hAeq.symm
  calc
    A * (1 - A * D) = A * 1 - A * (A * D) := by rw [mul_sub]
    _ = A - A * (A * D) := by rw [mul_one]
    _ = A - A := by rw [hAeq']
    _ = 0 := by simp

/--
For the same index-1 Drazin-style packet, `A` annihilates the defect lane
`1 - A*D` on the left.
-/
@[rep_depth thermo]
theorem drazin_indexOne_annihilates_left_defect
    {R : Type*} [Ring R]
    {A D : R}
    (hADA : A * D * A = A) :
    (1 - A * D) * A = 0 := by
  have hAeq : A = (A * D) * A := by
    simpa [mul_assoc] using hADA.symm
  have hAeq' : (A * D) * A = A := hAeq.symm
  calc
    (1 - A * D) * A = 1 * A - (A * D) * A := by rw [sub_mul]
    _ = A - (A * D) * A := by rw [one_mul]
    _ = A - A := by rw [hAeq']
    _ = 0 := by simp

/--
Finite CCR commutator.
-/
@[rep_depth thermo]
def ccrComm {R : Type*} [Ring R] (X Y : R) : R := X * Y - Y * X

/--
If two bosonic generators satisfy a CCR relation `XY - YX = η`,
their reverse-order product is `YX = XY - η`.
-/
@[rep_depth thermo]
theorem ccr_reverse_of_comm
    {R : Type*} [Ring R]
    {X Y η : R}
    (hccr : ccrComm X Y = η) :
    Y * X = X * Y - η := by
  have hxy : X * Y - Y * X = η := by
    simpa [ccrComm] using hccr
  calc
    Y * X = X * Y - (X * Y - Y * X) := by abel
    _ = X * Y - η := by rw [hxy]

/--
Bosonic number-like product identity under central CCR scalar.
If `XY - YX = η` and `η` commutes with `X`, then
`X*(Y*X) = (X*X)*Y - η*X`.
-/
@[rep_depth thermo]
theorem ccr_shift_left
    {R : Type*} [Ring R]
    {X Y η : R}
    (hccr : ccrComm X Y = η)
    (hηX : η * X = X * η) :
    X * (Y * X) = (X * X) * Y - η * X := by
  have hYX : Y * X = X * Y - η := ccr_reverse_of_comm (X := X) (Y := Y) (η := η) hccr
  calc
    X * (Y * X) = X * (X * Y - η) := by rw [hYX]
    _ = X * (X * Y) - X * η := by rw [mul_sub]
    _ = (X * X) * Y - X * η := by rw [mul_assoc]
    _ = (X * X) * Y - η * X := by rw [hηX]

/--
Finite CAR+CCR supergraded closure packet.
Odd generators `(u,v)` satisfy CAR and even generators `(X,Y)` satisfy CCR.
This theorem records the odd-even and even-even bracket forms.
-/
@[rep_depth thermo]
theorem car_ccr_supergraded_closure_packet
    {R : Type*} [Ring R]
    {u v X Y : R}
    {η : R}
    (hcar : u * v + v * u = 1)
    (hccr : ccrComm X Y = η) :
    oddAnticomm u v = 1 ∧ ccrComm X Y = η := by
  exact ⟨hcar, hccr⟩

/--
Nambu doubled CCR lane acts componentwise and preserves the commutator form.
-/
@[rep_depth thermo]
theorem nambu_ccr_componentwise
    {R : Type*} [Ring R]
    {X₁ Y₁ η₁ X₂ Y₂ η₂ : R}
    (h₁ : ccrComm X₁ Y₁ = η₁)
    (h₂ : ccrComm X₂ Y₂ = η₂) :
    ccrComm (R := R × R) (X₁, X₂) (Y₁, Y₂) = (η₁, η₂) := by
  ext
  · simpa [ccrComm] using h₁
  · simpa [ccrComm] using h₂

/--
Finite dissipative update on doubled carrier:
`v ↦ v - K v`, where `K` is a linear-like defect block operator.
-/
@[rep_depth thermo]
def dissipativeStep {R : Type*} [Ring R]
    (K : Nambu2 R → Nambu2 R) :
    Nambu2 R → Nambu2 R :=
  fun v => (v.1 - (K v).1, v.2 - (K v).2)

/--
Applying `dissipativeStep` with identity defect kills the state.
-/
@[rep_depth thermo]
theorem dissipativeStep_id_eq_zero
    {R : Type*} [Ring R] :
    dissipativeStep (R := R) (fun v : Nambu2 R => v) = fun _ => (0, 0) := by
  funext v
  ext <;> simp [dissipativeStep]

/--
Defect-lane closure: if `K` vanishes on the dissipative defect image,
then two dissipative steps collapse:
`(Id-K)∘(Id-K) = Id-K`.
-/
@[rep_depth thermo]
theorem dissipativeStep_idempotent_of_defect_annihilation
    {R : Type*} [Ring R]
    (K : Nambu2 R → Nambu2 R)
    (hdef : ∀ v, K (dissipativeStep K v) = (0, 0)) :
    ∀ v, dissipativeStep K (dissipativeStep K v) = dissipativeStep K v := by
  intro v
  have hk0 : K (dissipativeStep K v) = (0, 0) := hdef v
  have hk0₁ : (K (dissipativeStep K v)).1 = 0 := by
    simpa using congrArg Prod.fst hk0
  have hk0₂ : (K (dissipativeStep K v)).2 = 0 := by
    simpa using congrArg Prod.snd hk0
  ext
  · calc
      (dissipativeStep K (dissipativeStep K v)).1
          = (dissipativeStep K v).1 - (K (dissipativeStep K v)).1 := by
              simp [dissipativeStep]
      _ = (dissipativeStep K v).1 - 0 := by rw [hk0₁]
      _ = (dissipativeStep K v).1 := by simp
  · calc
      (dissipativeStep K (dissipativeStep K v)).2
          = (dissipativeStep K v).2 - (K (dissipativeStep K v)).2 := by
              simp [dissipativeStep]
      _ = (dissipativeStep K v).2 - 0 := by rw [hk0₂]
      _ = (dissipativeStep K v).2 := by simp

/-- Weyl-type finite block: pure diagonal (`b = c = 0`). -/
@[rep_depth thermo]
def isWeylBlock {R : Type*} [Ring R] (a b c d : R) : Prop :=
  b = 0 ∧ c = 0

/-- Majorana-type finite block: symmetric off-diagonal pairing (`b = c`). -/
@[rep_depth thermo]
def isMajoranaBlock {R : Type*} [Ring R] (a b c d : R) : Prop :=
  b = c

/-- Dirac-type finite block: diagonal-matched mass/energy (`a = d`). -/
@[rep_depth thermo]
def isDiracBlock {R : Type*} [Ring R] (a b c d : R) : Prop :=
  a = d

/--
Representation bridge: Weyl block is exactly the no-mixing condition.
-/
@[rep_depth thermo]
theorem weylBlock_iff_no_offdiag
    {R : Type*} [Ring R] (a b c d : R) :
    isWeylBlock (R := R) a b c d ↔ (b = 0 ∧ c = 0) := by
  rfl

/--
Representation bridge: Majorana symmetry is exactly off-diagonal equality.
-/
@[rep_depth thermo]
theorem majoranaBlock_iff_pairing_symmetry
    {R : Type*} [Ring R] (a b c d : R) :
    isMajoranaBlock (R := R) a b c d ↔ b = c := by
  rfl

/--
Representation bridge: Dirac diagonal equality is exactly `a = d`.
-/
@[rep_depth thermo]
theorem diracBlock_iff_diagonal_match
    {R : Type*} [Ring R] (a b c d : R) :
    isDiracBlock (R := R) a b c d ↔ a = d := by
  rfl

/--
Weyl block action has no off-diagonal mixing.
-/
@[rep_depth thermo]
theorem bdgOp_of_weylBlock_eq_diag
    {R : Type*} [Ring R]
    {a b c d : R}
    (hW : isWeylBlock (R := R) a b c d) :
    ∀ v : Nambu2 R, bdgOp a b c d v = bdgDiag a d v := by
  intro v
  rcases hW with ⟨hb, hc⟩
  rcases v with ⟨x, y⟩
  simp [bdgOp_apply, bdgDiag, hb, hc]

/--
Majorana pairing symmetry is preserved by squaring coefficients:
if `b = c`, then in `bdgOp^2` the off-diagonal coefficients remain equal.
-/
@[rep_depth thermo]
theorem majoranaBlock_preserved_under_square
    {R : Type*} [Ring R]
    {a b c d : R}
    (hM : isMajoranaBlock (R := R) a b c d)
    (hab : a * b = b * a)
    (hbd : b * d = d * b) :
    (a * b + b * d) = (c * a + d * c) := by
  rw [isMajoranaBlock] at hM
  have hac : a * c = c * a := by simpa [hM] using hab
  have hcd : c * d = d * c := by simpa [hM] using hbd
  rw [hM, hac, hcd]

/--
Dirac diagonal match is preserved under square coefficients.
-/
@[rep_depth thermo]
theorem diracBlock_preserved_under_square
    {R : Type*} [Ring R]
    {a b c d : R}
    (hD : isDiracBlock (R := R) a b c d) :
    (a * a + b * c) = (c * b + d * d) ↔ b * c = c * b := by
  rcases hD with rfl
  constructor
  · intro h
    have h' := congrArg (fun t => t - a * a) h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
  · intro h
    calc
      a * a + b * c = a * a + c * b := by rw [h]
      _ = c * b + a * a := by simpa [add_comm]
      _ = c * b + a * a := by rfl

/-- Coefficient-level square transform for finite BdG blocks. -/
@[rep_depth thermo]
def bdgSquareCoeffs {R : Type*} [Ring R] (a b c d : R) : R × R × R × R :=
  (a * a + b * c, a * b + b * d, c * a + d * c, c * b + d * d)

/-- First coefficient projection of `bdgSquareCoeffs`. -/
@[rep_depth thermo]
theorem bdgSquareCoeffs_fst
    {R : Type*} [Ring R] (a b c d : R) :
    (bdgSquareCoeffs (R := R) a b c d).1 = a * a + b * c := by
  rfl

/-- Second coefficient projection of `bdgSquareCoeffs`. -/
@[rep_depth thermo]
theorem bdgSquareCoeffs_snd1
    {R : Type*} [Ring R] (a b c d : R) :
    (bdgSquareCoeffs (R := R) a b c d).2.1 = a * b + b * d := by
  rfl

/-- Third coefficient projection of `bdgSquareCoeffs`. -/
@[rep_depth thermo]
theorem bdgSquareCoeffs_snd2fst
    {R : Type*} [Ring R] (a b c d : R) :
    (bdgSquareCoeffs (R := R) a b c d).2.2.1 = c * a + d * c := by
  rfl

/-- Fourth coefficient projection of `bdgSquareCoeffs`. -/
@[rep_depth thermo]
theorem bdgSquareCoeffs_snd2snd
    {R : Type*} [Ring R] (a b c d : R) :
    (bdgSquareCoeffs (R := R) a b c d).2.2.2 = c * b + d * d := by
  rfl

/--
Weyl blocks are preserved by coefficient squaring.
-/
@[rep_depth thermo]
theorem weylBlock_preserved_under_squareCoeffs
    {R : Type*} [Ring R]
    {a b c d : R}
    (hW : isWeylBlock (R := R) a b c d) :
    isWeylBlock (R := R)
      (bdgSquareCoeffs (R := R) a b c d).1
      (bdgSquareCoeffs (R := R) a b c d).2.1
      (bdgSquareCoeffs (R := R) a b c d).2.2.1
      (bdgSquareCoeffs (R := R) a b c d).2.2.2 := by
  rcases hW with ⟨hb, hc⟩
  constructor
  · simp [bdgSquareCoeffs, hb, hc]
  · simp [bdgSquareCoeffs, hb, hc]

/--
Majorana symmetry is preserved by coefficient squaring under commuting
pairing with diagonal lanes.
-/
@[rep_depth thermo]
theorem majoranaBlock_preserved_under_squareCoeffs
    {R : Type*} [Ring R]
    {a b c d : R}
    (hM : isMajoranaBlock (R := R) a b c d)
    (hab : a * b = b * a)
    (hbd : b * d = d * b) :
    isMajoranaBlock (R := R)
      (bdgSquareCoeffs (R := R) a b c d).1
      (bdgSquareCoeffs (R := R) a b c d).2.1
      (bdgSquareCoeffs (R := R) a b c d).2.2.1
      (bdgSquareCoeffs (R := R) a b c d).2.2.2 := by
  show (bdgSquareCoeffs (R := R) a b c d).2.1 = (bdgSquareCoeffs (R := R) a b c d).2.2.1
  exact majoranaBlock_preserved_under_square (a := a) (b := b) (c := c) (d := d) hM hab hbd

/--
Dirac diagonal match is preserved by coefficient squaring exactly when pairing
coefficients commute.
-/
@[rep_depth thermo]
theorem diracBlock_preserved_under_squareCoeffs
    {R : Type*} [Ring R]
    {a b c d : R}
    (hD : isDiracBlock (R := R) a b c d) :
    isDiracBlock (R := R)
      (bdgSquareCoeffs (R := R) a b c d).1
      (bdgSquareCoeffs (R := R) a b c d).2.1
      (bdgSquareCoeffs (R := R) a b c d).2.2.1
      (bdgSquareCoeffs (R := R) a b c d).2.2.2
      ↔ b * c = c * b := by
  change
    (bdgSquareCoeffs (R := R) a b c d).1 = (bdgSquareCoeffs (R := R) a b c d).2.2.2
      ↔ b * c = c * b
  simpa [isDiracBlock] using
    diracBlock_preserved_under_square (a := a) (b := b) (c := c) (d := d) hD

/--
Operator-level reconstruction:
the square of a BdG block equals the BdG operator built from `bdgSquareCoeffs`.
-/
@[rep_depth thermo]
theorem bdgOp_sq_eq_bdgOp_of_squareCoeffs
    {R : Type*} [Ring R]
    (a b c d : R) :
    ∀ v : Nambu2 R,
      bdgOp a b c d (bdgOp a b c d v)
        =
      bdgOp
        (bdgSquareCoeffs (R := R) a b c d).1
        (bdgSquareCoeffs (R := R) a b c d).2.1
        (bdgSquareCoeffs (R := R) a b c d).2.2.1
        (bdgSquareCoeffs (R := R) a b c d).2.2.2
        v := by
  intro v
  simpa [bdgSquareCoeffs] using
    bdgOp_sq_eq_bdgOp_coeffs (a := a) (b := b) (c := c) (d := d) v

/--
Coordinate-level reconstruction:
the explicit two coordinates of `bdgOp^2` are exactly those induced by
`bdgSquareCoeffs`.
-/
@[rep_depth thermo]
theorem bdgOp_sq_apply_via_squareCoeffs
    {R : Type*} [Ring R]
    (a b c d x y : R) :
    bdgOp a b c d (bdgOp a b c d (x, y))
      =
    ( (bdgSquareCoeffs (R := R) a b c d).1 * x
        + (bdgSquareCoeffs (R := R) a b c d).2.1 * y,
      (bdgSquareCoeffs (R := R) a b c d).2.2.1 * x
        + (bdgSquareCoeffs (R := R) a b c d).2.2.2 * y ) := by
  calc
    bdgOp a b c d (bdgOp a b c d (x, y))
        =
      bdgOp
        (bdgSquareCoeffs (R := R) a b c d).1
        (bdgSquareCoeffs (R := R) a b c d).2.1
        (bdgSquareCoeffs (R := R) a b c d).2.2.1
        (bdgSquareCoeffs (R := R) a b c d).2.2.2
        (x, y) := by
          simpa using bdgOp_sq_eq_bdgOp_of_squareCoeffs (a := a) (b := b) (c := c) (d := d) (x, y)
    _ =
      ( (bdgSquareCoeffs (R := R) a b c d).1 * x
          + (bdgSquareCoeffs (R := R) a b c d).2.1 * y,
        (bdgSquareCoeffs (R := R) a b c d).2.2.1 * x
          + (bdgSquareCoeffs (R := R) a b c d).2.2.2 * y ) := by
          simpa using
            bdgOp_apply
              (a := (bdgSquareCoeffs (R := R) a b c d).1)
              (b := (bdgSquareCoeffs (R := R) a b c d).2.1)
              (c := (bdgSquareCoeffs (R := R) a b c d).2.2.1)
              (d := (bdgSquareCoeffs (R := R) a b c d).2.2.2)
              x y

/--
Cube-iterate closure:
`bdgOp^3` is `bdgOp` composed with the squared-coefficient block.
-/
@[rep_depth thermo]
theorem bdgOp_cube_eq_comp_squareCoeffs
    {R : Type*} [Ring R]
    (a b c d : R) :
    ∀ v : Nambu2 R,
      bdgOp a b c d (bdgOp a b c d (bdgOp a b c d v))
        =
      bdgOp a b c d
        (bdgOp
          (bdgSquareCoeffs (R := R) a b c d).1
          (bdgSquareCoeffs (R := R) a b c d).2.1
          (bdgSquareCoeffs (R := R) a b c d).2.2.1
          (bdgSquareCoeffs (R := R) a b c d).2.2.2
          v) := by
  intro v
  rw [← bdgOp_sq_eq_bdgOp_of_squareCoeffs (a := a) (b := b) (c := c) (d := d) v]

/--
Closure-by-composition:
composing a BdG block with its squared-coefficient block is again a BdG block
with explicit cubic-step coefficients.
-/
@[rep_depth thermo]
theorem bdgOp_comp_squareCoeffs_eq_bdgOp
    {R : Type*} [Ring R]
    (a b c d : R) :
    ∀ v : Nambu2 R,
      bdgOp a b c d
        (bdgOp
          (bdgSquareCoeffs (R := R) a b c d).1
          (bdgSquareCoeffs (R := R) a b c d).2.1
          (bdgSquareCoeffs (R := R) a b c d).2.2.1
          (bdgSquareCoeffs (R := R) a b c d).2.2.2
          v)
        =
      bdgOp
        (a * (bdgSquareCoeffs (R := R) a b c d).1
          + b * (bdgSquareCoeffs (R := R) a b c d).2.2.1)
        (a * (bdgSquareCoeffs (R := R) a b c d).2.1
          + b * (bdgSquareCoeffs (R := R) a b c d).2.2.2)
        (c * (bdgSquareCoeffs (R := R) a b c d).1
          + d * (bdgSquareCoeffs (R := R) a b c d).2.2.1)
        (c * (bdgSquareCoeffs (R := R) a b c d).2.1
          + d * (bdgSquareCoeffs (R := R) a b c d).2.2.2)
        v := by
  intro v
  simpa using
    bdgOp_comp_eq_bdgOp_mulCoeffs
      (a := a) (b := b) (c := c) (d := d)
      (a' := (bdgSquareCoeffs (R := R) a b c d).1)
      (b' := (bdgSquareCoeffs (R := R) a b c d).2.1)
      (c' := (bdgSquareCoeffs (R := R) a b c d).2.2.1)
      (d' := (bdgSquareCoeffs (R := R) a b c d).2.2.2)
      v

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
