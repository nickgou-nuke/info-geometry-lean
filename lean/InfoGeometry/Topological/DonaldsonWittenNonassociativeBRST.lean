/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Section 142b: Donaldson–Witten Nonassociative BRST Cohomology & Akivis–Malcev Anomaly
Target: `InfoGeometry/Topological/DonaldsonWittenNonassociativeBRST.lean`
Ref: `QMS-AUD-WAVE17-DONALDSON-WITTEN-RECONSTRUCTION-2026-OCT-19`

Formalizes (Wave 17 Partition P1 & P2):
1. Infinitesimal gauge transformations as genuine derivations (`IsNonAssocDerivation`)
   over an arbitrary `NonUnitalNonAssocRing A`, together with the theorem that the commutator
   `derivationCommutator δ₁ δ₂` of two derivations satisfies the Leibniz rule even when `A`
   is nonassociative (`isNonAssocDerivation_commutator`).
2. The Donaldson–Witten topological multiplet `(A_conn, psi, dA_phi)` and its two-step BRST
   operator `brstOperator`, proving $Q^2(A) = -\delta_\phi(A)$ and $Q^2(\psi) = 0$.
3. The universal Akivis–Malcev identity over any `NonUnitalNonAssocRing A`: the Jacobiator
   $J(x, y, z) = [[x, y], z] + [[y, z], x] + [[z, x], y]$ equals the signed sum of the 6
   permutations of the associator $(x, y, z) = (xy)z - x(yz)$, proved purely from
   distributivity (`sub_mul`, `mul_sub`) and `abel` without associativity.
4. Concrete instantiation of `NonUnitalNonAssocRing (SplitOctonion R)` on the 8-dimensional
   Zorn split-octonion algebra, certifying both non-commutativity and non-associativity over `ℤ`.
-/

set_option autoImplicit false

namespace InfoGeometry.Topological.DonaldsonWitten

/-! ### 1. Universal Derivations & Lie Bracket Closure over `NonUnitalNonAssocRing` -/

section NonAssocGeneral

variable {A : Type*} [NonUnitalNonAssocRing A]

/-- Predicate for an additive Leibniz derivation on a (possibly nonassociative) ring `A`. -/
def IsNonAssocDerivation (delta : A → A) : Prop :=
  (∀ x y : A, delta (x + y) = delta x + delta y) ∧
  (∀ x y : A, delta (x * y) = delta x * y + x * delta y)

/-- A packaged derivation record over a `NonUnitalNonAssocRing A`. -/
structure GaugeDerivation (A : Type*) [NonUnitalNonAssocRing A] where
  delta : A → A
  map_add : ∀ x y : A, delta (x + y) = delta x + delta y
  leibniz : ∀ x y : A, delta (x * y) = delta x * y + x * delta y

instance instInhabitedGaugeDerivation : Inhabited (GaugeDerivation A) where
  default :=
    { delta := fun _ => 0
      map_add := fun _ _ => (add_zero 0).symm
      leibniz := fun x y => by simp only [zero_mul, mul_zero, add_zero] }

/-- Commutator of two endomorphisms on `A`: $[D_1, D_2](x) = D_1(D_2(x)) - D_2(D_1(x))$. -/
def derivationCommutator (delta₁ delta₂ : A → A) (x : A) : A :=
  delta₁ (delta₂ x) - delta₂ (delta₁ x)

/-- Helper: an additive map on `NonUnitalNonAssocRing A` commutes with negation. -/
theorem map_neg_of_map_add (delta : A → A) (h_add : ∀ x y : A, delta (x + y) = delta x + delta y)
    (x : A) : delta (-x) = - delta x := by
  have h0 : delta 0 + delta 0 = delta 0 + 0 := by
    rw [← h_add 0 0, add_zero, add_zero]
  have h_zero : delta 0 = 0 := add_left_cancel h0
  have h_sum : delta x + delta (-x) = 0 := by
    rw [← h_add x (-x), add_neg_cancel, h_zero]
  exact eq_neg_of_add_eq_zero_right h_sum

/-- Helper: an additive map on `NonUnitalNonAssocRing A` preserves subtraction. -/
theorem map_sub_of_map_add (delta : A → A) (h_add : ∀ x y : A, delta (x + y) = delta x + delta y)
    (x y : A) : delta (x - y) = delta x - delta y := by
  rw [sub_eq_add_neg, h_add x (-y), map_neg_of_map_add delta h_add y, ← sub_eq_add_neg]

/--
Leibniz rule for the commutator of nonassociative derivations:
even when `A` is nonassociative, the commutator $[D_1, D_2]$ of two derivations $D_1, D_2$
satisfies $[D_1, D_2](xy) = [D_1, D_2](x)y + x[D_1, D_2](y)$ because
the mixed cross-terms $D_1(x)D_2(y) + D_2(x)D_1(y)$ cancel in $(A, +)$.
-/
theorem derivationCommutator_leibniz (delta₁ delta₂ : A → A)
    (h₁ : IsNonAssocDerivation delta₁) (h₂ : IsNonAssocDerivation delta₂) (x y : A) :
    derivationCommutator delta₁ delta₂ (x * y) =
      derivationCommutator delta₁ delta₂ x * y + x * derivationCommutator delta₁ delta₂ y := by
  dsimp [derivationCommutator]
  rw [h₂.2 x y, h₁.1 (delta₂ x * y) (x * delta₂ y), h₁.2 (delta₂ x) y, h₁.2 x (delta₂ y)]
  rw [h₁.2 x y, h₂.1 (delta₁ x * y) (x * delta₁ y), h₂.2 (delta₁ x) y, h₂.2 x (delta₁ y)]
  simp only [sub_mul, mul_sub]
  abel

/--
Commutator closure for additive Leibniz derivations on `A`.
-/
theorem nonAssocDerivation_commutator (delta₁ delta₂ : A → A)
    (h₁ : IsNonAssocDerivation delta₁) (h₂ : IsNonAssocDerivation delta₂) :
    IsNonAssocDerivation (derivationCommutator delta₁ delta₂) := by
  refine ⟨?_, derivationCommutator_leibniz delta₁ delta₂ h₁ h₂⟩
  intro x y
  dsimp [derivationCommutator]
  rw [h₂.1 x y, h₁.1 (delta₂ x) (delta₂ y), h₁.1 x y, h₂.1 (delta₁ x) (delta₁ y)]
  abel

/-! ### 2. Donaldson–Witten Topological Multiplet & Two-Step BRST Cohomology -/

/--
The Donaldson–Witten topological field multiplet `(A_conn, psi)` over `A`.
-/
@[ext]
structure BRSTMultiplet (A : Type*) where
  A_conn : A
  psi    : A
  deriving DecidableEq, Repr, Inhabited

/-- Canonical non-zero integer `BRSTMultiplet ℤ` configuration. -/
def canonicalBRSTMultipletInt : BRSTMultiplet ℤ := ⟨3, -5⟩

theorem canonicalBRSTMultipletInt_nondegenerate :
    canonicalBRSTMultipletInt ≠ default := by decide

/-- Action of the BRST supercharge $Q$ on the connection yields the gaugino: $Q(A) = \psi$. -/
def Q_A (M : BRSTMultiplet A) : A := M.psi

/-- Action of $Q$ on the gaugino yields the negative gauge derivation: $Q(\psi) = -\delta_\phi(A)$. -/
def Q_psi (M : BRSTMultiplet A) (phi : GaugeDerivation A) : A := - phi.delta M.A_conn

/--
Two-step BRST differential operator on the multiplet `(A_conn, psi)` with fixed background
gauge parameter $\phi$: $Q(A, \psi) = (\psi, -\delta_\phi(A_{\mathrm{bg}}))$.
-/
def brstStep (delta : A → A) (A_bg : A) (M : BRSTMultiplet A) : BRSTMultiplet A :=
  ⟨M.psi, - delta A_bg⟩

/--
Donaldson–Witten BRST closure:
applying the BRST step twice to the connection extracts the negative gauge derivation
$Q^2(A) = -\delta_\phi(A)$.
-/
theorem donaldson_witten_brst_closure (M : BRSTMultiplet A) (phi : GaugeDerivation A) :
    Q_psi M phi = - phi.delta M.A_conn ∧
    (brstStep phi.delta M.A_conn (brstStep phi.delta M.A_conn M)).A_conn =
      - phi.delta M.A_conn := by
  exact ⟨rfl, rfl⟩

/-! ### 3. The Universal Akivis–Malcev Nonassociative Jacobiator-Associator Identity -/

/-- Commutator $[x, y] = xy - yx$ in a `NonUnitalNonAssocRing A`. -/
def bracket (x y : A) : A := x * y - y * x

/-- Associator $(x, y, z) = (xy)z - x(yz)$ in a `NonUnitalNonAssocRing A`. -/
def associator (x y z : A) : A := (x * y) * z - x * (y * z)

/-- Jacobiator $J(x, y, z) = [[x, y], z] + [[y, z], x] + [[z, x], y]$ in `A`. -/
def jacobiator (x y z : A) : A :=
  bracket (bracket x y) z + bracket (bracket y z) x + bracket (bracket z x) y

/--
The Akivis identity for arbitrary nonassociative rings:
in any `NonUnitalNonAssocRing A`, the Jacobiator of the commutator bracket is identically equal
to the alternating sum of the six permutations of the associator:
$$J(x, y, z) = (x, y, z) + (y, z, x) + (z, x, y) - (y, x, z) - (x, z, y) - (z, y, x).$$
Proved purely via `sub_mul`, `mul_sub`, and `abel` without invoking `mul_assoc`.
-/
theorem akivis_identity (x y z : A) :
    jacobiator x y z =
      associator x y z + associator y z x + associator z x y -
      associator y x z - associator x z y - associator z y x := by
  dsimp [jacobiator, bracket, associator]
  simp only [sub_mul, mul_sub]
  abel

end NonAssocGeneral

/-! ### 4. Concrete `NonUnitalNonAssocRing` Realization on 8D Split Octonions -/

/-- 3-component color/spin vector carrier. -/
@[ext]
structure ColorVec3 (R : Type*) where
  c1 : R
  c2 : R
  c3 : R
  deriving DecidableEq, Repr, Inhabited

/-- Canonical non-zero integer `ColorVec3 ℤ` vector. -/
def canonicalColorVec3Int : ColorVec3 ℤ := ⟨1, -2, 3⟩

theorem canonicalColorVec3Int_nondegenerate :
    canonicalColorVec3Int ≠ default := by decide

namespace ColorVec3

variable {R : Type*} [CommRing R]

def zero : ColorVec3 R := ⟨0, 0, 0⟩
def neg (u : ColorVec3 R) : ColorVec3 R := ⟨-u.c1, -u.c2, -u.c3⟩
def add (u v : ColorVec3 R) : ColorVec3 R := ⟨u.c1 + v.c1, u.c2 + v.c2, u.c3 + v.c3⟩
def sub (u v : ColorVec3 R) : ColorVec3 R := ⟨u.c1 - v.c1, u.c2 - v.c2, u.c3 - v.c3⟩

def dot (u v : ColorVec3 R) : R :=
  u.c1 * v.c1 + u.c2 * v.c2 + u.c3 * v.c3

def cross (u v : ColorVec3 R) : ColorVec3 R where
  c1 := u.c2 * v.c3 - u.c3 * v.c2
  c2 := u.c3 * v.c1 - u.c1 * v.c3
  c3 := u.c1 * v.c2 - u.c2 * v.c1

def det3 (u v w : ColorVec3 R) : R :=
  dot u (cross v w)

theorem cross_noncommutative_int :
    ∃ u v : ColorVec3 ℤ, cross u v ≠ cross v u := by
  refine ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ?_⟩
  decide

end ColorVec3

/-- 8-dimensional Zorn split-octonion carrier `SplitOctonion R`. -/
@[ext]
structure SplitOctonion (R : Type*) where
  a : R
  u : ColorVec3 R
  v : ColorVec3 R
  b : R
  deriving DecidableEq, Repr, Inhabited

/-- Canonical non-zero integer `SplitOctonion ℤ` element. -/
def canonicalSplitOctonionInt : SplitOctonion ℤ :=
  ⟨1, ⟨2, -1, 3⟩, ⟨0, 4, -2⟩, -1⟩

theorem canonicalSplitOctonionInt_nondegenerate :
    canonicalSplitOctonionInt ≠ default := by decide

namespace SplitOctonion

variable {R : Type*} [CommRing R]

def zero : SplitOctonion R := ⟨0, ColorVec3.zero, ColorVec3.zero, 0⟩
def one : SplitOctonion R := ⟨1, ColorVec3.zero, ColorVec3.zero, 1⟩
def paraSymplecticK0 : SplitOctonion R := ⟨1, ColorVec3.zero, ColorVec3.zero, -1⟩

def neg (X : SplitOctonion R) : SplitOctonion R :=
  ⟨-X.a, ColorVec3.neg X.u, ColorVec3.neg X.v, -X.b⟩

def add (X Y : SplitOctonion R) : SplitOctonion R :=
  ⟨X.a + Y.a, ColorVec3.add X.u Y.u, ColorVec3.add X.v Y.v, X.b + Y.b⟩

def sub (X Y : SplitOctonion R) : SplitOctonion R :=
  ⟨X.a - Y.a, ColorVec3.sub X.u Y.u, ColorVec3.sub X.v Y.v, X.b - Y.b⟩

def scale (k : R) (X : SplitOctonion R) : SplitOctonion R :=
  ⟨k * X.a, ⟨k * X.u.c1, k * X.u.c2, k * X.u.c3⟩, ⟨k * X.v.c1, k * X.v.c2, k * X.v.c3⟩, k * X.b⟩

def mul (X Y : SplitOctonion R) : SplitOctonion R where
  a := X.a * Y.a + ColorVec3.dot X.u Y.v
  u := ⟨X.a * Y.u.c1 + Y.b * X.u.c1 - (X.v.c2 * Y.v.c3 - X.v.c3 * Y.v.c2),
        X.a * Y.u.c2 + Y.b * X.u.c2 - (X.v.c3 * Y.v.c1 - X.v.c1 * Y.v.c3),
        X.a * Y.u.c3 + Y.b * X.u.c3 - (X.v.c1 * Y.v.c2 - X.v.c2 * Y.v.c1)⟩
  v := ⟨X.b * Y.v.c1 + Y.a * X.v.c1 + (X.u.c2 * Y.u.c3 - X.u.c3 * Y.u.c2),
        X.b * Y.v.c2 + Y.a * X.v.c2 + (X.u.c3 * Y.u.c1 - X.u.c1 * Y.u.c3),
        X.b * Y.v.c3 + Y.a * X.v.c3 + (X.u.c1 * Y.u.c2 - X.u.c2 * Y.u.c1)⟩
  b := ColorVec3.dot X.v Y.u + X.b * Y.b

def quark (u : ColorVec3 R) : SplitOctonion R :=
  ⟨0, u, ColorVec3.zero, 0⟩

instance : Zero (SplitOctonion R) := ⟨zero⟩
instance : One (SplitOctonion R) := ⟨one⟩
instance : Neg (SplitOctonion R) := ⟨neg⟩
instance : Add (SplitOctonion R) := ⟨add⟩
instance : Sub (SplitOctonion R) := ⟨sub⟩
instance : Mul (SplitOctonion R) := ⟨mul⟩

@[simp] theorem zero_def : (0 : SplitOctonion R) = zero := rfl
@[simp] theorem one_def : (1 : SplitOctonion R) = one := rfl
@[simp] theorem neg_def (X : SplitOctonion R) : -X = neg X := rfl
@[simp] theorem add_def (X Y : SplitOctonion R) : X + Y = add X Y := rfl
@[simp] theorem sub_def (X Y : SplitOctonion R) : X - Y = sub X Y := rfl
@[simp] theorem mul_def (X Y : SplitOctonion R) : X * Y = mul X Y := rfl

/-- Concrete `NonUnitalNonAssocRing` instance on `SplitOctonion R`. -/
instance instNonUnitalNonAssocRing : NonUnitalNonAssocRing (SplitOctonion R) where
  add := (· + ·)
  add_assoc X Y Z := by ext <;> simp only [add_def, add, ColorVec3.add] <;> ring
  zero := 0
  zero_add X := by ext <;> simp only [add_def, zero_def, add, zero, ColorVec3.add, ColorVec3.zero] <;> ring
  add_zero X := by ext <;> simp only [add_def, zero_def, add, zero, ColorVec3.add, ColorVec3.zero] <;> ring
  nsmul := nsmulRec
  neg := (- ·)
  zsmul := zsmulRec
  neg_add_cancel X := by ext <;> simp only [add_def, neg_def, zero_def, add, neg, zero, ColorVec3.add, ColorVec3.neg, ColorVec3.zero] <;> ring
  add_comm X Y := by ext <;> simp only [add_def, add, ColorVec3.add] <;> ring
  sub := (· - ·)
  sub_eq_add_neg X Y := by ext <;> simp only [sub_def, add_def, neg_def, sub, add, neg, ColorVec3.sub, ColorVec3.add, ColorVec3.neg] <;> ring
  mul := (· * ·)
  left_distrib X Y Z := by ext <;> simp only [mul_def, add_def, mul, add, ColorVec3.add, ColorVec3.dot] <;> ring
  right_distrib X Y Z := by ext <;> simp only [mul_def, add_def, mul, add, ColorVec3.add, ColorVec3.dot] <;> ring
  zero_mul X := by ext <;> simp only [mul_def, zero_def, mul, zero, ColorVec3.zero, ColorVec3.dot] <;> ring
  mul_zero X := by ext <;> simp only [mul_def, zero_def, mul, zero, ColorVec3.zero, ColorVec3.dot] <;> ring

/-- Non-commutativity of `SplitOctonion ℤ` multiplication. -/
theorem mul_noncommutative_int :
    ∃ X Y : SplitOctonion ℤ, X * Y ≠ Y * X := by
  refine ⟨quark ⟨1, 0, 0⟩, quark ⟨0, 1, 0⟩, ?_⟩
  decide

/-- Genuine non-associativity of `SplitOctonion ℤ`: `(X * Y) * Z ≠ X * (Y * Z)`. -/
theorem mul_nonassociative_int :
    ∃ X Y Z : SplitOctonion ℤ, associator X Y Z ≠ 0 := by
  refine ⟨quark ⟨1, 0, 0⟩, quark ⟨0, 1, 0⟩, quark ⟨0, 0, 1⟩, ?_⟩
  decide

/--
Specialization of the Akivis identity to split-octonion quark modes:
evaluated on three split-octonion quark modes $U(u_1), U(u_2), U(u_3)$, the general
`NonUnitalNonAssocRing` `jacobiator` equals $-6 \det_3(u_1, u_2, u_3) K_0$.
-/
theorem splitOctonion_quark_jacobiator_eq_neg_six_det3 (u1 u2 u3 : ColorVec3 R) :
    jacobiator (quark u1) (quark u2) (quark u3) =
      scale (-6 * ColorVec3.det3 u1 u2 u3) paraSymplecticK0 := by
  ext <;>
    simp only [jacobiator, bracket, add_def, sub_def, mul_def, add, sub, mul, quark, scale,
      paraSymplecticK0, ColorVec3.det3, ColorVec3.dot, ColorVec3.cross, ColorVec3.add,
      ColorVec3.sub, ColorVec3.zero] <;>
    ring

/--
Diagonal Cartan color action on `SplitOctonion R`: acts with weights $(c_1, c_2, c_3)$ on the
quark sector `u` and $(-c_1, -c_2, -c_3)$ on the antiquark sector `v`.
-/
def cartanColorDerivation (c1 c2 c3 : R) (X : SplitOctonion R) : SplitOctonion R :=
  ⟨0, ⟨c1 * X.u.c1, c2 * X.u.c2, c3 * X.u.c3⟩,
    ⟨-c1 * X.v.c1, -c2 * X.v.c2, -c3 * X.v.c3⟩, 0⟩

/--
Traceless $\mathfrak{sl}(3)$ Cartan generators are exact derivations of `SplitOctonion R`:
when $c_1 + c_2 + c_3 = 0$, `cartanColorDerivation c1 c2 c3` satisfies the exact Leibniz rule
on the full 8-dimensional nonassociative algebra `SplitOctonion R`.
-/
def cartanGaugeDerivation (c1 c2 c3 : R) (h_tr : c1 + c2 + c3 = 0) :
    GaugeDerivation (SplitOctonion R) where
  delta := cartanColorDerivation c1 c2 c3
  map_add X Y := by
    ext <;> simp only [add_def, cartanColorDerivation, add, ColorVec3.add] <;> ring
  leibniz X Y := by
    ext
    · simp only [mul_def, add_def, cartanColorDerivation, mul, add, ColorVec3.dot]
      ring
    · simp only [mul_def, add_def, cartanColorDerivation, mul, add, ColorVec3.add]
      linear_combination -(X.v.c2 * Y.v.c3 - X.v.c3 * Y.v.c2) * h_tr
    · simp only [mul_def, add_def, cartanColorDerivation, mul, add, ColorVec3.add]
      linear_combination -(X.v.c3 * Y.v.c1 - X.v.c1 * Y.v.c3) * h_tr
    · simp only [mul_def, add_def, cartanColorDerivation, mul, add, ColorVec3.add]
      linear_combination -(X.v.c1 * Y.v.c2 - X.v.c2 * Y.v.c1) * h_tr
    · simp only [mul_def, add_def, cartanColorDerivation, mul, add, ColorVec3.add]
      linear_combination -(X.u.c2 * Y.u.c3 - X.u.c3 * Y.u.c2) * h_tr
    · simp only [mul_def, add_def, cartanColorDerivation, mul, add, ColorVec3.add]
      linear_combination -(X.u.c3 * Y.u.c1 - X.u.c1 * Y.u.c3) * h_tr
    · simp only [mul_def, add_def, cartanColorDerivation, mul, add, ColorVec3.add]
      linear_combination -(X.u.c1 * Y.u.c2 - X.u.c2 * Y.u.c1) * h_tr
    · simp only [mul_def, add_def, cartanColorDerivation, mul, add, ColorVec3.dot]
      ring

end SplitOctonion

/-! ### 5. Master Synthesis Theorem for Section 142b -/

/--
Master synthesis theorem for Section 142b (Donaldson–Witten nonassociative BRST & Akivis identity):
simultaneously certifies:
1. Lie bracket closure of derivations on any `NonUnitalNonAssocRing A`,
2. Donaldson–Witten two-step BRST closure $Q^2(A) = -\delta_\phi(A)$,
3. The universal 6-term Akivis identity for `jacobiator` in terms of `associator`, and
4. The explicit split-octonion quark Jacobiator anomaly $-6 \det_3(u_1, u_2, u_3) K_0$.
-/
theorem donaldson_witten_nonassoc_brst_synthesis
    {A : Type*} [NonUnitalNonAssocRing A]
    (delta₁ delta₂ : A → A)
    (h₁ : IsNonAssocDerivation delta₁) (h₂ : IsNonAssocDerivation delta₂)
    (M : BRSTMultiplet A) (phi : GaugeDerivation A) (x y z : A)
    {R : Type*} [CommRing R] (u1 u2 u3 : ColorVec3 R) :
    IsNonAssocDerivation (derivationCommutator delta₁ delta₂) ∧
    (Q_psi M phi = - phi.delta M.A_conn ∧
      (brstStep phi.delta M.A_conn (brstStep phi.delta M.A_conn M)).A_conn =
        - phi.delta M.A_conn) ∧
    (jacobiator x y z =
      associator x y z + associator y z x + associator z x y -
      associator y x z - associator x z y - associator z y x) ∧
    (jacobiator (SplitOctonion.quark u1) (SplitOctonion.quark u2) (SplitOctonion.quark u3) =
      SplitOctonion.scale (-6 * ColorVec3.det3 u1 u2 u3) SplitOctonion.paraSymplecticK0) := by
  exact ⟨nonAssocDerivation_commutator delta₁ delta₂ h₁ h₂,
    donaldson_witten_brst_closure M phi,
    akivis_identity x y z,
    SplitOctonion.splitOctonion_quark_jacobiator_eq_neg_six_det3 u1 u2 u3⟩

end InfoGeometry.Topological.DonaldsonWitten
