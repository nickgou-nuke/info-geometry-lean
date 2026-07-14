import Mathlib
import InfoGeometry.Topology.V4RootSystem

/-!
# V4 / Q8 projective bridge

This finite owner file records the pure group-theoretic relation between the
Klein four group `V₄` and the quaternionic `Q₈` shadow:

* a concrete finite `Q₈` carrier with the standard quaternion multiplication
  table;
* the quotient map `Q₈ → V₄` that kills the central sign `±1`;
* explicit quaternionic generator relations for the standard `Q₈` basis;
* a projective-sign witness showing that the generator commutator is central.

The standard 2×2 complex matrix witness for the projective representation is
kept in the external certificates.  This file stays theorem-safe and finite:
it does not assert a full Schur-multiplier classification theorem.
-/

namespace V4Q8ProjectiveBridge

open InfoGeometry.Topology.V4RootSystem

/-- The finite `Q₈` carrier presented by eight named elements. -/
inductive Q8Elt where
  | p1
  | m1
  | i
  | mi
  | j
  | mj
  | k
  | mk
  deriving DecidableEq, Repr, Fintype

namespace Q8Elt

/-- Sign flip on the finite `Q₈` carrier. -/
def neg : Q8Elt → Q8Elt
  | p1 => m1
  | m1 => p1
  | i => mi
  | mi => i
  | j => mj
  | mj => j
  | k => mk
  | mk => k

/-- The quaternion multiplication table. -/
def mul : Q8Elt → Q8Elt → Q8Elt
  | p1, x => x
  | x, p1 => x
  | m1, x => neg x
  | x, m1 => neg x
  | i, i => m1
  | i, mi => p1
  | i, j => k
  | i, mj => mk
  | i, k => mj
  | i, mk => j
  | mi, i => p1
  | mi, mi => m1
  | mi, j => mk
  | mi, mj => k
  | mi, k => j
  | mi, mk => mj
  | j, i => mk
  | j, mi => k
  | j, j => m1
  | j, mj => p1
  | j, k => i
  | j, mk => mi
  | mj, i => k
  | mj, mi => mk
  | mj, j => p1
  | mj, mj => m1
  | mj, k => mi
  | mj, mk => i
  | k, i => j
  | k, mi => mj
  | k, j => mi
  | k, mj => i
  | k, k => m1
  | k, mk => p1
  | mk, i => mj
  | mk, mi => j
  | mk, j => i
  | mk, mj => mi
  | mk, k => p1
  | mk, mk => m1

/-- Inversion on the finite `Q₈` carrier. -/
def inv : Q8Elt → Q8Elt
  | p1 => p1
  | m1 => m1
  | i => mi
  | mi => i
  | j => mj
  | mj => j
  | k => mk
  | mk => k

instance : One Q8Elt := ⟨p1⟩
instance : Mul Q8Elt := ⟨mul⟩
instance : Inv Q8Elt := ⟨inv⟩

@[simp] theorem one_def : (1 : Q8Elt) = p1 := rfl
@[simp] theorem neg_def : neg p1 = m1 := rfl

theorem mul_assoc : ∀ a b c : Q8Elt, (a * b) * c = a * (b * c) := by
  intro a b c
  cases a <;> cases b <;> cases c <;> decide

theorem one_mul : ∀ a : Q8Elt, (1 : Q8Elt) * a = a := by
  intro a
  cases a <;> decide

theorem mul_one : ∀ a : Q8Elt, a * (1 : Q8Elt) = a := by
  intro a
  cases a <;> decide

theorem inv_mul_cancel : ∀ a : Q8Elt, a⁻¹ * a = (1 : Q8Elt) := by
  intro a
  cases a <;> decide

instance : Group Q8Elt where
  one := p1
  mul := mul
  inv := inv
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := inv_mul_cancel

/-- The central sign `-1` is order two. -/
theorem m1_sq : m1 * m1 = (1 : Q8Elt) := by
  decide

/-- The `i`, `j`, `k` basis elements square to `-1`. -/
theorem i_sq : i * i = m1 := by
  decide

theorem j_sq : j * j = m1 := by
  decide

theorem k_sq : k * k = m1 := by
  decide

/-- The standard quaternion multiplication table on the generators. -/
theorem ij_eq_k : i * j = k := by
  decide

theorem ji_eq_mk : j * i = mk := by
  decide

theorem jk_eq_i : j * k = i := by
  decide

theorem kj_eq_mi : k * j = mi := by
  decide

theorem ki_eq_j : k * i = j := by
  decide

theorem ik_eq_mj : i * k = mj := by
  decide

/-- The central sign commutes with everything. -/
theorem m1_mul (a : Q8Elt) : m1 * a = neg a := by
  cases a <;> decide

theorem mul_m1 (a : Q8Elt) : a * m1 = neg a := by
  cases a <;> decide

end Q8Elt

open Q8Elt

/-- The quotient `Q₈ → V₄` kills the central sign and remembers the axis. -/
def q8ToV4 : Q8Elt → V4Group
  | p1 => V4Group.I
  | m1 => V4Group.I
  | i => V4Group.W1
  | mi => V4Group.W1
  | j => V4Group.W2
  | mj => V4Group.W2
  | k => V4Group.W12
  | mk => V4Group.W12

/-- The quotient map is multiplicative. -/
theorem q8ToV4_mul (a b : Q8Elt) :
    q8ToV4 (a * b) = q8ToV4 a * q8ToV4 b := by
  cases a <;> cases b <;> decide

/-- The central sign lands in the identity coset. -/
theorem q8ToV4_m1 : q8ToV4 m1 = V4Group.I := by
  rfl

/-- The quotient map is surjective. -/
theorem q8ToV4_surjective : Function.Surjective q8ToV4 := by
  intro x
  cases x <;>
    first
    | refine ⟨p1, rfl⟩
    | refine ⟨i, rfl⟩
    | refine ⟨j, rfl⟩
    | refine ⟨k, rfl⟩

/-- The kernel of the quotient map is exactly the central sign pair. -/
theorem q8ToV4_kernel :
    ∀ a : Q8Elt, q8ToV4 a = V4Group.I ↔ a = p1 ∨ a = m1 := by
  intro a
  cases a <;> decide

/-- The finite central-extension packet `1 → ±1 → Q₈ → V₄ → 1`. -/
theorem q8_central_extension_packet :
    q8ToV4 p1 = V4Group.I ∧
    q8ToV4 m1 = V4Group.I ∧
    q8ToV4 i = V4Group.W1 ∧
    q8ToV4 j = V4Group.W2 ∧
    q8ToV4 k = V4Group.W12 ∧
    Function.Surjective q8ToV4 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, q8ToV4_surjective⟩

end V4Q8ProjectiveBridge
