import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.ThermalCompactRecurrence

Finite algebraic recurrences for compactified thermal coordinates.

The compactified coordinate is represented by cross-multiplied equations of the
form

`T * (1 + q) = 1 - q`.

The lemmas below prove the exact addition step and the doubled-index step at
pure ring level.  The executable functions use explicit inversion functions as
parameters; no functional calculus, Taylor expansion, analytic continuation, or
operator limit is asserted.
-/

namespace InfoGeometry.Canonical.ThermalCompactRecurrence

section RingLemmas

variable {R : Type*} [CommRing R]

/--
The inductive addition step for the Cayley/Möbius compactification map.

If `Tn` and `T1` satisfy the cross-multiplied compactified-coordinate equations

`Tn * (1 + qn) = 1 - qn`,
`T1 * (1 + q) = 1 - q`,

then the algebraic addition chart satisfies the corresponding cross-multiplied
relation for `qn * q`:

`(Tn + T1) * (1 + qn*q) = (1 + Tn*T1) * (1 - qn*q)`.
-/
theorem compactified_inductive_step
    (qn q Tn T1 : R)
    (hTn : Tn * (1 + qn) = 1 - qn)
    (hT1 : T1 * (1 + q) = 1 - q) :
    (Tn + T1) * (1 + qn * q) =
      (1 + Tn * T1) * (1 - qn * q) := by
  linear_combination (q * T1 + q) * hTn + (1 - Tn) * hT1

/--
Difference-zero form of `compactified_inductive_step`.
-/
theorem compactified_inductive_step_sub_eq_zero
    (qn q Tn T1 : R)
    (hTn : Tn * (1 + qn) = 1 - qn)
    (hT1 : T1 * (1 + q) = 1 - q) :
    (Tn + T1) * (1 + qn * q)
      - (1 + Tn * T1) * (1 - qn * q) = 0 := by
  rw [compactified_inductive_step qn q Tn T1 hTn hT1]
  ring

/--
The doubled-index compactified coordinate relation is forced up to `2`-torsion.

This is the unconditional ring statement behind the formula

`T₂n = 2*Tn*(1 + Tn^2)⁻¹`.

In rings where multiplication by `2` is cancellative, use
`compactified_doubling_step` below for the exact relation.
-/
theorem compactified_doubling_step_two_torsion
    (qn Tn T2n : R)
    (hTn : Tn * (1 + qn) = 1 - qn)
    (hT2n : T2n * (1 + Tn * Tn) = 2 * Tn) :
    (2 : R) * (T2n * (1 + qn * qn) - (1 - qn * qn)) = 0 := by
  linear_combination
    (-(qn * Tn * T2n - qn * T2n - 2 * qn + Tn * T2n + T2n - 2)) * hTn +
    ((1 + qn) * (1 + qn)) * hT2n

/--
The exact algebraic doubling step for compactified thermal coordinates.

The explicit property `h2Cancel` records the only ring-theoretic cancellation
used: multiplication by `2` has no kernel.  This avoids silently assuming a
field or characteristic-zero domain.
-/
theorem compactified_doubling_step
    (qn Tn T2n : R)
    (h2Cancel : ∀ a : R, (2 : R) * a = 0 → a = 0)
    (hTn : Tn * (1 + qn) = 1 - qn)
    (hT2n : T2n * (1 + Tn * Tn) = 2 * Tn) :
    T2n * (1 + qn * qn) = 1 - qn * qn := by
  have h := compactified_doubling_step_two_torsion qn Tn T2n hTn hT2n
  exact sub_eq_zero.mp (h2Cancel _ h)

/--
Cross-multiplied compactified-coordinate relation.

This is the finite algebraic interface `T * (1 + q) = 1 - q`; it is not a KMS
condition, an operator logarithm identity, or a functional-calculus statement.
-/
def CompactifiedRelation (q T : R) : Prop :=
  T * (1 + q) = 1 - q

/-- Ring homomorphisms preserve the compactified-coordinate relation. -/
theorem map_compactifiedRelation
    {S : Type*} [CommRing S]
    (f : R →+* S) {q T : R}
    (h : CompactifiedRelation q T) :
    CompactifiedRelation (f q) (f T) := by
  simpa [CompactifiedRelation] using congrArg f h

end RingLemmas

section StageTransport

variable {Stage : Nat → Type*} [∀ n : Nat, CommRing (Stage n)]
variable {Limit : Type*} [CommRing Limit]

/--
A compactified-coordinate relation transported along every finite stage of a
one-step ring-hom tower.

The theorem proves only finite-stage algebraic preservation of the
cross-multiplied relation.  No direct-limit object, completion, KMS condition,
or analytic modular flow is asserted.
-/
theorem compactifiedRelation_stage_chain
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (q T : ∀ n : Nat, Stage n)
    (h0 : CompactifiedRelation (q 0) (T 0))
    (hq : ∀ n : Nat, q (n + 1) = bond n (q n))
    (hT : ∀ n : Nat, T (n + 1) = bond n (T n)) :
    ∀ n : Nat, CompactifiedRelation (q n) (T n) := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      rw [hq n, hT n]
      exact map_compactifiedRelation (bond n) ih

/--
Image-local compactified-coordinate relation in an explicit target ring.

Each finite stage is first proved algebraically, then mapped into the target by
`toLimit n`.  This does not assert that `Limit` is a topological completion or
that arbitrary target elements satisfy the relation.
-/
theorem compactifiedRelation_limit_image_chain
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (q T : ∀ n : Nat, Stage n)
    (h0 : CompactifiedRelation (q 0) (T 0))
    (hq : ∀ n : Nat, q (n + 1) = bond n (q n))
    (hT : ∀ n : Nat, T (n + 1) = bond n (T n)) :
    ∀ n : Nat, CompactifiedRelation (toLimit n (q n)) (toLimit n (T n)) := by
  intro n
  exact map_compactifiedRelation (toLimit n)
    (compactifiedRelation_stage_chain bond q T h0 hq hT n)

/--
Compatible-cone readback for transported compactified coordinates.

If the target maps are compatible with the finite tower, then the target images
of the transported `q` and `T` coordinates are stage-independent.
-/
theorem compactifiedRelation_cone_readback
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (hcone : ∀ (n : Nat) (x : Stage n), toLimit (n + 1) (bond n x) = toLimit n x)
    (q T : ∀ n : Nat, Stage n)
    (hq : ∀ n : Nat, q (n + 1) = bond n (q n))
    (hT : ∀ n : Nat, T (n + 1) = bond n (T n)) :
    ∀ n : Nat,
      toLimit n (q n) = toLimit 0 (q 0) ∧
      toLimit n (T n) = toLimit 0 (T 0) := by
  intro n
  induction n with
  | zero =>
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      constructor
      · calc
          toLimit (n + 1) (q (n + 1))
              = toLimit (n + 1) (bond n (q n)) := by rw [hq n]
          _ = toLimit n (q n) := hcone n (q n)
          _ = toLimit 0 (q 0) := ih.1
      · calc
          toLimit (n + 1) (T (n + 1))
              = toLimit (n + 1) (bond n (T n)) := by rw [hT n]
          _ = toLimit n (T n) := hcone n (T n)
          _ = toLimit 0 (T 0) := ih.2

end StageTransport

section NoncommRingLemmas

variable {R : Type*} [Ring R]

/--
Noncommutative inductive addition step for the Cayley/Möbius compactification
map, under explicit local commutation hypotheses.

The ambient ring may be noncommutative.  The hypotheses say only that the four
coordinates appearing in this local modular chart commute in the required
places, as happens inside the commutative subalgebra generated by a single
modular parameter.  No global commutativity, functional calculus, operator
limit, or cone-invariance assertion is used.
-/
theorem compactified_inductive_step_noncomm
    (qn q Tn T1 : R)
    (hqnq : qn * q = q * qn)
    (hTn : Tn * (1 + qn) = 1 - qn)
    (hT1 : T1 * (1 + q) = 1 - q)
    (hTn_q : Tn * q = q * Tn)
    (hT1_qn : T1 * qn = qn * T1)
    (hT_comm : Tn * T1 = T1 * Tn) :
    (Tn + T1) * (1 + qn * q) =
      (1 + Tn * T1) * (1 - qn * q) := by
  have hTn_qn_val : Tn * qn = 1 - qn - Tn := by
    have h : Tn + Tn * qn = 1 - qn := by
      simpa [mul_add, mul_one] using hTn
    exact eq_sub_of_add_eq' h
  have hT1_q_val : T1 * q = 1 - q - T1 := by
    have h : T1 + T1 * q = 1 - q := by
      simpa [mul_add, mul_one] using hT1
    exact eq_sub_of_add_eq' h
  have h1 : Tn * qn * q = (1 - qn - Tn) * q := by
    rw [hTn_qn_val]
  have h2 : T1 * qn * q = qn * (1 - q - T1) := by
    calc
      T1 * qn * q = qn * T1 * q := by
        rw [hT1_qn]
      _ = qn * (T1 * q) := by
        noncomm_ring
      _ = qn * (1 - q - T1) := by
        rw [hT1_q_val]
  have h3 : Tn * T1 * qn * q = (1 - qn - Tn) * (1 - q - T1) := by
    calc
      Tn * T1 * qn * q = (Tn * qn) * (T1 * q) := by
        rw [show Tn * T1 * qn * q = Tn * (T1 * qn) * q by noncomm_ring]
        rw [hT1_qn]
        noncomm_ring
      _ = (1 - qn - Tn) * (1 - q - T1) := by
        rw [hTn_qn_val, hT1_q_val]
  calc
    (Tn + T1) * (1 + qn * q)
        = Tn + T1 + Tn * qn * q + T1 * qn * q := by
          noncomm_ring
    _ = Tn + T1 + (1 - qn - Tn) * q + qn * (1 - q - T1) := by
          rw [h1, h2]
    _ = 1 - qn * q + Tn * T1 - (1 - qn - Tn) * (1 - q - T1) := by
          noncomm_ring [hqnq, hTn_q, hT1_qn, hT_comm]
    _ = 1 - qn * q + Tn * T1 - Tn * T1 * qn * q := by
          rw [← h3]
    _ = (1 + Tn * T1) * (1 - qn * q) := by
          noncomm_ring

end NoncommRingLemmas

/-! ## Plain executable recurrence functions -/

/--
Compose two compactified thermal states represented as pairs `(q, T)`.

The caller supplies the inversion operation explicitly.  This is a plain
function on product types, not a proof-carrying state wrapper.
-/
def compactCompose {R : Type*} [CommRing R]
    (inv : R → R) (s1 s2 : R × R) : R × R :=
  let nextQ := s1.1 * s2.1
  let num := s1.2 + s2.2
  let den := 1 + s1.2 * s2.2
  (nextQ, num * inv den)

/--
Compute the compactified thermal state at a natural scale by binary splitting.

Input `(q1, T1)` is the one-step state.  The result is a pair `(qN, TN)`.
The inversion operation is an explicit parameter; this definition asserts no
analytic or spectral property of that operation.
-/
def computeScale {R : Type*} [CommRing R]
    (inv : R → R) (q1 T1 : R) : Nat → R × R
  | 0 => (1, 0)
  | 1 => (q1, T1)
  | n + 2 =>
      let N := n + 2
      let halfState := computeScale inv q1 T1 (N / 2)
      let evenState := compactCompose inv halfState halfState
      if N % 2 = 0 then
        evenState
      else
        compactCompose inv evenState (q1, T1)
termination_by n => n
decreasing_by omega

/-! ## Newton-Girard trace recurrence step functions -/

/--
One Newton-Girard exterior-algebra step for fermionic partition coefficients.

`A k` is the single-particle trace input, `Z` is the previously computed
coefficient function, and `invNat N` supplies the scalar `1/N`.  The recurrence
is intended for positive `N`; it is left as a plain formula so the scalar
normalization is explicit.
-/
def fermionicNewtonGirardStep {R : Type*} [CommRing R]
    (invNat : Nat → R) (A Z : Nat → R) (N : Nat) : R :=
  let sum := (List.range N).foldl (fun acc i =>
    let k := i + 1
    let sign : R := if k % 2 = 1 then 1 else -1
    acc + sign * A k * Z (N - k)) 0
  invNat N * sum

/--
One Newton-Girard symmetric-algebra step for bosonic partition coefficients.

`A k` is the single-particle trace input, `Z` is the previously computed
coefficient function, and `invNat N` supplies the scalar `1/N`.
-/
def bosonicNewtonGirardStep {R : Type*} [CommRing R]
    (invNat : Nat → R) (A Z : Nat → R) (N : Nat) : R :=
  let sum := (List.range N).foldl (fun acc i =>
    let k := i + 1
    acc + A k * Z (N - k)) 0
  invNat N * sum

end InfoGeometry.Canonical.ThermalCompactRecurrence
