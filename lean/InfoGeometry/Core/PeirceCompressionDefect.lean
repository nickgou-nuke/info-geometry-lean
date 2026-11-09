/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Core.IdempotencyDefect
import InfoGeometry.Core.PeirceDecomposition

/-!
# Multiplication defects of an idempotent compression

These are associative-ring identities. Star-square factorization supplies
self-adjointness, but no ordered positivity or diffraction interpretation is
asserted. The input operators need not be idempotent.
-/
namespace InfoGeometry.Core.PeirceCompressionDefect

open IdempotencyDefect

variable {A : Type*} [Ring A]

/-- The exact failure of compression to preserve multiplication. -/
theorem compression_mul_defect (p x y : A) (hp : p * p = p) :
    p * (x * y) * p - (p * x * p) * (p * y * p) =
      p * x * (1 - p) * y * p := by
  have hmiddle : (p * x * p) * (p * y * p) = p * x * p * y * p := by
    calc
      _ = p * x * (p * p) * y * p := by simp only [mul_assoc]
      _ = _ := by rw [hp]
  rw [hmiddle]
  noncomm_ring

/-- The complementary transfer product is the square-compression defect. -/
theorem compression_square_defect (p x : A) (hp : p * p = p) :
    p * (x * x) * p - (p * x * p) * (p * x * p) =
      (p * x * (1 - p)) * ((1 - p) * x * p) := by
  rw [compression_mul_defect p x x hp]
  have hc : (1 - p) * (1 - p) = 1 - p := by noncomm_ring [hp]
  calc
    _ = p * x * ((1 - p) * (1 - p)) * x * p := by rw [hc]
    _ = _ := by simp only [mul_assoc]

/-! ## Defect transport through nested compression -/

/-- The compressed idempotency defect is the ambient defect compressed to the
corner, minus the transfer through its complementary corner. -/
theorem defect_compression (p x : A) (hp : p * p = p) :
    defect (p * x * p) =
      p * defect x * p - p * x * (1 - p) * x * p := by
  rw [← compression_mul_defect p x x hp]
  unfold defect
  noncomm_ring

/-- The idempotency defect of a compressed operator is exactly the ordered
product of its two off-diagonal Peirce blocks, subtracted from the compressed
ambient defect.  This identifies the correction term in `defect_compression`
as transfer from the `p` corner to its complement and back; no commutation
between `p` and `x` is assumed. -/
theorem defect_compression_peirce_transfer (p x : A) (hp : p * p = p) :
    defect (p * x * p) =
      p * defect x * p -
        (InfoGeometry.Core.PeirceDecomposition.component10 p x) *
          (InfoGeometry.Core.PeirceDecomposition.component01 p x) := by
  have hTransfer :
      (InfoGeometry.Core.PeirceDecomposition.component10 p x) *
          (InfoGeometry.Core.PeirceDecomposition.component01 p x) =
        p * x * (1 - p) * x * p := by
    have hcomp : (1 - p) * (1 - p) = 1 - p := by
      noncomm_ring [hp]
    dsimp [InfoGeometry.Core.PeirceDecomposition.component10,
      InfoGeometry.Core.PeirceDecomposition.component01,
      InfoGeometry.Core.PeirceDecomposition.complementIdempotent]
    calc
      p * x * (1 - p) * ((1 - p) * x * p) =
          p * x * ((1 - p) * (1 - p)) * x * p := by noncomm_ring
      _ = p * x * (1 - p) * x * p := by rw [hcomp]
  rw [defect_compression p x hp, hTransfer]

/-- For compatible nested idempotents, the relative shell `p - q` gives the
exact correction to the defect of compressing first by `p` and then by `q`. -/
theorem defect_nested_compression (p q x : A)
    (hp : p * p = p) (hq : q * q = q)
    (hqp : q * p = q) (hpq : p * q = q) :
    defect (q * x * q) =
      q * defect (p * x * p) * q - q * x * (p - q) * x * q := by
  have hcompress : q * (p * x * p) * q = q * x * q := by
    calc
      _ = (q * p) * x * (p * q) := by simp only [mul_assoc]
      _ = _ := by rw [hqp, hpq]
  have hrelative : p * (1 - q) * p = p - q := by
    calc
      _ = p * p - (p * q) * p := by noncomm_ring
      _ = _ := by rw [hp, hpq, hqp]
  have htransfer :
      q * (p * x * p) * (1 - q) * (p * x * p) * q =
        q * x * (p - q) * x * q := by
    calc
      _ = (q * p) * x * (p * (1 - q) * p) * x * (p * q) := by
        simp only [mul_assoc]
      _ = _ := by rw [hqp, hpq, hrelative]
  have h := defect_compression q (p * x * p) hq
  rw [hcompress, htransfer] at h
  exact h

/-- A finite descending compatible flag accumulates the exact ordered
relative-shell corrections; this is a finite algebraic identity. -/
theorem defect_compression_flag (p : ℕ → A) (x : A) (n : ℕ)
    (hp : ∀ i ≤ n, p i * p i = p i)
    (hleft : ∀ i < n, p (i + 1) * p i = p (i + 1))
    (hright : ∀ i < n, p i * p (i + 1) = p (i + 1)) :
    defect (p n * x * p n) =
      p n * defect (p 0 * x * p 0) * p n -
        ∑ i ∈ Finset.range n, p n * x * (p i - p (i + 1)) * x * p n := by
  have hbase : ∀ k ≤ n, p k * p 0 = p k ∧ p 0 * p k = p k := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact ⟨hp 0 hk, hp 0 hk⟩
    | succ k ih =>
        intro hk
        have hkn : k ≤ n := (Nat.le_succ k).trans hk
        have hklt : k < n := (Nat.lt_succ_self k).trans_le hk
        rcases ih hkn with ⟨hkl, hkr⟩
        constructor
        · calc
            p (k + 1) * p 0 = (p (k + 1) * p k) * p 0 := by
              rw [hleft k hklt]
            _ = p (k + 1) * (p k * p 0) := mul_assoc _ _ _
            _ = p (k + 1) := by rw [hkl, hleft k hklt]
        · calc
            p 0 * p (k + 1) = p 0 * (p k * p (k + 1)) := by
              rw [hright k hklt]
            _ = (p 0 * p k) * p (k + 1) := (mul_assoc _ _ _).symm
            _ = p (k + 1) := by rw [hkr, hright k hklt]
  have hshells : ∀ k : ℕ,
      (∑ i ∈ Finset.range k, (p i - p (i + 1))) = p 0 - p k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        noncomm_ring
  have hsum :
      (∑ i ∈ Finset.range n, p n * x * (p i - p (i + 1)) * x * p n) =
        p n * x * (p 0 - p n) * x * p n := by
    calc
      _ = (p n * x) * (∑ i ∈ Finset.range n, (p i - p (i + 1))) *
          x * p n := by simp only [Finset.mul_sum, Finset.sum_mul]
      _ = _ := by rw [hshells]
  rw [hsum]
  exact defect_nested_compression (p 0) (p n) x
    (hp 0 (Nat.zero_le n)) (hp n le_rfl) (hbase n le_rfl).1 (hbase n le_rfl).2

/-! ## The universal defect of a pair of idempotents -/

/-- **Two-idempotent chordal defect identity.** For idempotents `p₁,p₂` in an
associative ring, the square `Δ = (p₂ - p₁)²` commutes with both endpoints,
the two return sandwiches are `pᵢ (1 - Δ)`, and the negative square of their
commutator is `Δ (1 - Δ)`. These are ring identities; no scalar angle,
positivity, or probability interpretation is assumed. -/
theorem twoIdempotentChordalDefect
    (p₁ p₂ : A) (hp₁ : p₁ * p₁ = p₁) (hp₂ : p₂ * p₂ = p₂) :
    let Δ := (p₂ - p₁) * (p₂ - p₁)
    let C := p₂ * p₁ - p₁ * p₂
    Δ * p₁ = p₁ * Δ ∧
    Δ * p₂ = p₂ * Δ ∧
    p₁ * p₂ * p₁ = p₁ * (1 - Δ) ∧
    p₂ * p₁ * p₂ = p₂ * (1 - Δ) ∧
    -(C * C) = Δ * (1 - Δ) := by
  intro Δ C
  dsimp [Δ, C]
  have hL₁ : ∀ z : A, p₁ * (p₁ * z) = p₁ * z := by
    intro z
    rw [← mul_assoc, hp₁]
  have hR₁ : ∀ z : A, (z * p₁) * p₁ = z * p₁ := by
    intro z
    rw [mul_assoc, hp₁]
  have hRp₁ : ∀ z : A, z * (p₁ * p₁) = z * p₁ := by
    intro z
    rw [hp₁]
  have hL₂ : ∀ z : A, p₂ * (p₂ * z) = p₂ * z := by
    intro z
    rw [← mul_assoc, hp₂]
  have hR₂ : ∀ z : A, (z * p₂) * p₂ = z * p₂ := by
    intro z
    rw [mul_assoc, hp₂]
  have hRp₂ : ∀ z : A, z * (p₂ * p₂) = z * p₂ := by
    intro z
    rw [hp₂]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · noncomm_ring [hL₁, hR₁, hRp₁, hL₂, hR₂, hRp₂]
  · noncomm_ring [hL₁, hR₁, hRp₁, hL₂, hR₂, hRp₂]
  · noncomm_ring [hL₁, hR₁, hRp₁, hL₂, hR₂, hRp₂]
    rw [hp₁]
    abel
  · noncomm_ring [hL₁, hR₁, hRp₁, hL₂, hR₂, hRp₂]
    rw [hp₂]
    abel
  · noncomm_ring [hL₁, hR₁, hRp₁, hL₂, hR₂, hRp₂]

/-- **Davis decomposition for two idempotents.** For idempotents `p₁,p₂`,
the difference `d = p₂ - p₁` and the centered sum
`s = p₁ + p₂ - 1` anticommute and have complementary squares. Their ordered
product is the commutator `p₂p₁ - p₁p₂`; the displayed corner identities are
the corresponding intertwining relations. This is a polynomial identity in an
associative ring, with no self-adjointness or positivity assumptions. -/
theorem twoIdempotentDavisDecomposition
    (p₁ p₂ : A) (hp₁ : p₁ * p₁ = p₁) (hp₂ : p₂ * p₂ = p₂) :
    let d := p₂ - p₁
    let s := p₁ + p₂ - 1
    let c := p₂ * p₁ - p₁ * p₂
    d * s = c ∧
    s * d = -c ∧
    d * s + s * d = 0 ∧
    d * s - s * d = c + c ∧
    d * d + s * s = 1 ∧
    p₁ * s = p₁ * p₂ ∧
    s * p₂ = p₁ * p₂ ∧
    d * p₁ = (1 - p₂) * d ∧
    p₁ * p₂ * p₁ = p₁ * (s * s) ∧
    -(c * c) = (d * d) * (s * s) := by
  intro d s c
  dsimp [d, s, c]
  have hL₁ : ∀ z : A, p₁ * (p₁ * z) = p₁ * z := by
    intro z
    rw [← mul_assoc, hp₁]
  have hL₂ : ∀ z : A, p₂ * (p₂ * z) = p₂ * z := by
    intro z
    rw [← mul_assoc, hp₂]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [mul_add, add_mul, sub_mul, mul_sub, mul_one, one_mul,
      neg_sub, mul_assoc, hp₁, hp₂, hL₁, hL₂]
    abel

/-- The product of the two Cartan involutions associated with idempotents is
the algebraic double-angle decomposition. Here `d = p - q`, so the sine
channel is `p*q - q*p`; the formula uses no scalar half-angle normalization. -/
theorem idempotentCartanProduct_doubleAngle
    (p q : A) (hp : p * p = p) (hq : q * q = q) :
    let d := p - q
    let c := p * q - q * p
    (p + p - 1) * (q + q - 1) =
        (1 - (d * d + d * d)) + (c + c) ∧
    ((p + p - 1) * (q + q - 1) + (q + q - 1) * (p + p - 1)) =
        (1 - (d * d + d * d)) + (1 - (d * d + d * d)) ∧
    ((p + p - 1) * (q + q - 1) - (q + q - 1) * (p + p - 1)) =
        c + c + c + c := by
  intro d c
  dsimp [d, c]
  constructor
  · noncomm_ring [hp, hq]
  constructor
  · noncomm_ring [hp, hq]
  · noncomm_ring [hp, hq]

/-! ## Three-idempotent reflection identities

The statements below stay in an arbitrary associative ring. “Bargmann” and
“Nambu” are names for the ordered products and alternating sum defined here;
no state space, trace, topology, or geometric phase is part of these types.
-/

/-- The centered sum of two idempotents. -/
def davisReflection (p q : A) : A := p + q - 1

/-- The three-step ordered product of centered idempotent sums. -/
def threeReflectionLoop (p q r : A) : A :=
  davisReflection p q * davisReflection q r * davisReflection r p

/-- The alternating associative three-variable commutator. -/
def alternatingTriple (x y z : A) : A :=
  (x * y * z + y * z * x + z * x * y) -
    (x * z * y + y * x * z + z * y * x)

/-- Two adjacent centered sums split into the ordered path and its complementary
path. Only the shared middle element must be idempotent; the endpoints are
arbitrary ring elements. -/
theorem adjacentDavisReflections_split
    (p q r : A) (hq : q * q = q) :
    davisReflection p q * davisReflection q r =
      p * q * r + (1 - p) * (1 - q) * (1 - r) := by
  unfold davisReflection
  noncomm_ring [hq]

/-- The ordered three-reflection loop separates into a `p` corner and a
complementary corner. The negative sign is due to the three complementary
factors. -/
theorem threeDavisReflections_corner_split
    (p q r : A) (hp : p * p = p) (hq : q * q = q) (hr : r * r = r) :
    threeReflectionLoop p q r =
      p * q * r * p - (1 - p) * (1 - q) * (1 - r) * (1 - p) := by
  unfold threeReflectionLoop davisReflection
  noncomm_ring [hp, hq, hr]

/-- Reversing the two internal vertices leaves the difference of the two
three-reflection loops equal to the commutator in the two orthogonal corners. -/
theorem threeDavisReflections_orientation
    (p q r : A) (hp : p * p = p) (hq : q * q = q) (hr : r * r = r) :
    threeReflectionLoop p q r - threeReflectionLoop p r q =
      p * (q * r - r * q) * p -
        (1 - p) * (q * r - r * q) * (1 - p) := by
  unfold threeReflectionLoop davisReflection
  noncomm_ring [hp, hq, hr]

/-- The cyclic sum of orientation differences is the alternating triple
commutator doubled, minus the boundary commutator sum. -/
theorem threeDavisReflections_cyclic_alternating_identity
    (p q r : A) (hp : p * p = p) (hq : q * q = q) (hr : r * r = r) :
    (threeReflectionLoop p q r - threeReflectionLoop p r q) +
      (threeReflectionLoop q r p - threeReflectionLoop q p r) +
      (threeReflectionLoop r p q - threeReflectionLoop r q p) +
      ((p * q - q * p) + (q * r - r * q) + (r * p - p * r)) =
      alternatingTriple p q r + alternatingTriple p q r := by
  unfold threeReflectionLoop davisReflection alternatingTriple
  noncomm_ring [hp, hq, hr]

/-! ## Two-boundary compression and its intermediate-corner decomposition -/

/-- Compression between distinct initial and final idempotent boundaries.
The multiplication order is final boundary, observable, initial boundary. -/
def twoBoundaryCompression (final observable initial : A) : A :=
  final * observable * initial

/-- The final boundary absorbs a two-boundary compression on the left. -/
theorem twoBoundaryCompression_left_absorption
    (final observable initial : A)
    (hfinal : final * final = final) :
    final * twoBoundaryCompression final observable initial =
      twoBoundaryCompression final observable initial := by
  unfold twoBoundaryCompression
  calc
    final * (final * observable * initial) =
        (final * final) * observable * initial := by simp only [mul_assoc]
    _ = final * observable * initial := by rw [hfinal]

/-- The initial boundary absorbs a two-boundary compression on the right. -/
theorem twoBoundaryCompression_right_absorption
    (final observable initial : A)
    (hinitial : initial * initial = initial) :
    twoBoundaryCompression final observable initial * initial =
      twoBoundaryCompression final observable initial := by
  unfold twoBoundaryCompression
  calc
    (final * observable * initial) * initial =
        final * observable * (initial * initial) := by simp only [mul_assoc]
    _ = final * observable * initial := by rw [hinitial]

/-- Reapplying the same idempotent boundary compression has no further effect.
This is the operator-level idempotency law for the compression map. -/
theorem twoBoundaryCompression_idempotent
    (p x : A) (hp : p * p = p) :
    twoBoundaryCompression p (twoBoundaryCompression p x p) p =
      twoBoundaryCompression p x p := by
  unfold twoBoundaryCompression
  calc
    p * (p * x * p) * p = (p * p) * x * (p * p) := by
      simp only [mul_assoc]
    _ = p * x * p := by rw [hp]

/-- The sum of two idempotent boundary observables doubles the transition
corner, without requiring the two idempotents to commute. -/
theorem twoBoundaryCompression_sum_amplification
    (initial final : A)
    (hinitial : initial * initial = initial)
    (hfinal : final * final = final) :
    twoBoundaryCompression final (initial + final) initial =
      final * initial + final * initial := by
  unfold twoBoundaryCompression
  have hinitial_absorb : (final * initial) * initial = final * initial := by
    calc
      (final * initial) * initial = final * (initial * initial) := by
        rw [mul_assoc]
      _ = final * initial := by rw [hinitial]
  have hfinal_absorb : (final * final) * initial = final * initial := by
    rw [hfinal]
  calc
    final * (initial + final) * initial =
        final * initial * initial + final * final * initial := by
          simp only [mul_add, add_mul, mul_assoc]
    _ = final * initial + final * initial := by
      rw [hinitial_absorb, hfinal_absorb]

/-- Resolving an intermediate idempotent into itself and its complement splits
the two-boundary product into its through-corner and complementary channels. -/
theorem twoBoundaryCompression_intermediate_decomposition
    (final x y initial middle : A)
    (hmiddle : middle * middle = middle) :
    twoBoundaryCompression final (x * y) initial =
      twoBoundaryCompression final x middle *
          twoBoundaryCompression middle y initial +
        (final * x * (1 - middle)) * ((1 - middle) * y * initial) := by
  unfold twoBoundaryCompression
  let complement := 1 - middle
  have hcomplement : complement * complement = complement := by
    dsimp [complement]
    noncomm_ring [hmiddle]
  have hsplit : middle + complement = 1 := by
    dsimp [complement]
    abel
  have hthrough :
      (final * x * middle) * (middle * y * initial) =
        (final * x * middle) * (y * initial) := by
    calc
      (final * x * middle) * (middle * y * initial) =
          ((final * x * middle) * middle) * (y * initial) := by
            simp only [mul_assoc]
      _ = ((final * x) * (middle * middle)) * (y * initial) := by
            simp only [mul_assoc]
      _ = (final * x * middle) * (y * initial) := by rw [hmiddle]
  have hout :
      (final * x * complement) * (complement * y * initial) =
        (final * x * complement) * (y * initial) := by
    calc
      (final * x * complement) * (complement * y * initial) =
          ((final * x * complement) * complement) * (y * initial) := by
            simp only [mul_assoc]
      _ = ((final * x) * (complement * complement)) * (y * initial) := by
            simp only [mul_assoc]
      _ = (final * x * complement) * (y * initial) := by rw [hcomplement]
  calc
    final * (x * y) * initial = (final * x) * (y * initial) := by
      simp only [mul_assoc]
    _ = (final * x) * (middle + complement) * (y * initial) := by
      rw [hsplit, mul_one]
    _ = (final * x * middle) * (y * initial) +
        (final * x * complement) * (y * initial) := by
      noncomm_ring
    _ = (final * x * middle) * (middle * y * initial) +
        (final * x * complement) * (complement * y * initial) := by
      rw [← hthrough, ← hout]

/-- Correct square expansion for the two-idempotent sandwich. The cross terms
give three copies of the transition corner and one square of that corner. -/
theorem twoBoundaryCompression_sum_square
    (initial final : A)
    (hinitial : initial * initial = initial)
    (hfinal : final * final = final) :
    twoBoundaryCompression final ((initial + final) * (initial + final)) initial =
      3 • (final * initial) + (final * initial) * (final * initial) := by
  unfold twoBoundaryCompression
  have hfinal_left : final * (final * initial) = final * initial := by
    calc
      final * (final * initial) = (final * final) * initial := by
        rw [mul_assoc]
      _ = final * initial := by rw [hfinal]
  calc
    final * ((initial + final) * (initial + final)) * initial =
        2 • (final * initial) +
          (final * (final * initial) +
            final * (initial * (final * initial))) := by
              noncomm_ring [hinitial, hfinal]
    _ = 3 • (final * initial) +
          (final * initial) * (final * initial) := by
      rw [hfinal_left]
      simp only [two_nsmul, three_nsmul, mul_assoc]
      abel

/-- Resolving the complement into idempotents resolves the defect into products.
Pairwise orthogonality is not needed for this identity once the sum is given. -/
theorem compression_defect_sum {I : Type*} [Fintype I]
    (p x y : A) (s : I → A) (hp : p * p = p)
    (hs : ∑ i, s i = 1 - p) (hi : ∀ i, s i * s i = s i) :
    p * (x * y) * p - (p * x * p) * (p * y * p) =
      ∑ i, (p * x * s i) * (s i * y * p) := by
  rw [compression_mul_defect p x y hp, ← hs]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = p * x * (s i * s i) * y * p := by rw [hi i]
    _ = _ := by simp only [mul_assoc]

section Star
variable [StarRing A]

/-- Polarized compression defect: arbitrary inputs give the mixed star product
of their complementary transfer corners. No self-adjointness of either input
or positivity structure on the ring is required. -/
theorem compression_adjoint_mul_defect (p x y : A) (hp : p * p = p)
    (hps : star p = p) :
    p * (star x * y) * p - (p * star x * p) * (p * y * p) =
      star ((1 - p) * x * p) * ((1 - p) * y * p) := by
  rw [compression_mul_defect p (star x) y hp]
  have hc : (1 - p) * (1 - p) = 1 - p := by noncomm_ring [hp]
  simp only [star_mul, star_sub, star_one, hps]
  calc
    _ = p * star x * ((1 - p) * (1 - p)) * y * p := by rw [hc]
    _ = _ := by simp only [mul_assoc]

/-- For a proper involution, equality in the compressed star-square identity
is exactly the absence of transfer from the compressed corner to its complement.
Properness is essential; a general star ring need not detect zero by star-squares. -/
theorem compression_adjoint_square_eq_iff_transfer_zero
    (hproper : ∀ z : A, star z * z = 0 → z = 0)
    (p x : A) (hp : p * p = p) (hps : star p = p) :
    p * (star x * x) * p = (p * star x * p) * (p * x * p) ↔
      (1 - p) * x * p = 0 := by
  rw [← sub_eq_zero, compression_adjoint_mul_defect p x x hp hps]
  constructor
  · exact hproper _
  · intro hz
    rw [hz, star_zero, mul_zero]

/-- For self-adjoint inputs and projections, one vanishing transfer corner
already forces the opposite corner to vanish, hence commutation. -/
theorem selfAdjoint_transfer_zero_iff_commute (p x : A) (hp : p * p = p)
    (hps : star p = p) (hxs : star x = x) :
    (1 - p) * x * p = 0 ↔ p * x = x * p := by
  constructor
  · intro hz
    have hxp : x * p = p * x * p := by
      rw [sub_mul, one_mul, sub_mul] at hz
      exact sub_eq_zero.mp hz
    have hpx : p * x = p * x * p := by
      simpa only [star_mul, hps, hxs, mul_assoc] using congrArg star hxp
    exact hpx.trans hxp.symm
  · intro hc
    rw [mul_assoc, ← hc, ← mul_assoc, sub_mul, one_mul, hp, sub_self, zero_mul]

/-- In a proper star ring, self-adjoint square compression is multiplicative
exactly on inputs commuting with the projection. This is a single-input
criterion, not a claim that compression preserves arbitrary products. -/
theorem compression_square_eq_iff_commute
    (hproper : ∀ z : A, star z * z = 0 → z = 0)
    (p x : A) (hp : p * p = p) (hps : star p = p) (hxs : star x = x) :
    p * (x * x) * p = (p * x * p) * (p * x * p) ↔ p * x = x * p := by
  have h := compression_adjoint_square_eq_iff_transfer_zero hproper p x hp hps
  rw [hxs] at h
  exact h.trans (selfAdjoint_transfer_zero_iff_commute p x hp hps hxs)

/-- The adjoint reverses the two inputs of the polarized defect. -/
theorem compression_adjoint_mul_defect_star (p x y : A) (hp : p * p = p)
    (hps : star p = p) :
    star (p * (star x * y) * p - (p * star x * p) * (p * y * p)) =
      p * (star y * x) * p - (p * star y * p) * (p * x * p) := by
  rw [compression_adjoint_mul_defect p x y hp hps,
    compression_adjoint_mul_defect p y x hp hps, star_mul, star_star]

/-- Self-adjoint compression and input give a literal star-square factorization. -/
theorem compression_square_defect_star (p x : A) (hp : p * p = p)
    (hps : star p = p) (hxs : star x = x) :
    p * (x * x) * p - (p * x * p) * (p * x * p) =
      (p * x * (1 - p)) * star (p * x * (1 - p)) := by
  rw [compression_square_defect p x hp]
  simp only [star_mul, star_sub, star_one, hps, hxs, mul_assoc]

/-- Self-adjointness is available without an order on the ring. -/
theorem compression_square_defect_selfAdjoint (p x : A) (hp : p * p = p)
    (hps : star p = p) (hxs : star x = x) :
    star (p * (x * x) * p - (p * x * p) * (p * x * p)) =
      p * (x * x) * p - (p * x * p) * (p * x * p) := by
  rw [compression_square_defect_star p x hp hps hxs, star_mul, star_star]

end Star
end InfoGeometry.Core.PeirceCompressionDefect
