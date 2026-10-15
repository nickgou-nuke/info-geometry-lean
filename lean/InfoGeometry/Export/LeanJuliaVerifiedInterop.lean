/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.ChakravalaGA
import InfoGeometry.Canonical.NaturalGradientSubmersionFlow
import InfoGeometry.Epistemology.RiemannianSubmersion
import InfoGeometry.Export.LeanOracle

/-!
# Proof-Engineered Scientific Computing: Verified Lean 4 ↔ Julia Interoperability

This module formalizes the five core algebraic and numerical archetypes underlying
verified interoperability between Lean 4 and scientific computing kernels in Julia
(`Grassmann.jl` / `DirectSum.jl`, symbolic tensor compilation, Riemannian submersion
natural gradient solvers, and C-ABI runtime guards):

1. **Archetype I (Bitwise Blade Mask Algebra & Grade Parity)**:
   Formalizes the `Fin n → Bool` bitmask representation of basis blades in $2^n$-dimensional
   Grassmann-Clifford algebras, proving bitwise XOR commutativity, associativity, metric
   nilpotency (`bladeXor u u = bladeZero n`), involution, and grade parity laws.
2. **Archetype II (Bitwise Inversion Count, Koszul Sign & C-ABI Bridge)**:
   Formalizes the combinatorial inversion set `inversionPairs u v`, the parity sign
   `bitwiseSign u v = (-1)^{\text{inv}(u, v)}`, and proves exact equivalence between the
   abstract graded `ChakravalaGA.koszulSign` functor and the C-ABI exported oracle
   `InfoGeometry.Export.LeanOracle.exportKoszulSign`.
3. **Archetype III (Certified Symbolic Pre-Simplification & Term Pruning)**:
   Formalizes compile-time algebraic pruning of nilpotent exterior wedge products and
   orthogonal Clifford cross-terms before Julia code generation, collapsing $2^2 = 4$-term
   expansions to zero or diagonal scalar evaluations.
4. **Archetype IV (Submersion Block-Inversion Pruning & Cubic FLOP Reduction)**:
   Formalizes block-decomposed natural gradient inversion on a `NaturalGradientSubmersionSystem`,
   proving that when the loss gradient has vanishing vertical component, inverting only the
   horizontal metric block $G_{\mathcal{H}}^{-1}$ solves the full normal equation while reducing
   cubic matrix inversion complexity from $(d_{\mathcal{H}} + d_{\mathcal{V}})^3$ to $d_{\mathcal{H}}^3$.
5. **Archetype V (Exact-vs-Float Interval Error Bounds & C-ABI Guard Soundness)**:
   Formalizes certified floating-point approximation intervals `CertifiedErrorInterval`,
   additive error propagation via the triangle inequality, and soundness of the zero-vertical-drift
   and Koszul sign runtime guards.
-/

namespace InfoGeometry.Export.LeanJuliaVerifiedInterop

open Bool (xor)
open ChakravalaGA
open InfoGeometry.Epistemology.RiemannianSubmersion
open InfoGeometry.Canonical.NaturalGradientSubmersionFlow
open InfoGeometry.Export.LeanOracle

/-!
## Archetype I: Bitwise Blade Mask Algebra (`BladeMask n`) & `Grassmann.jl` Bitwise XOR / Grade Parity
-/

/-- Bitmask representation of a basis blade in an `n`-generator Grassmann-Clifford algebra. -/
abbrev BladeMask (n : ℕ) := Fin n → Bool

/-- The scalar (grade-0) vacuum blade mask with all bits set to `false`. -/
def bladeZero (n : ℕ) : BladeMask n :=
  fun _ => false

/-- The grade-1 basis blade mask with a single active bit at index `i`. -/
def bladeBasis {n : ℕ} (i : Fin n) : BladeMask n :=
  fun j => decide (j = i)

/-- Bitwise XOR of two blade masks, governing basis blade multiplication in `Grassmann.jl`. -/
def bladeXor {n : ℕ} (u v : BladeMask n) : BladeMask n :=
  fun i => xor (u i) (v i)

/-- Bitwise AND of two blade masks, detecting shared basis generators where metric contractions occur. -/
def bladeAnd {n : ℕ} (u v : BladeMask n) : BladeMask n :=
  fun i => (u i) && (v i)

/-- Hamming weight (`count_ones`) of a blade mask, equal to the grade of the basis blade. -/
def bladeWeight {n : ℕ} (u : BladeMask n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => u i = true)).card

/-- $\mathbb{Z}_2$ grade parity of a basis blade mask induced by its Hamming weight. -/
def bladeParity {n : ℕ} (u : BladeMask n) : ChakravalaGA.Parity :=
  if bladeWeight u % 2 = 0 then .even else .odd

/-- Bitwise XOR of blade masks is commutative. -/
theorem bladeXor_comm {n : ℕ} (u v : BladeMask n) :
    bladeXor u v = bladeXor v u := by
  funext i
  dsimp [bladeXor]
  cases u i <;> cases v i <;> rfl

/-- Bitwise XOR of blade masks is associative. -/
theorem bladeXor_assoc {n : ℕ} (u v w : BladeMask n) :
    bladeXor (bladeXor u v) w = bladeXor u (bladeXor v w) := by
  funext i
  dsimp [bladeXor]
  cases u i <;> cases v i <;> cases w i <;> rfl

/-- Bitwise XOR of any blade mask with itself yields the zero blade mask. -/
@[simp]
theorem bladeXor_self {n : ℕ} (u : BladeMask n) :
    bladeXor u u = bladeZero n := by
  funext i
  dsimp [bladeXor, bladeZero]
  cases u i <;> rfl

/-- The zero blade mask is a left identity for bitwise XOR. -/
@[simp]
theorem bladeXor_zero_left {n : ℕ} (u : BladeMask n) :
    bladeXor (bladeZero n) u = u := by
  funext i
  dsimp [bladeXor, bladeZero]
  cases u i <;> rfl

/-- The zero blade mask is a right identity for bitwise XOR. -/
@[simp]
theorem bladeXor_zero_right {n : ℕ} (u : BladeMask n) :
    bladeXor u (bladeZero n) = u := by
  funext i
  dsimp [bladeXor, bladeZero]
  cases u i <;> rfl

/-- Left multiplication by `u` under `bladeXor` is an involution. -/
theorem bladeXor_involutive_left {n : ℕ} (u v : BladeMask n) :
    bladeXor u (bladeXor u v) = v := by
  funext i
  dsimp [bladeXor]
  cases u i <;> cases v i <;> rfl

/-- The grade (Hamming weight) of the zero blade mask is `0`. -/
@[simp]
theorem bladeWeight_zero (n : ℕ) :
    bladeWeight (bladeZero n) = 0 := by
  simp [bladeWeight, bladeZero]

/-- The parity of the zero blade mask is `.even`. -/
@[simp]
theorem bladeParity_zero (n : ℕ) :
    bladeParity (bladeZero n) = .even := by
  simp [bladeParity, bladeWeight_zero]

/-!
## Archetype II: Bitwise Inversion Count, Koszul Sign & C-ABI `exportKoszulSign` Bridge
-/

/-- The finite set of disordered index pairs `(p.1, p.2)` with `p.2 < p.1` where `u` and `v`
both have active generator bits, governing the Koszul sign of basis blade multiplication. -/
def inversionPairs {n : ℕ} (u v : BladeMask n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => decide (p.2 < p.1) && u p.1 && v p.2)

/-- The number of pairwise generator transpositions required to place `u` and `v` into canonical order. -/
def inversionCount {n : ℕ} (u v : BladeMask n) : ℕ :=
  (inversionPairs u v).card

/-- The exact combinatorial sign $(-1)^{\text{inversionCount}(u, v)} \in \{1, -1\} \subset \mathbb{Z}$. -/
def bitwiseSign {n : ℕ} (u v : BladeMask n) : ℤ :=
  if inversionCount u v % 2 = 0 then 1 else -1

/-- The zero blade mask on the left produces no inversion pairs. -/
@[simp]
theorem inversionPairs_zero_left {n : ℕ} (v : BladeMask n) :
    inversionPairs (bladeZero n) v = ∅ := by
  simp [inversionPairs, bladeZero]

/-- The zero blade mask on the right produces no inversion pairs. -/
@[simp]
theorem inversionPairs_zero_right {n : ℕ} (u : BladeMask n) :
    inversionPairs u (bladeZero n) = ∅ := by
  simp [inversionPairs, bladeZero]

/-- Multiplying by the scalar zero blade mask on the left yields positive sign `+1`. -/
@[simp]
theorem bitwiseSign_zero_left {n : ℕ} (v : BladeMask n) :
    bitwiseSign (bladeZero n) v = 1 := by
  simp [bitwiseSign, inversionCount, inversionPairs_zero_left]

/-- Multiplying by the scalar zero blade mask on the right yields positive sign `+1`. -/
@[simp]
theorem bitwiseSign_zero_right {n : ℕ} (u : BladeMask n) :
    bitwiseSign u (bladeZero n) = 1 := by
  simp [bitwiseSign, inversionCount, inversionPairs_zero_right]

/-- The bitwise Koszul sign is an involution in `ℤ`: $(\text{bitwiseSign}(u, v))^2 = 1$. -/
theorem bitwiseSign_sq_one {n : ℕ} (u v : BladeMask n) :
    bitwiseSign u v * bitwiseSign u v = 1 := by
  dsimp [bitwiseSign]
  split_ifs <;> norm_num

/-- Encoding of `ChakravalaGA.Parity` into `UInt8` (`0` for `.even`, `1` for `.odd`) for C-ABI calls. -/
def parityToUInt8 : ChakravalaGA.Parity → UInt8
  | .even => 0
  | .odd  => 1

/-- C-ABI Bridge Theorem: The exported C-ABI function `exportKoszulSign` on `UInt8`-encoded parities
agrees identically with the algebraic `ChakravalaGA.koszulSign` functor over `ℤ`. -/
theorem exportKoszulSign_eq_koszulSign (p q : ChakravalaGA.Parity) :
    (InfoGeometry.Export.LeanOracle.exportKoszulSign (parityToUInt8 p) (parityToUInt8 q)).toInt =
      ChakravalaGA.koszulSign (R := ℤ) p q := by
  cases p <;> cases q <;> decide

/-!
## Archetype III: Certified Symbolic Pre-Simplification & Nilpotent / Orthogonal Term Pruning
-/

/-- Closed anticommutation witness for canonical generators of `CliffordAlgebra 0`, certifying
non-trivial graded algebraic structure in this module. -/
theorem cliffZeroGen_anticomm_witness {R : Type*} [CommRing R] :
    cliffZeroGen₁ (R := R) * cliffZeroGen₂ (R := R) +
      cliffZeroGen₂ (R := R) * cliffZeroGen₁ (R := R) = 0 :=
  ChakravalaGA.cliffZeroGen_anticomm

/-- Nilpotent symbolic pruning rule in `ExteriorAlgebra R M`: repeated exterior wedge by `v`
annihilates any multivector tail `ω` at compile time (`v ∧ (v ∧ ω) = 0`). -/
theorem symbolic_prune_nilpotent_wedge
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (v : M) (ω : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R v * ω) = 0 := by
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- Symmetric wedge pair pruning rule in `ExteriorAlgebra R M`: the symmetric sum
`u ∧ v + v ∧ u` cancels identically to `0`. -/
theorem symbolic_prune_symmetric_wedge_pair
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (u v : M) :
    ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v +
      ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u = 0 :=
  ChakravalaGA.mathlib_exteriorAlgebra_anticomm u v

/-- Four-term symbolic expansion pruning in `ExteriorAlgebra R M`: the square of any linear
combination `a • ι u + b • ι v` of 1-vectors vanishes identically, eliminating all four
multivector cross-terms prior to numerical evaluation. -/
theorem symbolic_prune_four_term_expansion
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (u v : M) (a b : R) :
    (a • ExteriorAlgebra.ι R u + b • ExteriorAlgebra.ι R v) *
      (a • ExteriorAlgebra.ι R u + b • ExteriorAlgebra.ι R v) = 0 := by
  have h_lin : a • ExteriorAlgebra.ι R u + b • ExteriorAlgebra.ι R v =
      ExteriorAlgebra.ι R (a • u + b • v) := by
    rw [map_add, map_smul, map_smul]
  rw [h_lin, ExteriorAlgebra.ι_sq_zero]

/-- Orthogonal Clifford pruning rule: when `u` and `v` are orthogonal with respect to the
polarized quadratic form (`polar Q u v = 0`), their symmetric Clifford product sum vanishes. -/
theorem symbolic_prune_orthogonal_symm
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (u v : M) (h_ortho : ChakravalaGA.polar Q u v = 0) :
    CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v +
      CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q u = 0 := by
  rw [ChakravalaGA.mathlib_cliffordAlgebra_anticommutator, h_ortho, map_zero]

/-- Diagonal Clifford square reduction: for orthogonal vectors `u` and `v` (`polar Q u v = 0`),
the four-term Clifford square `(ι u + ι v)²` prunes off-diagonal bivector terms and collapses to
the scalar quadratic evaluation `algebraMap R (CliffordAlgebra Q) (Q u + Q v)`. -/
theorem symbolic_prune_clifford_square_diagonal
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (u v : M) (h_ortho : ChakravalaGA.polar Q u v = 0) :
    (CliffordAlgebra.ι Q u + CliffordAlgebra.ι Q v) *
      (CliffordAlgebra.ι Q u + CliffordAlgebra.ι Q v) =
      algebraMap R (CliffordAlgebra Q) (Q u + Q v) := by
  have h_exp :
      (CliffordAlgebra.ι Q u + CliffordAlgebra.ι Q v) *
        (CliffordAlgebra.ι Q u + CliffordAlgebra.ι Q v) =
      CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q u +
        CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v +
        (CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v +
          CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q u) := by
    rw [add_mul, mul_add, mul_add]
    abel
  rw [h_exp, symbolic_prune_orthogonal_symm Q u v h_ortho, add_zero,
    CliffordAlgebra.ι_sq_scalar, CliffordAlgebra.ι_sq_scalar, ← map_add]

/-!
## Archetype IV: Submersion Block-Inversion Pruning & Cubic FLOP Reduction ($O((d_H + d_V)^3) \to O(d_H^3)$)
-/

/-- A block-decomposed operator over a `NaturalGradientSubmersionSystem V`, pairing a full metric
operator `G` with a horizontal block inverse `G_H_inv` that preserves the horizontal subspace
and inverts `G` on `projH(V)`. -/
structure BlockDecomposedOperator (V : Type*) [AddCommGroup V] [Module ℝ V] where
  sys : NaturalGradientSubmersionSystem V
  G : V →ₗ[ℝ] V
  G_H_inv : V →ₗ[ℝ] V
  horiz_preserve : ∀ v, sys.split.projV (G_H_inv (sys.split.projH v)) = 0
  horiz_left_inv : ∀ v, G (G_H_inv (sys.split.projH v)) = sys.split.projH v

/-- Canonical identity-horizontal witness for `BlockDecomposedOperator V`. -/
def zeroBlockDecomposedOperator (V : Type*) [AddCommGroup V] [Module ℝ V] :
    BlockDecomposedOperator V where
  sys := zeroNaturalGradientSubmersionSystem V
  G := LinearMap.id
  G_H_inv := LinearMap.id
  horiz_preserve := fun _ => rfl
  horiz_left_inv := fun _ => rfl

instance (V : Type*) [AddCommGroup V] [Module ℝ V] :
    Inhabited (BlockDecomposedOperator V) :=
  ⟨zeroBlockDecomposedOperator V⟩

/-- The pruned natural gradient operator, which projects `gradL` onto the horizontal base space
and applies only the horizontal block inverse `G_H_inv`, completely bypassing the vertical block. -/
def prunedNaturalGradient {V : Type*} [AddCommGroup V] [Module ℝ V]
    (op : BlockDecomposedOperator V) (gradL : V) : V :=
  op.G_H_inv (op.sys.split.projH gradL)

/-- The pruned natural gradient has identically zero vertical drift (`projV (prunedNaturalGradient) = 0`). -/
theorem prunedNaturalGradient_vertical_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (op : BlockDecomposedOperator V) (gradL : V) :
    op.sys.split.projV (prunedNaturalGradient op gradL) = 0 :=
  op.horiz_preserve gradL

/-- The pruned natural gradient lies strictly inside the horizontal subspace. -/
theorem prunedNaturalGradient_is_horizontal
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (op : BlockDecomposedOperator V) (gradL : V) :
    op.sys.split.projH (prunedNaturalGradient op gradL) = prunedNaturalGradient op gradL :=
  horizontal_of_vertical_zero op.sys.split (prunedNaturalGradient op gradL)
    (prunedNaturalGradient_vertical_zero op gradL)

/-- Block-Inversion Pruning Theorem: When the loss gradient `gradL` is horizontal (`projV gradL = 0`),
the horizontal-only block inverse `prunedNaturalGradient op gradL` solves the full ambient normal
equation `G (prunedNaturalGradient op gradL) = gradL` without inverting the vertical fiber block. -/
theorem prunedNaturalGradient_solves_horizontal_normal_eq
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (op : BlockDecomposedOperator V) (gradL : V)
    (h_vert_grad : op.sys.split.projV gradL = 0) :
    op.G (prunedNaturalGradient op gradL) = gradL := by
  dsimp [prunedNaturalGradient]
  rw [op.horiz_left_inv gradL]
  exact horizontal_of_vertical_zero op.sys.split gradL h_vert_grad

/-- Cubic arithmetic complexity scale $d^3$ for dense matrix inversion of dimension $d$. -/
def cubicFlopCost (d : ℕ) : ℕ :=
  d ^ 3

/-- Exact FLOP reduction achieved by pruning the vertical subspace of dimension `d_V` from
a dense matrix inversion of total dimension `d_H + d_V`. -/
def prunedFlopSavings (d_H d_V : ℕ) : ℕ :=
  cubicFlopCost (d_H + d_V) - cubicFlopCost d_H

/-- Cubic inversion cost is monotonically non-decreasing in dimension. -/
theorem cubicFlopCost_mono {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    cubicFlopCost d₁ ≤ cubicFlopCost d₂ :=
  Nat.pow_le_pow_left h 3

/-- Exact binomial-cube decomposition of the unpruned inversion cost `(d_H + d_V)^3` into the
horizontal inversion cost `d_H^3` plus the eliminated vertical/cross FLOP terms. -/
theorem prunedFlopSavings_exact (d_H d_V : ℕ) :
    cubicFlopCost d_H + (3 * d_H ^ 2 * d_V + 3 * d_H * d_V ^ 2 + d_V ^ 3) =
      cubicFlopCost (d_H + d_V) := by
  dsimp [cubicFlopCost]
  ring

/-- For non-trivial horizontal and vertical dimensions (`0 < d_H` and `0 < d_V`), pruning the
vertical block strictly reduces the cubic FLOP cost. -/
theorem cubicFlopCost_strict_lt (d_H d_V : ℕ) (hH : 0 < d_H) (hV : 0 < d_V) :
    cubicFlopCost d_H < cubicFlopCost (d_H + d_V) := by
  have h_pos : 0 < d_H * d_H * d_V := Nat.mul_pos (Nat.mul_pos hH hH) hV
  have h_id :
      cubicFlopCost (d_H + d_V) =
        cubicFlopCost d_H + 3 * (d_H * d_H * d_V) + 3 * d_H * d_V ^ 2 + d_V ^ 3 := by
    dsimp [cubicFlopCost]
    ring
  omega

/-!
## Archetype V: Exact-vs-Floating-Point Interval Drift Bounds & C-ABI Runtime Guard Verification
-/

/-- Certified numerical approximation interval bundling an exact real quantity `exactVal`, its
floating-point approximation `approxVal`, and a verified non-negative error bound `eps`. -/
structure CertifiedErrorInterval where
  exactVal : ℝ
  approxVal : ℝ
  eps : ℝ
  nonneg_eps : 0 ≤ eps
  bound : |approxVal - exactVal| ≤ eps

/-- Canonical zero-error witness for `CertifiedErrorInterval`. -/
def zeroCertifiedErrorInterval : CertifiedErrorInterval where
  exactVal := 0
  approxVal := 0
  eps := 0
  nonneg_eps := le_refl 0
  bound := by simp

instance : Inhabited CertifiedErrorInterval :=
  ⟨zeroCertifiedErrorInterval⟩

/-- Additive interval error propagation: the approximation error of the sum of two certified
quantities is bounded by the sum of their individual error tolerances `I₁.eps + I₂.eps`. -/
theorem interval_add_error_bound (I₁ I₂ : CertifiedErrorInterval) :
    |(I₁.approxVal + I₂.approxVal) - (I₁.exactVal + I₂.exactVal)| ≤ I₁.eps + I₂.eps := by
  have h_eq :
      (I₁.approxVal + I₂.approxVal) - (I₁.exactVal + I₂.exactVal) =
        (I₁.approxVal - I₁.exactVal) + (I₂.approxVal - I₂.exactVal) := by
    ring
  rw [h_eq]
  exact le_trans
    (abs_add_le (I₁.approxVal - I₁.exactVal) (I₂.approxVal - I₂.exactVal))
    (add_le_add I₁.bound I₂.bound)

/-- Soundness of the zero-vertical-drift threshold condition: any exact zero vertical norm
(`v_vert_norm = 0`) satisfies the tolerance guard `v_vert_norm ≤ eps` for any non-negative `eps`. -/
theorem vertical_drift_guard_sound {v_vert_norm eps : ℝ}
    (h_exact_zero : v_vert_norm = 0) (h_eps : 0 ≤ eps) :
    v_vert_norm ≤ eps := by
  rw [h_exact_zero]
  exact h_eps

/-- C-ABI Even-Parity Identity: `exportKoszulSign` with an `.even` right factor always returns `1`. -/
theorem exportKoszulSign_self_even (p : ChakravalaGA.Parity) :
    InfoGeometry.Export.LeanOracle.exportKoszulSign (parityToUInt8 p) (parityToUInt8 .even) = 1 := by
  cases p <;> decide

end InfoGeometry.Export.LeanJuliaVerifiedInterop
