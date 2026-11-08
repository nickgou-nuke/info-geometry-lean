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
import InfoGeometry.Epistemology.RiemannianSubmersion
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Export.LeanOracle

/-!
# Finite Algebraic Identities for Export Reference Contracts

This module contains finite, kernel-checkable identities that can serve as
reference contracts for scientific-computing exports. It proves mask XOR laws,
exterior and Clifford identities, a parity encoding identity for the repository's
Lean export definition, a polynomial cost-model identity, and real error-bound
propagation. These theorems do not certify a Julia implementation, a C ABI
execution, a floating-point backend, or a metric inverse.

The causal order is: the repository-owned finite `BitWord` carrier; mask-only
combinatorics and parity encoding; native exterior/Clifford identities; an
existing submersion projection identity and polynomial cost arithmetic; and a
real-valued triangle inequality. No theorem in this module connects mask
inversion parity to Clifford blade multiplication or to the Cantor hopping code.
-/

namespace InfoGeometry.Export.LeanJuliaVerifiedInterop

open Bool (xor)
open ChakravalaGA
open InfoGeometry.Epistemology.RiemannianSubmersion
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Export.LeanOracle

/-!
## Archetype I: Finite Cantor BitWord Carrier and Mask Combinatorics
-/

/-- The all-false mask on the canonical finite Cantor `BitWord` carrier. -/
def maskZero (n : ℕ) : BitWord n :=
  fun _ => false

/-- Pointwise Boolean XOR of two masks. This is mask algebra only; it omits Clifford signs and metric factors. -/
def maskXor {n : ℕ} (u v : BitWord n) : BitWord n :=
  fun i => xor (u i) (v i)

/-- Hamming weight of a Boolean mask. -/
def maskWeight {n : ℕ} (u : BitWord n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => u i = true)).card

/-- Parity of the Hamming weight of a Boolean mask. -/
def maskParity {n : ℕ} (u : BitWord n) : ChakravalaGA.Parity :=
  if maskWeight u % 2 = 0 then .even else .odd

/-- Pointwise XOR is commutative. -/
theorem maskXor_comm {n : ℕ} (u v : BitWord n) :
    maskXor u v = maskXor v u := by
  funext i
  dsimp [maskXor]
  cases u i <;> cases v i <;> rfl

/-- Pointwise XOR is associative. -/
theorem maskXor_assoc {n : ℕ} (u v w : BitWord n) :
    maskXor (maskXor u v) w = maskXor u (maskXor v w) := by
  funext i
  dsimp [maskXor]
  cases u i <;> cases v i <;> cases w i <;> rfl

/-- A mask XOR itself is the all-false mask. -/
@[simp]
theorem maskXor_self {n : ℕ} (u : BitWord n) :
    maskXor u u = maskZero n := by
  funext i
  dsimp [maskXor, maskZero]
  cases u i <;> rfl

/-- The all-false mask is a left identity for XOR. -/
@[simp]
theorem maskXor_zero_left {n : ℕ} (u : BitWord n) :
    maskXor (maskZero n) u = u := by
  funext i
  dsimp [maskXor, maskZero]
  cases u i <;> rfl

/-- The all-false mask is a right identity for XOR. -/
@[simp]
theorem maskXor_zero_right {n : ℕ} (u : BitWord n) :
    maskXor u (maskZero n) = u := by
  funext i
  dsimp [maskXor, maskZero]
  cases u i <;> rfl

/-- XOR with `u` is an involution. -/
theorem maskXor_involutive_left {n : ℕ} (u v : BitWord n) :
    maskXor u (maskXor u v) = v := by
  funext i
  dsimp [maskXor]
  cases u i <;> cases v i <;> rfl

/-- The Hamming weight of the all-false mask is `0`. -/
@[simp]
theorem maskWeight_zero (n : ℕ) :
    maskWeight (maskZero n) = 0 := by
  simp [maskWeight, maskZero]

/-- The all-false mask has even Hamming-weight parity. -/
@[simp]
theorem maskParity_zero (n : ℕ) :
    maskParity (maskZero n) = .even := by
  simp [maskParity, maskWeight_zero]

/-!
## Archetype II: Mask Inversion Count and Parity Encoding
-/

/-- The finite set of index pairs `(i, j)` with `j < i`, where `u i` and `v j` are both true.
This combinatorial count is not identified here with a Clifford blade-product sign. -/
def maskInversionPairs {n : ℕ} (u v : BitWord n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => decide (p.2 < p.1) && u p.1 && v p.2)

/-- The number of ordered active-bit pairs counted by `maskInversionPairs`. -/
def maskInversionCount {n : ℕ} (u v : BitWord n) : ℕ :=
  (maskInversionPairs u v).card

/-- A sign computed from the parity of `maskInversionCount`; no product-law interpretation is asserted. -/
def maskInversionSign {n : ℕ} (u v : BitWord n) : ℤ :=
  if maskInversionCount u v % 2 = 0 then 1 else -1

/-- The all-false mask on the left produces no inversion pairs. -/
@[simp]
theorem maskInversionPairs_zero_left {n : ℕ} (v : BitWord n) :
    maskInversionPairs (maskZero n) v = ∅ := by
  simp [maskInversionPairs, maskZero]

/-- The all-false mask on the right produces no inversion pairs. -/
@[simp]
theorem maskInversionPairs_zero_right {n : ℕ} (u : BitWord n) :
    maskInversionPairs u (maskZero n) = ∅ := by
  simp [maskInversionPairs, maskZero]

/-- The all-false left mask produces sign `+1`. -/
@[simp]
theorem maskInversionSign_zero_left {n : ℕ} (v : BitWord n) :
    maskInversionSign (maskZero n) v = 1 := by
  simp [maskInversionSign, maskInversionCount, maskInversionPairs_zero_left]

/-- The all-false right mask produces sign `+1`. -/
@[simp]
theorem maskInversionSign_zero_right {n : ℕ} (u : BitWord n) :
    maskInversionSign u (maskZero n) = 1 := by
  simp [maskInversionSign, maskInversionCount, maskInversionPairs_zero_right]

/-- The mask inversion sign is an involution in `ℤ`. -/
theorem maskInversionSign_sq_one {n : ℕ} (u v : BitWord n) :
    maskInversionSign u v * maskInversionSign u v = 1 := by
  dsimp [maskInversionSign]
  split_ifs <;> norm_num

/-- Encoding of `ChakravalaGA.Parity` as `UInt8` (`0` for `.even`, `1` for `.odd`). -/
def parityToUInt8 : ChakravalaGA.Parity → UInt8
  | .even => 0
  | .odd  => 1

/-- The Lean `exportKoszulSign` definition agrees with `koszulSign` on encoded parities.
This theorem does not certify compiled C-ABI or Julia execution. -/
theorem exportKoszulSign_eq_koszulSign (p q : ChakravalaGA.Parity) :
    (InfoGeometry.Export.LeanOracle.exportKoszulSign (parityToUInt8 p) (parityToUInt8 q)).toInt =
      ChakravalaGA.koszulSign (R := ℤ) p q := by
  cases p <;> cases q <;> decide

/-!
## Archetype III: Exterior and Clifford Algebra Identities
-/

/-- Canonical generators of `CliffordAlgebra 0` anticommute. -/
theorem cliffZeroGen_anticomm {R : Type*} [CommRing R] :
    cliffZeroGen₁ (R := R) * cliffZeroGen₂ (R := R) +
      cliffZeroGen₂ (R := R) * cliffZeroGen₁ (R := R) = 0 :=
  ChakravalaGA.cliffZeroGen_anticomm

/-- Repeated exterior multiplication by `v` annihilates any tail `ω`. -/
theorem exterior_mul_generator_twice_eq_zero
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (v : M) (ω : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R v * ω) = 0 := by
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- Exterior generators anticommute in the exterior algebra. -/
theorem exterior_generators_anticommute
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (u v : M) :
    ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v +
      ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u = 0 :=
  ChakravalaGA.mathlib_exteriorAlgebra_anticomm u v

/-- The square of any linear combination of two exterior generators vanishes, by the exterior
algebra relation for the resulting 1-vector. -/
theorem exterior_linear_combination_square_eq_zero
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (u v : M) (a b : R) :
    (a • ExteriorAlgebra.ι R u + b • ExteriorAlgebra.ι R v) *
      (a • ExteriorAlgebra.ι R u + b • ExteriorAlgebra.ι R v) = 0 := by
  have h_lin : a • ExteriorAlgebra.ι R u + b • ExteriorAlgebra.ι R v =
      ExteriorAlgebra.ι R (a • u + b • v) := by
    rw [map_add, map_smul, map_smul]
  rw [h_lin, ExteriorAlgebra.ι_sq_zero]

/-- Orthogonal Clifford generators anticommute when their polarized pairing vanishes. -/
theorem clifford_orthogonal_generators_anticommute
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) (u v : M) (h_ortho : ChakravalaGA.polar Q u v = 0) :
    CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q v +
      CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q u = 0 := by
  rw [ChakravalaGA.mathlib_cliffordAlgebra_anticommutator, h_ortho, map_zero]

/-- The Clifford square of a sum of orthogonal vectors is the scalar sum of their quadratic
values. -/
theorem clifford_square_add_of_orthogonal
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
  rw [h_exp, clifford_orthogonal_generators_anticommute Q u v h_ortho, add_zero,
    CliffordAlgebra.ι_sq_scalar, CliffordAlgebra.ι_sq_scalar, ← map_add]

/-!
## Archetype IV: Horizontal Projection and Polynomial Cost Arithmetic
-/

/-- The vertical projection of a horizontal projection vanishes, by the submersion split. -/
theorem horizontal_projection_vertical_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (split : SubmersionSplit V) (x : V) :
    split.projV (split.projH x) = 0 :=
  split.orthoVH x

/-- A cubic polynomial cost model on a natural-number dimension parameter. -/
def cubicCostModel (d : ℕ) : ℕ :=
  d ^ 3

/-- The cubic cost model is monotone in its dimension parameter. -/
theorem cubicCostModel_mono {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    cubicCostModel d₁ ≤ cubicCostModel d₂ :=
  Nat.pow_le_pow_left h 3

/-- Binomial-cube decomposition in the abstract cubic cost model. -/
theorem cubicCostModel_add_expansion (d_H d_V : ℕ) :
    cubicCostModel d_H + (3 * d_H ^ 2 * d_V + 3 * d_H * d_V ^ 2 + d_V ^ 3) =
      cubicCostModel (d_H + d_V) := by
  dsimp [cubicCostModel]
  ring

/-- The abstract cubic model strictly increases when a positive dimension is added. -/
theorem cubicCostModel_strict_add (d_H d_V : ℕ) (hH : 0 < d_H) (hV : 0 < d_V) :
    cubicCostModel d_H < cubicCostModel (d_H + d_V) := by
  have h_pos : 0 < d_H * d_H * d_V := Nat.mul_pos (Nat.mul_pos hH hH) hV
  have h_id :
      cubicCostModel (d_H + d_V) =
        cubicCostModel d_H + 3 * (d_H * d_H * d_V) + 3 * d_H * d_V ^ 2 + d_V ^ 3 := by
    dsimp [cubicCostModel]
    ring
  omega

/-!
## Archetype V: Real-Valued Error Propagation
-/

/-- The real triangle inequality propagates two stated absolute-error bounds. -/
theorem real_add_error_bound {x₁ x₂ y₁ y₂ ε₁ ε₂ : ℝ}
    (h₁ : |x₁ - y₁| ≤ ε₁) (h₂ : |x₂ - y₂| ≤ ε₂) :
    |(x₁ + x₂) - (y₁ + y₂)| ≤ ε₁ + ε₂ := by
  have h_eq :
      (x₁ + x₂) - (y₁ + y₂) = (x₁ - y₁) + (x₂ - y₂) := by
    ring
  rw [h_eq]
  exact le_trans
    (abs_add_le (x₁ - y₁) (x₂ - y₂))
    (add_le_add h₁ h₂)

/-- The Lean export definition with an `.even` right factor returns `1`. -/
theorem exportKoszulSign_self_even (p : ChakravalaGA.Parity) :
    InfoGeometry.Export.LeanOracle.exportKoszulSign (parityToUInt8 p) (parityToUInt8 .even) = 1 := by
  cases p <;> decide

end InfoGeometry.Export.LeanJuliaVerifiedInterop
