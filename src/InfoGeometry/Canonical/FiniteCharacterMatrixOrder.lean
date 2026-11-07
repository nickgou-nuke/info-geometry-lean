/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
--/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import InfoGeometry.Algebra.F4Derivations
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-!
# Finite Fourier and matrix-order archetypes

This owner records a finite algebraic bridge motivated by the distinction
between scalar characters and matrix-valued representations. It proves scalar
character blindness to commutators, a conditional Chebyshev `T₂` identity,
faithfulness of one explicit `S3Perm` representation in `Mat₂(ℤ)`, and a
four-trace identity.

The finite group-ring convolution theorem remains in
`InfoGeometry.Algebra.NoncommutativePlaneWaveKernel`; this owner does not wrap it.
It also packages a homomorphism from the repository's six-element `S3Perm`
group into `Mat₂(ℤ)`, proves its Schur commutant law (`s3MatrixRep_commutant_iff_scalar`),
Burnside `3 • M` spanning identity (`three_smul_matrix_in_s3_span`), regular character
orthogonality (`s3_regular_character_orthogonality`), and uniqueness of four-trace
reconstruction under `2`-regularity (`four_traces_unique_of_two_mul_injective`). The two
simple-reflection matrices are also explicitly decomposed into the standard Peirce grading
and one off-diagonal corner each (`s3_reflections_as_peirce_corner_combinations`).

## i. Overview

The carrier is a commutative coefficient ring for scalar identities and the
concrete integer ring for the two matrix witnesses. The matrices are `2 × 2`
over `ℤ`; the trace reconstruction statement is over an arbitrary commutative
ring and recovers `2 • M` (uniquely when multiplication by `2` is injective).

## ii. Key results

The declarations prove scalar commutator blindness, conditional `T₂`, explicit
noncommutation, faithfulness, scalar-only commutant, `3 • M` spanning, and regular
character orthogonality of the concrete `S3Perm` representation, together with the
four-trace identity and uniqueness. `s3_reflections_as_peirce_corner_combinations` identifies
the two generating matrices with explicit Peirce-corner expressions in the same matrix carrier.

## iii. Table of contents

1. Scalar character identity.
2. Conditional Chebyshev identity.
3. Concrete matrix-order witness and an `S3Perm` matrix homomorphism.
4. Four-trace reconstruction identity, uniqueness, Schur commutant, Burnside span,
   and regular character orthogonality.

## iv. References

The finite group-ring convolution transform is owned by
`InfoGeometry.Algebra.NoncommutativePlaneWaveKernel`. The broader motivation is
Karkada et al., *Symmetry in language statistics shapes the geometry of model
representations*, arXiv:2602.15029.

### Three-Bucket Audit Map
* **BUCKET 1 (Keep / Proved Kernel Content):**
  `scalar_character_blind_to_commutators`, `chebyshev_T2_identity`,
  `reflection_generators_are_involutions_and_do_not_commute`, `s3MatrixRep`,
  `s3MatrixRep_preserves_transposition_order`, `s3MatrixRep_injective`,
  `two_mul_matrix_from_four_traces`, `four_traces_unique_of_two_mul_injective`,
  `s3MatrixRep_commutant_iff_scalar`, `three_smul_matrix_in_s3_span`,
  `peirceGradingS_anticomm_peirceSwapPhi`, `s3_reflections_as_peirce_corner_combinations`,
  `s3_regular_character_orthogonality`.
* **BUCKET 2 (Delete / Rejected Surrogates):**
  Zero duplicate wrappers around `NoncommutativePlaneWaveKernel`.
* **BUCKET 3 (Conditional / Open Context):**
  Four-trace uniqueness requires `Function.Injective (fun x : K => 2 * x)`; continuous
  compact Lie group Peter–Weyl completeness remains external context.
-/

namespace InfoGeometry.Canonical.FiniteCharacterMatrixOrder

open scoped Matrix BigOperators

/-- A multiplicative scalar-valued character into a commutative ring identifies
the two orders of every product. -/
lemma scalar_character_blind_to_commutators
    {G K : Type*} [Mul G] [CommRing K]
    (χ : G → K) (hχ : ∀ x y : G, χ (x * y) = χ x * χ y) (x y : G) :
    χ (x * y) - χ (y * x) = 0 := by
  rw [hχ x y, hχ y x, mul_comm, sub_self]

/-- The second Chebyshev polynomial identity under the unit-circle relation. -/
lemma chebyshev_T2_identity {K : Type*} [CommRing K] (c s : K)
    (h : c * c + s * s = 1) :
    c * c - s * s = 2 * (c * c) - 1 := by
  calc
    c * c - s * s = 2 * (c * c) - (c * c + s * s) := by ring
    _ = 2 * (c * c) - 1 := by rw [h]

/-! The following concrete matrices witness noncommuting order in dimension two
and are then assembled into a homomorphism from the repository's finite `S3Perm`. -/

/-- First integer root-reflection generator `!![-1, 1; 0, 1]`. -/
def reflectionA : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 1; 0, 1]

/-- Second integer root-reflection generator `!![1, 0; 1, -1]`. -/
def reflectionB : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, -1]

/-- The third transposition matrix, obtained as the conjugate `A * B * A`. -/
def reflectionC : Matrix (Fin 2) (Fin 2) ℤ := reflectionA * reflectionB * reflectionA

/-- The two concrete integer reflections square to identity but fail to commute. -/
lemma reflection_generators_are_involutions_and_do_not_commute :
    reflectionA * reflectionA = 1 ∧
    reflectionB * reflectionB = 1 ∧
    reflectionA * reflectionB ≠ reflectionB * reflectionA := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reflectionA, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reflectionB, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    norm_num [reflectionA, reflectionB, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- A two-dimensional integer matrix representation of the repository's six-element
`S3Perm` group. This is a representation homomorphism; no irreducibility claim is made. -/
def s3MatrixRep : InfoGeometry.Algebra.S3Perm →* Matrix (Fin 2) (Fin 2) ℤ where
  toFun
    | .id => 1
    | .s12 => reflectionA
    | .s23 => reflectionB
    | .s31 => reflectionC
    | .s12_s23 => reflectionB * reflectionA
    | .s23_s12 => reflectionA * reflectionB
  map_one' := by decide
  map_mul' x y := by
    cases x <;> cases y <;> decide

/-- The homomorphism sends the repository's noncommuting transpositions to
noncommuting integer matrices, and therefore preserves this word-order witness. -/
lemma s3MatrixRep_preserves_transposition_order :
    s3MatrixRep .s12 * s3MatrixRep .s23 ≠ s3MatrixRep .s23 * s3MatrixRep .s12 := by
  change reflectionA * reflectionB ≠ reflectionB * reflectionA
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  norm_num [reflectionA, reflectionB, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- The concrete two-dimensional representation separates all six elements of
the repository's `S3Perm` group. This is a faithfulness result for this explicit
integer representation; it does not assert irreducibility or a group-algebra
Wedderburn decomposition. -/
lemma s3MatrixRep_injective : Function.Injective s3MatrixRep := by
  intro x y h
  cases x <;> cases y <;> try rfl
  all_goals
    have hEntries := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℤ => (M 0 0, M 0 1, M 1 0, M 1 1)) h
    norm_num [s3MatrixRep, reflectionA, reflectionB, reflectionC,
      Matrix.mul_apply, Fin.sum_univ_two] at hEntries

/-- Over a commutative ring, the four trace coefficients recover twice a matrix.
This identity alone is not a uniqueness theorem unless multiplication by `2`
is injective (for example, if `2` is a unit). -/
lemma two_mul_matrix_from_four_traces {K : Type*} [CommRing K]
    (M : Matrix (Fin 2) (Fin 2) K) :
    (2 : K) • M =
      Matrix.trace (M * !![1, 0; 0, 1]) • !![1, 0; 0, 1] +
      Matrix.trace (M * !![1, 0; 0, -1]) • !![1, 0; 0, -1] +
      Matrix.trace (M * !![0, 1; 1, 0]) • !![0, 1; 1, 0] -
      Matrix.trace (M * !![0, 1; -1, 0]) • !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Whenever multiplication by `2` is injective in `K`, the four trace inner products
uniquely determine `M : Matrix (Fin 2) (Fin 2) K`. -/
lemma four_traces_unique_of_two_mul_injective {K : Type*} [CommRing K]
    (h2 : Function.Injective (fun x : K => (2 : K) * x))
    (M N : Matrix (Fin 2) (Fin 2) K)
    (hI : Matrix.trace (M * !![1, 0; 0, 1]) = Matrix.trace (N * !![1, 0; 0, 1]))
    (hS : Matrix.trace (M * !![1, 0; 0, -1]) = Matrix.trace (N * !![1, 0; 0, -1]))
    (hPhi : Matrix.trace (M * !![0, 1; 1, 0]) = Matrix.trace (N * !![0, 1; 1, 0]))
    (hJ : Matrix.trace (M * !![0, 1; -1, 0]) = Matrix.trace (N * !![0, 1; -1, 0])) :
    M = N := by
  have hEq : (2 : K) • M = (2 : K) • N := by
    rw [two_mul_matrix_from_four_traces M, two_mul_matrix_from_four_traces N,
        hI, hS, hPhi, hJ]
  ext i j
  apply h2
  simpa [Matrix.smul_apply, smul_eq_mul] using congr_fun (congr_fun hEq i) j

/-- **Schur Commutant Theorem for the 2D `S3Perm` Representation:**
Over any commutative ring `K` (with no characteristic assumption), a `2 × 2` matrix `M`
commutes with the two root-reflection generators `!![-1, 1; 0, 1]` and `!![1, 0; 1, -1]`
if and only if `M` is a scalar multiple `M 0 0 • 1` of the identity matrix. -/
lemma s3MatrixRep_commutant_iff_scalar {K : Type*} [CommRing K]
    (M : Matrix (Fin 2) (Fin 2) K) :
    (!![(-1 : K), 1; 0, 1] * M = M * !![(-1 : K), 1; 0, 1] ∧
     !![(1 : K), 0; 1, -1] * M = M * !![(1 : K), 0; 1, -1]) ↔
    M = M 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) := by
  constructor
  · rintro ⟨hA, hB⟩
    have hA00 := congr_fun (congr_fun hA 0) 0
    have hB00 := congr_fun (congr_fun hB 0) 0
    have hB10 := congr_fun (congr_fun hB 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one] at hA00 hB00 hB10
    have h01 : M 0 1 = 0 := by linear_combination -hB00
    have h10 : M 1 0 = 0 := by linear_combination hA00
    have h11 : M 1 1 = M 0 0 := by linear_combination -hB10 - 2 * hA00
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, h01, h10, h11]
  · intro hScalar
    rw [hScalar]
    exact ⟨by ext i j; fin_cases i <;> fin_cases j <;>
                simp [Matrix.mul_apply, Matrix.one_apply],
           by ext i j; fin_cases i <;> fin_cases j <;>
                simp [Matrix.mul_apply, Matrix.one_apply]⟩

/-- **Burnside Spanning Identity for the 2D `S3Perm` Representation:**
Over any commutative ring `K`, `3 • M` for any `2 × 2` matrix `M` is an explicit linear
combination of the four `S3Perm` representation matrices corresponding to `.id`, `.s12`,
`.s23`, and `.s12_s23`. -/
lemma three_smul_matrix_in_s3_span {K : Type*} [CommRing K]
    (M : Matrix (Fin 2) (Fin 2) K) :
    (3 : K) • M =
      (2 * M 0 0 + M 0 1 - M 1 0 + M 1 1) • !![(1 : K), 0; 0, 1] +
      (-M 0 0 + M 0 1 + 2 * M 1 0 + M 1 1) • !![(-1 : K), 1; 0, 1] +
      (M 0 0 + 2 * M 0 1 + M 1 0 - M 1 1) • !![(1 : K), 0; 1, -1] +
      (M 0 0 + 2 * M 0 1 - 2 * M 1 0 - M 1 1) • !![(-1 : K), 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, smul_eq_mul] <;> ring

/-- Alternating sign character `χ_sign : S3Perm →* ℤ` sending even permutations to `1`
and transpositions to `-1`. -/
def s3SignChar : InfoGeometry.Algebra.S3Perm →* ℤ where
  toFun
    | .id => 1
    | .s12 => -1
    | .s23 => -1
    | .s31 => -1
    | .s12_s23 => 1
    | .s23_s12 => 1
  map_one' := rfl
  map_mul' x y := by cases x <;> cases y <;> decide

/-- Diagonal Peirce grading involution `S_P = !![1, 0; 0, -1]` over `K`. -/
def peirceGradingS {K : Type*} [CommRing K] : Matrix (Fin 2) (Fin 2) K :=
  !![1, 0; 0, -1]

/-- Off-diagonal swap involution `Φ = !![0, 1; 1, 0]` over `K`. -/
def peirceSwapPhi {K : Type*} [CommRing K] : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 1, 0]

/-- Anticommutator witness `S_P * Φ + Φ * S_P = 0` in `Matrix (Fin 2) (Fin 2) K`
over any commutative ring `K`. -/
lemma peirceGradingS_anticomm_peirceSwapPhi {K : Type*} [CommRing K] :
    peirceGradingS (K := K) * peirceSwapPhi (K := K) +
      peirceSwapPhi (K := K) * peirceGradingS (K := K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peirceGradingS, peirceSwapPhi]

/-- The concrete rank-one Peirce cut in the same `2 × 2` matrix carrier as `s3MatrixRep`. -/
def standardPeirceCut : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]

/-- Upper off-diagonal matrix unit, the `conePlus` corner for `standardPeirceCut`. -/
def peirceUnit12 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

/-- Lower off-diagonal matrix unit, the `coneMinus` corner for `standardPeirceCut`. -/
def peirceUnit21 : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

/-- The two simple reflections in the faithful `S3Perm` representation split into the
diagonal Peirce grading and one off-diagonal Peirce corner each. This is an explicit
same-carrier bridge: the representation matrices and the Peirce operators both lie in
`Matrix (Fin 2) (Fin 2) ℤ`. It does not assert that the generic rotor theorem is a
dihedral representation. -/
lemma s3_reflections_as_peirce_corner_combinations :
    s3MatrixRep .s12 =
        - InfoGeometry.OperatorAlgebra.PeirceSpine.invS standardPeirceCut +
          InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus standardPeirceCut peirceUnit12 ∧
    s3MatrixRep .s23 =
        InfoGeometry.OperatorAlgebra.PeirceSpine.invS standardPeirceCut +
          InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus standardPeirceCut peirceUnit21 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [s3MatrixRep, reflectionA, reflectionB, standardPeirceCut,
      peirceUnit12, peirceUnit21, InfoGeometry.OperatorAlgebra.PeirceSpine.invS,
      InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus,
      InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus,
      Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two]

/-- **Exact Peter–Weyl Regular Character Orthogonality on `S3Perm`:**
For every `g : S3Perm`, the weighted character sum `1 + χ_sign(g) + 2 · Tr(ρ₂(g))`
equals `6` at `g = .id` and `0` at all five non-identity elements. -/
lemma s3_regular_character_orthogonality (g : InfoGeometry.Algebra.S3Perm) :
    (1 : ℤ) + s3SignChar g + 2 * Matrix.trace (s3MatrixRep g) =
      match g with | .id => 6 | _ => 0 := by
  cases g <;> decide

end InfoGeometry.Canonical.FiniteCharacterMatrixOrder
