/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearInternalExternalParityFactorization
import InfoGeometry.Physics.NuclearPhononRPAAlgebra
import InfoGeometry.Core.IdempotentCartan

/-!
# Operator RPA blocks and chiral parity

The signed RPA block is expressed through the existing operator-valued
`blockHamiltonian`. Its coefficients belong to an arbitrary associative ring.
The square retains the commutator of the two coefficients.

An unnormalised Hadamard intertwiner changes the block to an off-diagonal
chiral operator with independent ordered factors `a - b` and `a + b`. Its
square has the two ordered products on its diagonal. The intertwining
identities require neither coefficient commutation nor division by two.
-/

namespace InfoGeometry.Physics.OperatorRPABlock

open InfoGeometry.Physics.NuclearOperatorSuperSoloviev
open InfoGeometry.Physics.NuclearInternalExternalParityFactorization

variable {A : Type*} [Ring A]

/-- The full signed RPA square retains both copies of the coefficient
commutator. -/
theorem rpa_square (a b : A) :
    blockHamiltonian a (-a) b (-b) * blockHamiltonian a (-a) b (-b) =
      blockHamiltonian (a * a - b * b) (a * a - b * b)
        (a * b - b * a) (a * b - b * a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two] <;>
    noncomm_ring

/-- The square loses its off-diagonal term exactly when the two coefficient
operators commute. -/
theorem rpa_square_offDiagonal_eq_zero_iff (a b : A) :
    (blockHamiltonian a (-a) b (-b) *
      blockHamiltonian a (-a) b (-b)) 0 1 = 0 ↔ a * b = b * a := by
  rw [rpa_square]
  simp [blockHamiltonian, sub_eq_zero]

/-- Noncommuting RPA coefficients create a nonzero off-diagonal defect. This
is the bare algebraic obstruction that grades the commuting Tamm–Dancoff
sector from the noncommuting full RPA sector. -/
theorem rpa_square_offDiagonal_ne_zero_of_not_commute (a b : A)
    (h : a * b ≠ b * a) :
    (blockHamiltonian a (-a) b (-b) *
      blockHamiltonian a (-a) b (-b)) 0 1 ≠ 0 := by
  intro hz
  exact h ((rpa_square_offDiagonal_eq_zero_iff a b).mp hz)

/-- Commuting RPA coefficients collapse the squared block to a purely diagonal
quantum-number sector even when the backward amplitude is nonzero. -/
theorem rpa_square_commuting_coeffs_diagonal (a b : A) (h : a * b = b * a) :
    blockHamiltonian a (-a) b (-b) * blockHamiltonian a (-a) b (-b) =
      blockHamiltonian (a * a - b * b) (a * a - b * b) 0 0 := by
  rw [rpa_square, h, sub_self]

/-- The `b = 0` (no backward amplitude / Tamm–Dancoff) limit of the RPA square
is the diagonal square with entries `a * a`; no involution or self-adjointness
structure on the coefficient ring is assumed. -/
theorem rpa_block_b_zero_eq_tda_square (a : A) :
    blockHamiltonian a (-a) 0 0 * blockHamiltonian a (-a) 0 0 =
      blockHamiltonian (a * a) (a * a) 0 0 := by
  simpa using rpa_square a (0 : A)

/-- The Tamm–Dancoff limit has zero off-diagonal commutator defect. -/
theorem rpa_block_b_zero_offDiagonal_eq_zero (a : A) :
    (blockHamiltonian a (-a) 0 0 * blockHamiltonian a (-a) 0 0) 0 1 = 0 := by
  simp [blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two]

/-- The signed RPA operator acts on forward/backward amplitudes by the
ordered operator equations `(a*x + b*y, -b*x - a*y)`. This retains the
coefficient order and makes no commutativity assumption on `A`. -/
theorem rpa_mulVec_amplitudes (a b : A) (x y : A) :
    (blockHamiltonian a (-a) b (-b)).mulVec ![x, y] = ![a * x + b * y, -b * x - a * y] := by
  ext i
  fin_cases i
  · simp [blockHamiltonian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [blockHamiltonian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    noncomm_ring

/-- A particular forward amplitude has no backward output exactly when it is
annihilated on the left by the backward coupling. This pointwise criterion
allows a nonzero coupling to leave a nontrivial forward subspace untouched. -/
theorem rpa_forward_state_no_backward_output_iff (a b x : A) :
    (blockHamiltonian a (-a) b (-b)).mulVec ![x, 0] 1 = 0 ↔ b * x = 0 := by
  rw [rpa_mulVec_amplitudes]
  simp

/-- The forward-amplitude sector is invariant under the signed RPA block
exactly when the backward coupling vanishes. The converse uses the unit
amplitude, so this characterization holds over any unital coefficient ring. -/
theorem rpa_forward_sector_invariant_iff_backward_coupling_zero (a b : A) :
    (∀ x : A, (blockHamiltonian a (-a) b (-b)).mulVec ![x, 0] 1 = 0) ↔ b = 0 := by
  constructor
  · intro h
    have hUnit := h 1
    rw [rpa_mulVec_amplitudes] at hUnit
    simpa using hUnit
  · intro hb x
    rw [rpa_mulVec_amplitudes]
    simp [hb]

/-- The unnormalised Hadamard block squares to twice the identity; an inverse
is not required for any result below. -/
theorem hadamard_square :
    blockHamiltonian (1 : A) (-1) 1 1 * blockHamiltonian 1 (-1) 1 1 =
      (2 : ℕ) • (1 : Block2 A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two]

/-- The signed RPA block intertwines with a chiral off-diagonal operator.
The two factors keep their original multiplication order. -/
theorem hadamard_intertwines_rpa (a b : A) :
    blockHamiltonian 1 (-1) 1 1 * blockHamiltonian a (-a) b (-b) =
      blockHamiltonian 0 0 (a - b) (a + b) *
        blockHamiltonian 1 (-1) 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two] <;>
    abel

/-- Multiplication on both sides gives twice the chiral block, with no
assumption that two is invertible. -/
theorem hadamard_rpa_hadamard (a b : A) :
    blockHamiltonian 1 (-1) 1 1 * blockHamiltonian a (-a) b (-b) *
        blockHamiltonian 1 (-1) 1 1 =
      (2 : ℕ) • blockHamiltonian 0 0 (a - b) (a + b) := by
  rw [hadamard_intertwines_rpa, mul_assoc, hadamard_square]
  simp only [two_nsmul, mul_add, mul_one]

/-- Before the change of block coordinates, exchanging the two sheets is
the chiral sign reversal of the signed RPA block. -/
theorem exchange_conjugation_rpa (a b : A) :
    blockHamiltonian 0 0 1 1 * blockHamiltonian a (-a) b (-b) *
        blockHamiltonian 0 0 1 1 =
      -blockHamiltonian a (-a) b (-b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two]

/-- The transformed RPA operator is odd under the existing external Fock
parity involution. -/
theorem chiral_rpa_parity (a b : A) :
    externalFockParity * blockHamiltonian 0 0 (a - b) (a + b) *
        externalFockParity =
      -blockHamiltonian 0 0 (a - b) (a + b) := by
  rw [externalFockParity_reflection]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectOffDiagonal, blockHamiltonian]

/-- Squaring the chiral form produces two ordered operator products, one on
each sheet. They are not identified with one common scalar. -/
theorem chiral_rpa_square (a b : A) :
    blockHamiltonian 0 0 (a - b) (a + b) *
        blockHamiltonian 0 0 (a - b) (a + b) =
      blockHamiltonian ((a - b) * (a + b)) ((a + b) * (a - b)) 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockHamiltonian, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two square sectors differ by the sign of the retained coefficient
commutator. -/
theorem ordered_rpa_products (a b : A) :
    (a - b) * (a + b) = a * a - b * b + (a * b - b * a) ∧
      (a + b) * (a - b) = a * a - b * b - (a * b - b * a) := by
  constructor <;> noncomm_ring

/-- The same Hadamard map intertwines the complete squared RPA operator
with the two ordered square sectors. -/
theorem hadamard_intertwines_rpa_square (a b : A) :
    blockHamiltonian 1 (-1) 1 1 *
        (blockHamiltonian a (-a) b (-b) * blockHamiltonian a (-a) b (-b)) =
      blockHamiltonian ((a - b) * (a + b)) ((a + b) * (a - b)) 0 0 *
        blockHamiltonian 1 (-1) 1 1 := by
  calc
    _ = (blockHamiltonian 1 (-1) 1 1 *
          blockHamiltonian a (-a) b (-b)) *
          blockHamiltonian a (-a) b (-b) := (mul_assoc _ _ _).symm
    _ = (blockHamiltonian 0 0 (a - b) (a + b) *
          blockHamiltonian 1 (-1) 1 1) *
          blockHamiltonian a (-a) b (-b) := by
            rw [hadamard_intertwines_rpa]
    _ = blockHamiltonian 0 0 (a - b) (a + b) *
          (blockHamiltonian 1 (-1) 1 1 *
            blockHamiltonian a (-a) b (-b)) := mul_assoc _ _ _
    _ = blockHamiltonian 0 0 (a - b) (a + b) *
          (blockHamiltonian 0 0 (a - b) (a + b) *
            blockHamiltonian 1 (-1) 1 1) := by
              rw [hadamard_intertwines_rpa]
    _ = (blockHamiltonian 0 0 (a - b) (a + b) *
          blockHamiltonian 0 0 (a - b) (a + b)) *
          blockHamiltonian 1 (-1) 1 1 := (mul_assoc _ _ _).symm
    _ = _ := by rw [chiral_rpa_square]

/-- Chiral parity preserves the full ordered square even when its two
diagonal operators are different. -/
theorem chiral_rpa_square_parity (a b : A) :
    externalFockParity *
        (blockHamiltonian 0 0 (a - b) (a + b) *
          blockHamiltonian 0 0 (a - b) (a + b)) * externalFockParity =
      blockHamiltonian 0 0 (a - b) (a + b) *
        blockHamiltonian 0 0 (a - b) (a + b) := by
  simp only [chiral_rpa_square]
  rw [externalFockParity_reflection]
  simp only [reflectOffDiagonal, neg_zero]

/-! ## Tamm–Dancoff (`b = 0`) Reduction, Noncommutative `[a, b]` Defect & RPA Zero Modes -/

/-- Setting `b = 0` collapses the signed RPA operator block to the block-diagonal
Tamm–Dancoff (TDA) operator. -/
theorem tda_block_eq (a : A) :
    blockHamiltonian a (-a) (0 : A) (-0) = blockHamiltonian a (-a) 0 0 := by
  simp [blockHamiltonian]

/-- The RPA correlation commutator `a * b - b * a` vanishes identically in the `b = 0` TDA limit. -/
theorem tda_correlation_commutator_eq_zero (a : A) :
    a * (0 : A) - (0 : A) * a = 0 := by
  simp

/-- In the `b = 0` TDA limit, both chiral ordered products collapse to `a ^ 2`. -/
theorem tda_chiral_ordered_products_eq_sq (a : A) :
    (a - 0) * (a + 0) = a ^ 2 ∧ (a + 0) * (a - 0) = a ^ 2 := by
  simp [sq]

/-- Squaring the chiral operator at `b = 0` yields equal diagonal blocks `a ^ 2` across both sheets. -/
theorem chiral_tda_square (a : A) :
    blockHamiltonian 0 0 (a - 0) (a + 0) * blockHamiltonian 0 0 (a - 0) (a + 0) =
      blockHamiltonian (a ^ 2) (a ^ 2) 0 0 := by
  simpa [sq] using chiral_rpa_square a (0 : A)

/-- Forward-amplitude action of the signed RPA block and its exact `b = 0` TDA invariance
(`2603.29257v1` Eq. 9: `Y = 0` invariant subspace). -/
theorem rpa_block_mulVec_tda_invariant (a b x : A) :
    (blockHamiltonian a (-a) b (-b)).mulVec ![x, 0] = ![a * x, -(b * x)] ∧
      (blockHamiltonian a (-a) 0 (-0)).mulVec ![x, 0] = ![a * x, 0] := by
  refine ⟨?_, ?_⟩
  · simpa [mul_zero, add_zero, sub_eq_add_neg, neg_mul] using rpa_mulVec_amplitudes a b x 0
  · simpa [neg_zero] using rpa_mulVec_amplitudes a (0 : A) x 0

/-- Exact difference between the squared full RPA block and the squared `b = 0` TDA block,
retaining both `-(b * b)` correlation shifts and the `[a, b]` commutator defect. -/
theorem rpa_square_sub_tda_square (a b : A) :
    blockHamiltonian a (-a) b (-b) * blockHamiltonian a (-a) b (-b) -
        blockHamiltonian a (-a) 0 0 * blockHamiltonian a (-a) 0 0 =
      blockHamiltonian (-(b * b)) (-(b * b)) (a * b - b * a) (a * b - b * a) := by
  rw [rpa_square, rpa_block_b_zero_eq_tda_square]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockHamiltonian]

/-- Chiral-basis difference between the squared full RPA operator and the squared `b = 0` TDA
operator, isolating the opposite sheet commutator defects `± [a, b]`. -/
theorem chiral_rpa_square_sub_tda_square (a b : A) :
    blockHamiltonian 0 0 (a - b) (a + b) * blockHamiltonian 0 0 (a - b) (a + b) -
        blockHamiltonian 0 0 (a - 0) (a + 0) * blockHamiltonian 0 0 (a - 0) (a + 0) =
      blockHamiltonian (-(b * b) + (a * b - b * a)) (-(b * b) - (a * b - b * a)) 0 0 := by
  rw [chiral_rpa_square, chiral_tda_square]
  have hord := ordered_rpa_products a b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockHamiltonian, hord.1, hord.2, sq] <;> noncomm_ring

/-- Exact difference between the two chiral RPA sheet squares equals twice the `[a, b]` commutator. -/
theorem chiral_rpa_sheet_difference (a b : A) :
    (a - b) * (a + b) - (a + b) * (a - b) = (a * b - b * a) + (a * b - b * a) := by
  noncomm_ring

/-- Any right null-vector `u` of `a - b` yields a zero-mode `![u, -u]` of the signed RPA block. -/
theorem rpa_zero_mode_of_sub_eq_zero {a b u : A} (h : (a - b) * u = 0) :
    (blockHamiltonian a (-a) b (-b)).mulVec ![u, -u] = 0 := by
  rw [rpa_mulVec_amplitudes]
  have h0 : a * u + b * -u = 0 := by
    calc
      a * u + b * -u = (a - b) * u := by noncomm_ring
      _ = 0 := h
  have h1 : -b * u - a * -u = 0 := by
    calc
      -b * u - a * -u = (a - b) * u := by noncomm_ring
      _ = 0 := h
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- Any right null-vector `u` of `a + b` yields a zero-mode `![u, u]` of the signed RPA block. -/
theorem rpa_zero_mode_of_add_eq_zero {a b u : A} (h : (a + b) * u = 0) :
    (blockHamiltonian a (-a) b (-b)).mulVec ![u, u] = 0 := by
  rw [rpa_mulVec_amplitudes]
  have h0 : a * u + b * u = 0 := by
    calc
      a * u + b * u = (a + b) * u := by noncomm_ring
      _ = 0 := h
  have h1 : -b * u - a * u = 0 := by
    calc
      -b * u - a * u = -((a + b) * u) := by noncomm_ring
      _ = 0 := by rw [h, neg_zero]
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- Canonical Goldstone-diagonal zero mode `![1, -1]` when backward coupling equals forward
coupling (`b = a`). -/
theorem rpa_zero_mode_eq_diagonal (a : A) :
    (blockHamiltonian a (-a) a (-a)).mulVec ![1, -1] = 0 :=
  rpa_zero_mode_of_sub_eq_zero (by simp)

section PhononRPABridge

open InfoGeometry.Physics.NuclearPhononRPA

/-- Action of a `2 × 2` matrix-valued block operator `Block2 (Matrix ι ι R)` on a two-component
vector `Fin 2 → (ι → R)` over an arbitrary finite index type `ι` and commutative ring `R`. -/
def blockAction {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Block2 (Matrix ι ι R)) (v : Fin 2 → (ι → R)) : Fin 2 → (ι → R) :=
  fun i => Matrix.mulVec (M i 0) (v 0) + Matrix.mulVec (M i 1) (v 1)

/-- Equivalence between the block-operator RPA eigenproblem on `Fin 2 → (ι → R)` and the coupled
forward/backward matrix equations `A_mat *ᵥ x + B_mat *ᵥ y = ω • x` and
`-B_mat *ᵥ x - A_mat *ᵥ y = ω • y`. -/
theorem blockHamiltonian_rpa_eigenproblem_iff {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (A_mat B_mat : Matrix ι ι R) (x y : ι → R) (ω : R) :
    blockAction (blockHamiltonian A_mat (-A_mat) B_mat (-B_mat)) ![x, y] = ![ω • x, ω • y] ↔
      (Matrix.mulVec A_mat x + Matrix.mulVec B_mat y = ω • x ∧
        -Matrix.mulVec B_mat x - Matrix.mulVec A_mat y = ω • y) := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [blockAction, blockHamiltonian, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.neg_mulVec] at h0 h1
    refine ⟨h0, ?_⟩
    simpa only [sub_eq_add_neg] using h1
  · rintro ⟨h0, h1⟩
    ext i k
    fin_cases i
    · simpa [blockAction, blockHamiltonian] using congrFun h0 k
    · simpa [blockAction, blockHamiltonian, Matrix.neg_mulVec, sub_eq_add_neg] using congrFun h1 k

/-- **Acyclic Bridge to `PhononRPA.thouless_goldstone_zero_mode`**: any conserved symmetry
generator `P_0 = P_rest + rpa.rpaMode Finset.univ x y` commuting with `H` in a linearized RPA
`PhononRPA ι Alg` system produces an exact null-vector `![x, y]` of the signed RPA block
`blockHamiltonian A_mat (-A_mat) B_mat (-B_mat)` over any finite mode type `ι` and field `F`. -/
theorem phononRPA_thouless_zero_mode_to_blockHamiltonian
    {ι F Alg : Type*} [Fintype ι] [DecidableEq ι]
    [Field F] [Ring Alg] [Algebra F Alg] [Nontrivial Alg]
    (rpa : PhononRPA ι Alg) (H P_rest : Alg)
    (A_mat B_mat : Matrix ι ι F) (x y : ι → F)
    (h_eom_Qdag : ∀ i : ι, NuclearPhononRPA.comm H (rpa.Qdag i) =
      ∑ j : ι, (A_mat j i • rpa.Qdag j - B_mat j i • rpa.Q j))
    (h_eom_Q : ∀ i : ι, NuclearPhononRPA.comm H (rpa.Q i) =
      ∑ j : ι, (B_mat j i • rpa.Qdag j - A_mat j i • rpa.Q j))
    (h_rest : ∀ k : ι, NuclearPhononRPA.comm (rpa.Q k) (NuclearPhononRPA.comm H P_rest) = 0 ∧
      NuclearPhononRPA.comm (rpa.Qdag k) (NuclearPhononRPA.comm H P_rest) = 0)
    (h_comm : NuclearPhononRPA.comm H (P_rest + rpa.rpaMode Finset.univ x y) = 0) :
    blockAction (blockHamiltonian A_mat (-A_mat) B_mat (-B_mat)) ![x, y] = 0 := by
  have hzero := rpa.thouless_goldstone_zero_mode Finset.univ H P_rest A_mat B_mat x y
    (fun i _ => h_eom_Qdag i) (fun i _ => h_eom_Q i) (fun k _ => h_rest k) h_comm
  have heig : blockAction (blockHamiltonian A_mat (-A_mat) B_mat (-B_mat)) ![x, y] =
      ![(0 : F) • x, (0 : F) • y] := by
    rw [blockHamiltonian_rpa_eigenproblem_iff]
    constructor <;> ext k
    · simpa [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib] using
        (hzero k (Finset.mem_univ k)).1
    · simpa [Matrix.mulVec, dotProduct, sub_eq_add_neg, neg_mul,
        Finset.sum_add_distrib, Finset.sum_neg_distrib] using
        (hzero k (Finset.mem_univ k)).2
  rw [heig]
  ext i k
  fin_cases i <;> simp

section ChiralCurvatureObstruction

/-- Over any `ℝ`-algebra, the chiral RPA sheet difference `(a - b) * (a + b) - (a + b) * (a - b)`
is exact twice the commutator `[a, b]`, characterizing `[a, b]` as the chiral sheet-curvature defect. -/
theorem chiral_rpa_sheet_curvature_eq_two_comm {Alg : Type*} [Ring Alg] [Algebra ℝ Alg]
    (a b : Alg) :
    (a - b) * (a + b) - (a + b) * (a - b) = (2 : ℝ) • (a * b - b * a) := by
  have h : (2 : ℝ) • (a * b - b * a) = (a * b - b * a) + (a * b - b * a) := by
    have h2 : (2 : ℝ) = 1 + 1 := by norm_num
    rw [h2, add_smul, one_smul]
  rw [h]
  exact chiral_rpa_sheet_difference a b

/-- The chiral RPA sheet-curvature defect vanishes if and only if `a` and `b` commute (`a * b = b * a`). -/
theorem chiral_rpa_sheet_difference_eq_zero_iff {Alg : Type*} [Ring Alg] [Algebra ℝ Alg]
    (a b : Alg) :
    (a - b) * (a + b) = (a + b) * (a - b) ↔ Commute a b := by
  rw [← sub_eq_zero, chiral_rpa_sheet_curvature_eq_two_comm, smul_eq_zero]
  constructor
  · rintro (h2 | hcomm)
    · norm_num at h2
    · exact sub_eq_zero.mp hcomm
  · intro hcomm
    right
    exact sub_eq_zero.mpr hcomm.eq

/-- Equivalently, the RPA-minus-TDA off-diagonal commutator defect vanishes iff `Commute a b`. -/
theorem rpa_vs_tda_curvature_defect_vanishes_iff (a b : A) :
    a * b - b * a = 0 ↔ Commute a b := by
  rw [sub_eq_zero, commute_iff_eq]

end ChiralCurvatureObstruction

section PeirceOddGradeTransport

/-- The RPA coefficient commutator is nonzero exactly when the Peirce odd
grade of the forward coefficient relative to an idempotent backward
coefficient is nonzero. This transports the obstruction into the existing
`oddPart` grade without adding a wrapper or a new structure field. -/
theorem rpa_commutator_ne_zero_iff_oddPart_ne_zero (a b : A)
    (hb : b * b = b) :
    a * b ≠ b * a ↔
      InfoGeometry.Core.IdempotentCartan.oddPart b a ≠ 0 := by
  constructor
  · intro hcomm hodd
    exact hcomm
      ((InfoGeometry.Core.IdempotentCartan.odd_zero_iff_commute hb a).mp hodd).symm
  · intro hodd hcomm
    exact hodd
      ((InfoGeometry.Core.IdempotentCartan.odd_zero_iff_commute hb a).mpr hcomm.symm)

/-- The full RPA square retains an off-diagonal defect exactly when that
idempotent-relative Peirce odd grade is nonzero. -/
theorem rpa_square_offDiagonal_ne_zero_iff_oddPart_ne_zero (a b : A)
    (hb : b * b = b) :
    (blockHamiltonian a (-a) b (-b) *
      blockHamiltonian a (-a) b (-b)) 0 1 ≠ 0 ↔
        InfoGeometry.Core.IdempotentCartan.oddPart b a ≠ 0 := by
  constructor
  · intro hdef hodd
    exact hdef ((rpa_square_offDiagonal_eq_zero_iff a b).mpr
      ((InfoGeometry.Core.IdempotentCartan.odd_zero_iff_commute hb a).mp hodd).symm)
  · intro hodd hzero
    exact hodd ((InfoGeometry.Core.IdempotentCartan.odd_zero_iff_commute hb a).mpr
      ((rpa_square_offDiagonal_eq_zero_iff a b).mp hzero).symm)

end PeirceOddGradeTransport

end PhononRPABridge

end InfoGeometry.Physics.OperatorRPABlock
