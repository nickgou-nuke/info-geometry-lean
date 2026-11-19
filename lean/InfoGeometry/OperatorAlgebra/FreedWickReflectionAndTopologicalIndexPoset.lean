/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Causal.FiniteDependencyCompiler
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Meta.EpistemicCompilerChain
import InfoGeometry.Meta.MetaEpistemicCompiler
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NoncommRing

/-!
# InfoGeometry.OperatorAlgebra.FreedWickReflectionAndTopologicalIndexPoset

Noncommutative epistemic-compiler formalization ("solve et coagula") distilling Dan Freed's
rigorous Quantum Field Theory and Topological Index Theory perspective into an acyclic
6-node causal poset $(\mathcal{F}, \preceq)$ of native Mathlib operator-algebraic theorems:

- **$\mathcal{F}_1$ (`osReflectionCut`) — Osterwalder–Schrader Reflection Positivity & Chiral Cut**:
  Involutive matrix reflection `osReflect η X := η * X * η` (`η² = 1`), trace sesquilinear form
  `osTraceForm η X Y := Matrix.trace (star (osReflect η X) * Y)`, positive semidefiniteness
  `0 ≤ (osTraceForm η X X).re` on the reflection-invariant sector `osReflect η X = X` in arbitrary
  matrix dimension `n`, and strict Lorentzian negativity `(osTraceForm pauliZ2 pauliX2 pauliX2).re = -2 < 0`
  from the anticommuting chiral split `pauliZ2 * pauliX2 = - (pauliX2 * pauliZ2)`.
- **$\mathcal{F}_2$ (`wickSegalCayleyDichotomy`) — Euclidean Semigroup vs Lorentzian Cayley Unitary**:
  Explicit contractive Euclidean transfer matrix `euclidStep2 γ` (`0 ≤ γ < 1`, trace strictly `< 2`),
  Lorentzian Cayley unitary transform `cayleyStep2 ω` satisfying `(1 + i ω σ_x) cayleyStep2 ω = 1 - i ω σ_x`
  and exact unitarity `star (cayleyStep2 ω) * cayleyStep2 ω = 1` with invariant trace `2`, plus
  noncommuting rank-1 orthogonal projections `projDiag2 * projPlus2 ≠ projPlus2 * projDiag2`.
- **$\mathcal{F}_3$ (`projectiveAnomalyCancellation`) — Projective 2-Cocycle Anomaly & Doubled Cancellation**:
  Noncommutative projective group lift 2-cocycle `u g * u h = z g h • u (g * h)` in general `R`-algebras
  `A`, proof of coboundary invariance of commutator skewness under scalar rescaling `u' g = b g • u g`,
  explicit `ZMod 2 × ZMod 2` Pauli projective obstruction on `Mat2C` proving no scalar coboundary
  restores commutativity, and doubled Kronecker tensor representation
  `doubledPauliHom : Multiplicative (ZMod 2 × ZMod 2) →* (Matrix (Fin 2) (Fin 2) Mat2C)ˣ`
  where `(-1) * (-1) = 1` yields a genuine group homomorphism with non-diagonal block image.
- **$\mathcal{F}_4$ (`kreinBrstCohomology`) — Hilbert Nilpotent No-Go vs Krein-Hermitian BRST**:
  General `Matrix (Fin n) (Fin n) ℂ` Hilbert no-go theorem proving `star Q = Q → Q * Q = 0 → Q = 0`,
  contrasted with the nonzero Krein-Hermitian BRST operator `brstQ2 ≠ 0` (`brstQ2 * brstQ2 = 0`,
  `kreinEta2 * star brstQ2 * kreinEta2 = brstQ2`, `gradingGamma2 * brstQ2 + brstQ2 * gradingGamma2 = 0`)
  and its algebraic Hodge-laplacian commutator `brstQ2 * brstQ2Star + brstQ2Star * brstQ2 = 1`.
- **$\mathcal{F}_5$ (`mcKeanSingerIndexInvariance`) — McKean–Singer Supertrace & Jumping-Kernel Invariance**:
  Exact vanishing of `superTrace γ (D ^ (k + 1)) = 0` for EVERY `k : ℕ` and arbitrary dimension `m`
  whenever `γ * D + D * γ = 0`, polynomial heat-kernel invariance `superTrace γ (heatKernelPoly N c t D) = c 0 * trace γ`,
  and an explicit `Mat3C` self-adjoint jumping Dirac family `diracJump3 s` whose kernel jumps from
  dimension `3` (`s = 0`) to dimension `1` (`s ≠ 0`) while its supertrace index stays `1` identically.
- **$\mathcal{F}_6$ (`masterTopologicalSynthesis`) — Diamond Causal Poset & Certified Compilation**:
  Non-linear 6-node diamond poset `FreedQFTArchetype` (`F1 ≤ {F2, F3, F4}`, `{F2, F4} ≤ F5`, `{F3, F5} ≤ F6`),
  QMS `TypedArchetype`s `archF1`–`archF6` and `freedWickTopologicalPosetArchetype`, `#audit_archetype`,
  and `executable_certified_compilation`.

## Three-Bucket Audit Map

* **BUCKET 1 (Native kernel-checked definitions & theorems)**:
  - Involutive OS reflection positivity in arbitrary `Matrix (Fin n) (Fin n) ℂ` and indefinite
    Lorentzian counterexample on `Mat2C`.
  - Euclidean contraction vs exact Lorentzian Cayley unitary relation and trace split.
  - Coboundary skewness invariance, `ZMod 2 × ZMod 2` Pauli no-go rescaling theorem, and
    genuine `Multiplicative (ZMod 2 × ZMod 2) →* (Matrix (Fin 2) (Fin 2) Mat2C)ˣ` cancellation.
  - Dimension-arbitrary Hilbert self-adjoint nilpotent no-go vs Krein-Hermitian `Mat2C` BRST.
  - Dimension-arbitrary all-powers McKean–Singer vanishing, heat-polynomial invariance, and
    explicit `Mat3C` kernel-jumping invariant index family.
* **BUCKET 2 (Reused repository owners)**:
  - `InfoGeometry.Algebra.FiniteSpin`: `Mat2C`, `Mat3C`.
  - `InfoGeometry.MetaCompiler`: `TypedArchetype`, `Phase`, `executable_certified_compilation`,
    `#register_archetype`, `#audit_archetype`.
  - `InfoGeometry.Causal.FiniteDependencyCompiler` & `ProofCarryingSchedule`:
    `compile`, `ValidSchedule`, `ProofRules`.
* **BUCKET 3 (Explicit hypotheses / scope)**:
  - Cayley transform identity holds for arbitrary real frequency `ω : ℝ`; McKean–Singer polynomial
    invariance holds over finite-dimensional matrix rings `Matrix (Fin m) (Fin m) ℂ` for every
    polynomial truncation degree `N : ℕ` without infinite-series convergence assumptions.
-/

set_option autoImplicit false

namespace InfoGeometry.OperatorAlgebra.FreedWickReflectionAndTopologicalIndexPoset

open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.ProofCarryingSchedule
open InfoGeometry.MetaCompiler

section ScalarHelpers

private theorem scalar_conj_mul_re_normSq (z : ℂ) :
    (star z * z).re = Complex.normSq z := by
  have h1 : star z = starRingEnd ℂ z := rfl
  rw [h1, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem scalar_zero_of_normSq_zero {z : ℂ} (hz : Complex.normSq z = 0) :
    z = 0 := by
  have h1 := Complex.normSq_eq_zero.mp hz
  exact h1

private theorem scalar_neg_two_lt_zero : (-(2 : ℝ)) < 0 := by
  norm_num

private theorem scalar_euclid_trace_lt {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ < 1) :
    1 + γ * γ < 2 := by
  nlinarith [h0, h1]

private theorem scalar_cayley_denom_ne_zero (ω : ℝ) :
    (1 : ℂ) + (ω : ℂ) ^ 2 ≠ 0 := by
  have hr : (0 : ℝ) < 1 + ω ^ 2 := by positivity
  have hc : ((1 + ω ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  push_cast at hc
  exact hc

private theorem scalar_conj_cayley_denom_inv (ω : ℝ) :
    star (((1 : ℂ) + (ω : ℂ) ^ 2)⁻¹) = ((1 : ℂ) + (ω : ℂ) ^ 2)⁻¹ := by
  have hr : ((1 + ω ^ 2 : ℝ) : ℂ) = (1 : ℂ) + (ω : ℂ) ^ 2 := by push_cast; rfl
  rw [← hr, ← Complex.ofReal_inv]
  exact Complex.conj_ofReal ((1 + ω ^ 2)⁻¹)

private theorem scalar_cayley_diag_unitary (ω : ℝ) :
    let d : ℂ := ((1 : ℂ) + (ω : ℂ) ^ 2)⁻¹
    star (d * (1 - (ω : ℂ) ^ 2)) * (d * (1 - (ω : ℂ) ^ 2)) +
      star (d * (-2 * Complex.I * (ω : ℂ))) * (d * (-2 * Complex.I * (ω : ℂ))) = 1 := by
  intro d
  have hd : star d = d := scalar_conj_cayley_denom_inv ω
  have hne : (1 : ℂ) + (ω : ℂ) ^ 2 ≠ 0 := scalar_cayley_denom_ne_zero ω
  have hStar1 : star (1 - (ω : ℂ) ^ 2) = 1 - (ω : ℂ) ^ 2 := by
    simp [Complex.conj_ofReal]
  have hStar2 : star (-2 * Complex.I * (ω : ℂ)) = 2 * Complex.I * (ω : ℂ) := by
    simp [Complex.conj_ofReal]
  simp only [star_mul, hd, hStar1, hStar2]
  dsimp [d]
  field_simp [hne]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem scalar_cayley_off_unitary (ω : ℝ) :
    let d : ℂ := ((1 : ℂ) + (ω : ℂ) ^ 2)⁻¹
    star (d * (1 - (ω : ℂ) ^ 2)) * (d * (-2 * Complex.I * (ω : ℂ))) +
      star (d * (-2 * Complex.I * (ω : ℂ))) * (d * (1 - (ω : ℂ) ^ 2)) = 0 := by
  intro d
  have hd : star d = d := scalar_conj_cayley_denom_inv ω
  have hStar1 : star (1 - (ω : ℂ) ^ 2) = 1 - (ω : ℂ) ^ 2 := by
    simp [Complex.conj_ofReal]
  have hStar2 : star (-2 * Complex.I * (ω : ℂ)) = 2 * Complex.I * (ω : ℂ) := by
    simp [Complex.conj_ofReal]
  simp only [star_mul, hd, hStar1, hStar2]
  ring

private theorem scalar_cayley_lhs_diag (ω : ℝ) :
    let d : ℂ := ((1 : ℂ) + (ω : ℂ) ^ 2)⁻¹
    1 * (d * (1 - (ω : ℂ) ^ 2)) +
      (Complex.I * (ω : ℂ)) * (d * (-2 * Complex.I * (ω : ℂ))) = 1 := by
  intro d
  have hne : (1 : ℂ) + (ω : ℂ) ^ 2 ≠ 0 := scalar_cayley_denom_ne_zero ω
  dsimp [d]
  field_simp [hne]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem scalar_cayley_lhs_off (ω : ℝ) :
    let d : ℂ := ((1 : ℂ) + (ω : ℂ) ^ 2)⁻¹
    1 * (d * (-2 * Complex.I * (ω : ℂ))) +
      (Complex.I * (ω : ℂ)) * (d * (1 - (ω : ℂ) ^ 2)) = -(Complex.I * (ω : ℂ)) := by
  intro d
  have hne : (1 : ℂ) + (ω : ℂ) ^ 2 ≠ 0 := scalar_cayley_denom_ne_zero ω
  dsimp [d]
  field_simp [hne]
  ring

private theorem scalar_double_half_zero {z : ℂ} (hz : z = -z) : z = 0 := by
  have h2 : (2 : ℂ) * z = 0 := by
    calc
      (2 : ℂ) * z = z + z := two_mul z
      _ = z + (-z) := by conv_lhs => rhs; rw [hz]
      _ = 0 := add_neg_cancel z
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

end ScalarHelpers

/-- Complex `2 × 2` block matrix over `Mat2C`. -/
abbrev NestedMat2C := Matrix (Fin 2) (Fin 2) Mat2C

section NoncommutativityWitnesses

/-- Canonical Pauli matrices in `Mat2C`. -/
def pauliX2 : Mat2C := !![0, 1; 1, 0]
def pauliZ2 : Mat2C := !![1, 0; 0, -1]

/-- Closed `Mat2C` noncommutativity witness (`pauliX2 * pauliZ2 ≠ pauliZ2 * pauliX2`). -/
theorem mat2c_freed_noncommutative :
    ∃ A B : Mat2C, A * B ≠ B * A := by
  refine ⟨pauliX2, pauliZ2, ?_⟩
  intro hEq
  have h01 := congrArg (fun M : Mat2C => M 0 1) hEq
  simp [pauliX2, pauliZ2, Matrix.mul_apply, Fin.sum_univ_two] at h01
  exact (by norm_num : (-1 : ℂ) ≠ 1) h01

/-- Closed `NestedMat2C = Matrix (Fin 2) (Fin 2) Mat2C` noncommutativity witness. -/
theorem nestedMat2c_freed_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) Mat2C, A * B ≠ B * A := by
  let A : Matrix (Fin 2) (Fin 2) Mat2C := !![0, (1 : Mat2C); (1 : Mat2C), 0]
  let B : Matrix (Fin 2) (Fin 2) Mat2C := !![(1 : Mat2C), 0; 0, -(1 : Mat2C)]
  refine ⟨A, B, ?_⟩
  intro hEq
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) Mat2C => (M 0 1) 0 0) hEq
  simp [A, B, Matrix.mul_apply, Fin.sum_univ_two] at h01
  exact (by norm_num : (-1 : ℂ) ≠ 1) h01

/-- Closed `Mat3C = Matrix (Fin 3) (Fin 3) ℂ` noncommutativity witness. -/
theorem mat3c_freed_noncommutative :
    ∃ A B : Mat3C, A * B ≠ B * A := by
  let A : Mat3C := !![0, 0, 1; 0, 0, 0; 1, 0, 0]
  let B : Mat3C := !![1, 0, 0; 0, 1, 0; 0, 0, -1]
  refine ⟨A, B, ?_⟩
  intro hEq
  have h02 := congrArg (fun M : Mat3C => M 0 2) hEq
  simp [A, B, Matrix.mul_apply, Fin.sum_univ_three] at h02
  exact (by norm_num : (-1 : ℂ) ≠ 1) h02

end NoncommutativityWitnesses

/-! ## $\mathcal{F}_1$: Osterwalder–Schrader Reflection Positivity & Chiral Cut -/

section ArchetypeF1_OSReflection

/-- Involutive reflection conjugation `X ↦ η * X * η` on `Matrix (Fin n) (Fin n) ℂ`. -/
def osReflect {n : ℕ} (η X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  η * X * η

/-- Osterwalder–Schrader trace pairing `tr((osReflect η X)ᴴ Y)`. -/
def osTraceForm {n : ℕ} (η X Y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  Matrix.trace (star (osReflect η X) * Y)

theorem pauliX2_sq : pauliX2 * pauliX2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX2, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliZ2_sq : pauliZ2 * pauliZ2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ2, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliZ2_pauliX2_anticomm :
    pauliZ2 * pauliX2 = -(pauliX2 * pauliZ2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX2, pauliZ2, Matrix.mul_apply, Fin.sum_univ_two]

theorem osReflect_involutive {n : ℕ} (η X : Matrix (Fin n) (Fin n) ℂ)
    (hη : η * η = 1) :
    osReflect η (osReflect η X) = X := by
  dsimp [osReflect]
  calc
    η * (η * X * η) * η = (η * η) * X * (η * η) := by noncomm_ring
    _ = 1 * X * 1 := by rw [hη]
    _ = X := by noncomm_ring

theorem trace_star_mul_self_re {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.trace (star X * X)).re =
      ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (X j i) := by
  dsimp [Matrix.trace, Matrix.diag]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mul_apply, Matrix.star_apply]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact scalar_conj_mul_re_normSq (X j i)

/-- **Osterwalder–Schrader Positivity on Reflection-Even Sector**:
whenever `osReflect η X = X`, `(osTraceForm η X X).re ≥ 0` in arbitrary matrix dimension `n`. -/
theorem osTraceForm_nonneg_of_reflect_invariant {n : ℕ}
    (η X : Matrix (Fin n) (Fin n) ℂ) (hRef : osReflect η X = X) :
    0 ≤ (osTraceForm η X X).re := by
  dsimp [osTraceForm]
  rw [hRef, trace_star_mul_self_re]
  refine Finset.sum_nonneg fun i _ => ?_
  exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (X j i)

/-- **Strict Lorentzian / Chiral Reflection Negativity**:
for odd chiral operator `pauliX2` under `η = pauliZ2`, `osReflect pauliZ2 pauliX2 = -pauliX2`
and `(osTraceForm pauliZ2 pauliX2 pauliX2).re = -2 < 0`, separating Euclidean from Lorentzian signature. -/
theorem osTraceForm_pauliZ2_pauliX2_negative :
    osReflect pauliZ2 pauliX2 = -pauliX2 ∧
      (osTraceForm pauliZ2 pauliX2 pauliX2).re = -(2 : ℝ) ∧
      (osTraceForm pauliZ2 pauliX2 pauliX2).re < 0 := by
  have hRef : osReflect pauliZ2 pauliX2 = -pauliX2 := by
    dsimp [osReflect]
    calc
      pauliZ2 * pauliX2 * pauliZ2 = -(pauliX2 * pauliZ2) * pauliZ2 := by
          rw [pauliZ2_pauliX2_anticomm]
      _ = -(pauliX2 * (pauliZ2 * pauliZ2)) := by noncomm_ring
      _ = -(pauliX2 * 1) := by rw [pauliZ2_sq]
      _ = -pauliX2 := by noncomm_ring
  have hVal : (osTraceForm pauliZ2 pauliX2 pauliX2).re = -(2 : ℝ) := by
    dsimp [osTraceForm]
    rw [hRef]
    have hStar : star pauliX2 = pauliX2 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pauliX2, Matrix.star_apply]
    rw [star_neg, hStar, neg_mul, pauliX2_sq, Matrix.trace_neg, Matrix.trace_one,
      Fintype.card_fin]
    norm_num
  refine ⟨hRef, hVal, ?_⟩
  rw [hVal]
  exact scalar_neg_two_lt_zero

end ArchetypeF1_OSReflection

/-! ## $\mathcal{F}_2$: Euclidean Contractive Semigroup vs Lorentzian Cayley Unitary -/

section ArchetypeF2_WickCayleyDichotomy

/-- Damped Euclidean transfer step `diag(1, γ)` for `γ : ℝ`. -/
noncomputable def euclidStep2 (γ : ℝ) : Mat2C :=
  !![(1 : ℂ), 0; 0, (γ : ℂ)]

/-- Explicit Cayley unitary evolution `((1 - i ω σₓ)(1 + i ω σₓ)⁻¹)` in `Mat2C`. -/
noncomputable def cayleyStep2 (ω : ℝ) : Mat2C :=
  let d : ℂ := ((1 : ℂ) + (ω : ℂ) ^ 2)⁻¹
  !![d * (1 - (ω : ℂ) ^ 2), d * (-2 * Complex.I * (ω : ℂ));
     d * (-2 * Complex.I * (ω : ℂ)), d * (1 - (ω : ℂ) ^ 2)]

/-- Noncommuting rank-1 orthogonal projectors witnessing quantum measurement incompatibility. -/
def projDiag2 : Mat2C := !![1, 0; 0, 0]
noncomputable def projPlus2 : Mat2C := !![(1 / 2 : ℂ), (1 / 2 : ℂ); (1 / 2 : ℂ), (1 / 2 : ℂ)]

theorem euclidStep2_contractive_trace {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ < 1) :
    (Matrix.trace (star (euclidStep2 γ) * euclidStep2 γ)).re = 1 + γ * γ ∧
      (Matrix.trace (star (euclidStep2 γ) * euclidStep2 γ)).re < 2 := by
  have hTr : (Matrix.trace (star (euclidStep2 γ) * euclidStep2 γ)).re = 1 + γ * γ := by
    dsimp [euclidStep2, Matrix.trace, Matrix.diag]
    simp only [Fin.sum_univ_two, Matrix.mul_apply, Matrix.star_apply]
    norm_num [Complex.add_re, Complex.mul_re]
  refine ⟨hTr, ?_⟩
  rw [hTr]
  exact scalar_euclid_trace_lt h0 h1

theorem cayleyStep2_solves_cayley_and_unitary (ω : ℝ) :
    (1 + (Complex.I * (ω : ℂ)) • pauliX2) * cayleyStep2 ω =
        1 - (Complex.I * (ω : ℂ)) • pauliX2 ∧
      star (cayleyStep2 ω) * cayleyStep2 ω = 1 ∧
      (Matrix.trace (star (cayleyStep2 ω) * cayleyStep2 ω)).re = 2 := by
  have hCay :
      (1 + (Complex.I * (ω : ℂ)) • pauliX2) * cayleyStep2 ω =
        1 - (Complex.I * (ω : ℂ)) • pauliX2 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, pauliX2, cayleyStep2] using
        scalar_cayley_lhs_diag ω
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, pauliX2, cayleyStep2] using
        scalar_cayley_lhs_off ω
    · have h := scalar_cayley_lhs_off ω
      dsimp only at h
      rw [add_comm] at h
      simpa [Matrix.mul_apply, Fin.sum_univ_two, pauliX2, cayleyStep2] using h
    · have h := scalar_cayley_lhs_diag ω
      dsimp only at h
      rw [add_comm] at h
      simpa [Matrix.mul_apply, Fin.sum_univ_two, pauliX2, cayleyStep2] using h
  have hUni : star (cayleyStep2 ω) * cayleyStep2 ω = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      simpa [cayleyStep2] using scalar_cayley_diag_unitary ω
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      simpa [cayleyStep2] using scalar_cayley_off_unitary ω
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      simpa [cayleyStep2, add_comm] using scalar_cayley_off_unitary ω
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      simpa [cayleyStep2, add_comm] using scalar_cayley_diag_unitary ω
  have hTr : (Matrix.trace (star (cayleyStep2 ω) * cayleyStep2 ω)).re = 2 := by
    rw [hUni, Matrix.trace_one, Fintype.card_fin]
    norm_num
  exact ⟨hCay, hUni, hTr⟩

theorem projDiag2_projPlus2_noncomm_idempotents :
    projDiag2 * projDiag2 = projDiag2 ∧
      projPlus2 * projPlus2 = projPlus2 ∧
      projDiag2 * projPlus2 ≠ projPlus2 * projDiag2 := by
  have hp1 : projDiag2 * projDiag2 = projDiag2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [projDiag2, Matrix.mul_apply, Fin.sum_univ_two]
  have hp2 : projPlus2 * projPlus2 = projPlus2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [projPlus2, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  refine ⟨hp1, hp2, ?_⟩
  intro hEq
  have h01 := congrArg (fun M : Mat2C => M 0 1) hEq
  simp [projDiag2, projPlus2, Matrix.mul_apply, Fin.sum_univ_two] at h01

end ArchetypeF2_WickCayleyDichotomy

/-! ## $\mathcal{F}_3$: Projective 2-Cocycle Obstruction & Doubled Kronecker Cancellation -/

section ArchetypeF3_ProjectiveAnomaly

/-- Algebraic coboundary rescaling `u' g = (b g : R) • (u g : A)` cancels identically in any
group commutator quotient, preserving the projective 2-cocycle asymmetry factor. -/
theorem coboundary_commutator_skewness_invariant
    {G R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (u : G → Aˣ) (b : G → Rˣ) (g h : G) {zgh zhg : Rˣ} {w : Aˣ}
    (h1 : (u g : A) * (u h : A) = (zgh : R) • (w : A))
    (h2 : (u h : A) * (u g : A) = (zhg : R) • (w : A))
    (hComm : ((b g : R) • (u g : A)) * ((b h : R) • (u h : A)) =
      ((b h : R) • (u h : A)) * ((b g : R) • (u g : A))) :
    ((zgh : R) - (zhg : R)) • (1 : A) = 0 := by
  have hL :
      ((b g : R) • (u g : A)) * ((b h : R) • (u h : A)) =
        ((b g : R) * (b h : R) * (zgh : R)) • (w : A) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, h1, smul_smul, smul_smul]
  have hR :
      ((b h : R) • (u h : A)) * ((b g : R) • (u g : A)) =
        ((b g : R) * (b h : R) * (zhg : R)) • (w : A) := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, h2, smul_smul, smul_smul,
      mul_comm (b h : R) (b g : R)]
  rw [hL, hR] at hComm
  have hw := congrArg (fun M : A => M * (w⁻¹ : Aˣ)) hComm
  simp only [Algebra.smul_mul_assoc, Units.mul_inv] at hw
  have hbg := congrArg (fun M : A => (((b g)⁻¹ * (b h)⁻¹ : Rˣ) : R) • M) hw
  simp only [smul_smul] at hbg
  have hL1 : (((b g)⁻¹ * (b h)⁻¹ : Rˣ) : R) * ((b g : R) * (b h : R) * (zgh : R)) = (zgh : R) := by
    calc
      (((b g)⁻¹ * (b h)⁻¹ : Rˣ) : R) * ((b g : R) * (b h : R) * (zgh : R))
          = ((((b g : R) * (((b g)⁻¹ : Rˣ) : R)) * ((b h : R) * (((b h)⁻¹ : Rˣ) : R))) * (zgh : R)) := by
            rw [Units.val_mul]; ring
      _ = (1 * 1) * (zgh : R) := by
            rw [← Units.val_mul, mul_inv_cancel, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      _ = (zgh : R) := by ring
  have hR1 : (((b g)⁻¹ * (b h)⁻¹ : Rˣ) : R) * ((b g : R) * (b h : R) * (zhg : R)) = (zhg : R) := by
    calc
      (((b g)⁻¹ * (b h)⁻¹ : Rˣ) : R) * ((b g : R) * (b h : R) * (zhg : R))
          = ((((b g : R) * (((b g)⁻¹ : Rˣ) : R)) * ((b h : R) * (((b h)⁻¹ : Rˣ) : R))) * (zhg : R)) := by
            rw [Units.val_mul]; ring
      _ = (1 * 1) * (zhg : R) := by
            rw [← Units.val_mul, mul_inv_cancel, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      _ = (zhg : R) := by ring
  rw [hL1, hR1] at hbg
  rw [sub_smul, sub_eq_zero]
  exact hbg

private theorem zmod2_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx : x.val < 2 := ZMod.val_lt x
  have h01 : x.val = 0 ∨ x.val = 1 := by omega
  rcases h01 with h0 | h1
  · left
    exact ZMod.val_injective 2 (h0.trans (rfl : (0 : ZMod 2).val = 0).symm)
  · right
    exact ZMod.val_injective 2 (h1.trans (rfl : (1 : ZMod 2).val = 1).symm)

/-- Explicit projective Pauli lift of `ZMod 2 × ZMod 2` into `(Mat2C)ˣ`. -/
def pauliProjMat (g : ZMod 2 × ZMod 2) : Mat2C :=
  if g.1 = 0 then (if g.2 = 0 then 1 else pauliZ2)
  else (if g.2 = 0 then pauliX2 else pauliX2 * pauliZ2)

theorem pauliProjMat_mul_inv (g : ZMod 2 × ZMod 2) :
    pauliProjMat g * (if g.1 = 0 then pauliProjMat g else
      if g.2 = 0 then pauliX2 else pauliZ2 * pauliX2) = 1 ∧
    (if g.1 = 0 then pauliProjMat g else
      if g.2 = 0 then pauliX2 else pauliZ2 * pauliX2) * pauliProjMat g = 1 := by
  rcases g with ⟨g1, g2⟩
  rcases zmod2_zero_or_one g1 with rfl | rfl <;> rcases zmod2_zero_or_one g2 with rfl | rfl
  · simp [pauliProjMat]
  · simp [pauliProjMat, pauliZ2_sq]
  · simp [pauliProjMat, pauliX2_sq]
  · simp only [pauliProjMat, one_ne_zero, ite_false]
    constructor
    · calc
        pauliX2 * pauliZ2 * (pauliZ2 * pauliX2)
            = pauliX2 * (pauliZ2 * pauliZ2) * pauliX2 := by noncomm_ring
        _ = pauliX2 * 1 * pauliX2 := by rw [pauliZ2_sq]
        _ = pauliX2 * pauliX2 := by noncomm_ring
        _ = 1 := pauliX2_sq
    · calc
        pauliZ2 * pauliX2 * (pauliX2 * pauliZ2)
            = pauliZ2 * (pauliX2 * pauliX2) * pauliZ2 := by noncomm_ring
        _ = pauliZ2 * 1 * pauliZ2 := by rw [pauliX2_sq]
        _ = pauliZ2 * pauliZ2 := by noncomm_ring
        _ = 1 := pauliZ2_sq

def pauliProjUnit (g : ZMod 2 × ZMod 2) : Mat2Cˣ where
  val := pauliProjMat g
  inv := if g.1 = 0 then pauliProjMat g else
    if g.2 = 0 then pauliX2 else pauliZ2 * pauliX2
  val_inv := (pauliProjMat_mul_inv g).1
  inv_val := (pauliProjMat_mul_inv g).2

/-- **No-Coboundary Projective Anomaly Theorem**:
under ANY `ℂˣ` phase redefinition `b : ZMod 2 × ZMod 2 → ℂˣ`, the Pauli generators
`(1, 0)` and `(0, 1)` cannot be made to commute in `Mat2C`. -/
theorem pauliProjUnit_anomaly_irremovable (b : ZMod 2 × ZMod 2 → ℂˣ) :
    ((b (1, 0) : ℂ) • (pauliProjUnit (1, 0) : Mat2C)) *
        ((b (0, 1) : ℂ) • (pauliProjUnit (0, 1) : Mat2C)) ≠
      ((b (0, 1) : ℂ) • (pauliProjUnit (0, 1) : Mat2C)) *
        ((b (1, 0) : ℂ) • (pauliProjUnit (1, 0) : Mat2C)) := by
  intro hComm
  let g10 : ZMod 2 × ZMod 2 := (1, 0)
  let g01 : ZMod 2 × ZMod 2 := (0, 1)
  let w : Mat2Cˣ := ⟨pauliX2 * pauliZ2, pauliZ2 * pauliX2,
    by
      calc (pauliX2 * pauliZ2) * (pauliZ2 * pauliX2)
          = pauliX2 * (pauliZ2 * pauliZ2) * pauliX2 := by noncomm_ring
        _ = 1 := by rw [pauliZ2_sq]; simp [pauliX2_sq],
    by
      calc (pauliZ2 * pauliX2) * (pauliX2 * pauliZ2)
          = pauliZ2 * (pauliX2 * pauliX2) * pauliZ2 := by noncomm_ring
        _ = 1 := by rw [pauliX2_sq]; simp [pauliZ2_sq]⟩
  have h1 : (pauliProjUnit g10 : Mat2C) * (pauliProjUnit g01 : Mat2C) =
      ((1 : ℂˣ) : ℂ) • (w : Mat2C) := by
    simp [pauliProjUnit, pauliProjMat, g10, g01, w]
  have h2 : (pauliProjUnit g01 : Mat2C) * (pauliProjUnit g10 : Mat2C) =
      ((-1 : ℂˣ) : ℂ) • (w : Mat2C) := by
    simp only [pauliProjUnit, pauliProjMat, g10, g01, w, one_ne_zero,
      ite_true, ite_false, Units.val_neg, Units.val_one, neg_smul, one_smul]
    exact pauliZ2_pauliX2_anticomm
  have hContra := coboundary_commutator_skewness_invariant pauliProjUnit b g10 g01 h1 h2 hComm
  have hEntry := congrArg (fun M : Mat2C => M 0 0) hContra
  simp [Matrix.smul_apply, smul_eq_mul] at hEntry

/-- Kronecker block tensor `M ⊗ M` inside `NestedMat2C = Matrix (Fin 2) (Fin 2) Mat2C`. -/
def kronSquare2C (M : Mat2C) : NestedMat2C :=
  !![M 0 0 • M, M 0 1 • M;
     M 1 0 • M, M 1 1 • M]

theorem kronSquare2C_mul (A B : Mat2C) :
    kronSquare2C A * kronSquare2C B = kronSquare2C (A * B) := by
  have fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
    fin_cases i
    · left; rfl
    · right; rfl
  refine Matrix.ext fun p q => ?_
  rcases fin2_cases p with rfl | rfl <;> rcases fin2_cases q with rfl | rfl <;>
    simp only [kronSquare2C, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      smul_mul_smul_comm, ← add_smul]

theorem kronSquare2C_one : kronSquare2C (1 : Mat2C) = 1 := by
  ext p q i j
  fin_cases p <;> fin_cases q <;> fin_cases i <;> fin_cases j <;>
    simp [kronSquare2C]

private theorem kronSquare2C_neg (M : Mat2C) : kronSquare2C (-M) = kronSquare2C M := by
  ext p q i j
  fin_cases p <;> fin_cases q <;>
    simp [kronSquare2C]

private theorem pauliProjMat_add_mul (g h : ZMod 2 × ZMod 2) :
    pauliProjMat g * pauliProjMat h = pauliProjMat (g + h) ∨
      pauliProjMat g * pauliProjMat h = -pauliProjMat (g + h) := by
  have h20 : (1 : ZMod 2) + 1 = 0 := by decide
  have hp00 : pauliProjMat (0, 0) = 1 := by simp [pauliProjMat]
  have hp01 : pauliProjMat (0, 1) = pauliZ2 := by simp [pauliProjMat]
  have hp10 : pauliProjMat (1, 0) = pauliX2 := by simp [pauliProjMat]
  have hp11 : pauliProjMat (1, 1) = pauliX2 * pauliZ2 := by simp [pauliProjMat]
  have hXZ_Z : (pauliX2 * pauliZ2) * pauliZ2 = pauliX2 := by
    rw [mul_assoc, pauliZ2_sq, mul_one]
  have hZ_XZ : pauliZ2 * (pauliX2 * pauliZ2) = -pauliX2 := by
    rw [← mul_assoc, pauliZ2_pauliX2_anticomm, neg_mul, mul_assoc, pauliZ2_sq, mul_one]
  have hX_XZ : pauliX2 * (pauliX2 * pauliZ2) = pauliZ2 := by
    rw [← mul_assoc, pauliX2_sq, one_mul]
  have hXZ_X : (pauliX2 * pauliZ2) * pauliX2 = -pauliZ2 := by
    rw [mul_assoc, pauliZ2_pauliX2_anticomm, mul_neg, ← mul_assoc, pauliX2_sq, one_mul]
  have hXZ_XZ : (pauliX2 * pauliZ2) * (pauliX2 * pauliZ2) = -1 := by
    calc
      (pauliX2 * pauliZ2) * (pauliX2 * pauliZ2)
          = pauliX2 * (pauliZ2 * pauliX2) * pauliZ2 := by noncomm_ring
      _ = -(pauliX2 * pauliX2 * (pauliZ2 * pauliZ2)) := by
            rw [pauliZ2_pauliX2_anticomm]; noncomm_ring
      _ = -1 := by rw [pauliX2_sq, pauliZ2_sq]; noncomm_ring
  rcases g with ⟨g1, g2⟩
  rcases h with ⟨h1, h2⟩
  rcases zmod2_zero_or_one g1 with rfl | rfl <;>
    rcases zmod2_zero_or_one g2 with rfl | rfl <;>
    rcases zmod2_zero_or_one h1 with rfl | rfl <;>
    rcases zmod2_zero_or_one h2 with rfl | rfl
  all_goals
    repeat first
      | rw [Prod.mk_add_mk]
      | rw [add_zero]
      | rw [zero_add]
      | rw [h20]
    repeat first
      | rw [hp00]
      | rw [hp01]
      | rw [hp10]
      | rw [hp11]
    repeat first
      | rw [one_mul]
      | rw [mul_one]
      | rw [pauliZ2_sq]
      | rw [pauliX2_sq]
      | rw [pauliZ2_pauliX2_anticomm]
      | rw [hXZ_Z]
      | rw [hZ_XZ]
      | rw [hX_XZ]
      | rw [hXZ_X]
      | rw [hXZ_XZ]
    first | exact Or.inl rfl | exact Or.inr rfl

private theorem pauliProjMat_self_kron (g : ZMod 2 × ZMod 2) :
    kronSquare2C (pauliProjMat g * pauliProjMat g) = 1 := by
  have h20 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases pauliProjMat_add_mul g g with hEq | hNeg
  · have hAdd0 : g + g = 0 := by
      rcases g with ⟨g1, g2⟩
      rcases zmod2_zero_or_one g1 with rfl | rfl <;> rcases zmod2_zero_or_one g2 with rfl | rfl <;>
        simp [h20]
    rw [hEq, hAdd0]
    simpa [pauliProjMat] using kronSquare2C_one
  · have hAdd0 : g + g = 0 := by
      rcases g with ⟨g1, g2⟩
      rcases zmod2_zero_or_one g1 with rfl | rfl <;> rcases zmod2_zero_or_one g2 with rfl | rfl <;>
        simp [h20]
    rw [hNeg, kronSquare2C_neg, hAdd0]
    simpa [pauliProjMat] using kronSquare2C_one

/-- Unit embedding of `pauliProjUnit g ⊗ pauliProjUnit g` into `(NestedMat2C)ˣ`. -/
def doubledPauliUnit (g : ZMod 2 × ZMod 2) : NestedMat2Cˣ where
  val := kronSquare2C (pauliProjMat g)
  inv := kronSquare2C (pauliProjMat g)
  val_inv := by
    rw [kronSquare2C_mul]
    exact pauliProjMat_self_kron g
  inv_val := by
    rw [kronSquare2C_mul]
    exact pauliProjMat_self_kron g

/-- **Genuine Linear Group Homomorphism via Anomaly Doubling**:
tensor-doubling cancels the `ℤ₂` projective sign `(-1) * (-1) = +1`, producing a genuine
monoid homomorphism `Multiplicative (ZMod 2 × ZMod 2) →* (NestedMat2C)ˣ` whose generators
remain strictly non-scalar block matrices. -/
def doubledPauliHom :
    Multiplicative (ZMod 2 × ZMod 2) →* NestedMat2Cˣ where
  toFun g := doubledPauliUnit (Multiplicative.toAdd g)
  map_one' := by
    apply Units.ext
    dsimp [doubledPauliUnit, pauliProjMat]
    simpa using kronSquare2C_one
  map_mul' g h := by
    apply Units.ext
    dsimp [doubledPauliUnit]
    rw [kronSquare2C_mul]
    rcases pauliProjMat_add_mul (Multiplicative.toAdd g) (Multiplicative.toAdd h) with hEq | hNeg
    · rw [hEq]
    · rw [hNeg, kronSquare2C_neg]

theorem doubledPauliHom_nontrivial_action :
    (doubledPauliHom (Multiplicative.ofAdd (1, 0)) : NestedMat2C) ≠ 1 ∧
      (doubledPauliHom (Multiplicative.ofAdd (0, 1)) : NestedMat2C) ≠ 1 := by
  constructor
  · intro h1
    have hEntry := congrArg (fun M : NestedMat2C => (M 0 0) 0 0) h1
    simp [doubledPauliHom, doubledPauliUnit, pauliProjMat,
      kronSquare2C, pauliX2] at hEntry
  · intro h1
    have hEntry := congrArg (fun M : NestedMat2C => (M 0 0) 1 1) h1
    simp [doubledPauliHom, doubledPauliUnit, pauliProjMat,
      kronSquare2C, pauliZ2] at hEntry
    norm_num at hEntry

end ArchetypeF3_ProjectiveAnomaly

/-! ## $\mathcal{F}_4$: Hilbert Self-Adjoint Nilpotent No-Go vs Krein-Hermitian BRST -/

section ArchetypeF4_KreinBrstCohomology

/-- **Hilbert Self-Adjoint Nilpotent No-Go Theorem**:
in arbitrary matrix dimension `n`, any Hilbert self-adjoint operator `star Q = Q`
satisfying `Q * Q = 0` must vanish identically. -/
theorem hilbert_selfAdj_nilpotent_zero {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (hAdj : star Q = Q) (hNil : Q * Q = 0) :
    Q = 0 := by
  have hTr0 : (Matrix.trace (star Q * Q)).re = 0 := by
    rw [hAdj, hNil, Matrix.trace_zero, Complex.zero_re]
  rw [trace_star_mul_self_re] at hTr0
  have hOuter : ∀ i ∈ Finset.univ,
      (∑ j : Fin n, Complex.normSq (Q j i)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (Q j i)).mp hTr0
  ext j i
  have hInner : ∀ k ∈ Finset.univ, Complex.normSq (Q k i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun k _ => Complex.normSq_nonneg (Q k i)).mp
      (hOuter i (Finset.mem_univ i))
  exact scalar_zero_of_normSq_zero (hInner j (Finset.mem_univ j))

/-- Krein-Hermitian nilpotent BRST differential `brstQ2`, grading `pauliZ2`, and metric `pauliX2`. -/
def brstQ2 : Mat2C := !![0, 1; 0, 0]
def brstQ2Star : Mat2C := !![0, 0; 1, 0]

/-- **Krein-Hermitian BRST Escape & Gauge-Fixed Hodge Resolution**:
under indefinite metric `η = pauliX2` and grading `γ = pauliZ2`, `brstQ2 ≠ 0` is
Krein-self-adjoint (`η (star Q) η = Q`), nilpotent (`Q² = 0`), odd (`γ Q + Q γ = 0`),
and admits the gauge-fixing identity `Q Qᴴ + Qᴴ Q = 1`. -/
theorem krein_brst_witness :
    brstQ2 ≠ 0 ∧
      brstQ2 * brstQ2 = 0 ∧
      pauliX2 * star brstQ2 * pauliX2 = brstQ2 ∧
      pauliZ2 * brstQ2 + brstQ2 * pauliZ2 = 0 ∧
      brstQ2 * brstQ2Star + brstQ2Star * brstQ2 = 1 := by
  have hNz : brstQ2 ≠ 0 := by
    intro h0
    have h01 := congrArg (fun M : Mat2C => M 0 1) h0
    simp [brstQ2] at h01
  have hNil : brstQ2 * brstQ2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [brstQ2, Matrix.mul_apply, Fin.sum_univ_two]
  have hStar : star brstQ2 = brstQ2Star := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [brstQ2, brstQ2Star]
  have hKrein : pauliX2 * star brstQ2 * pauliX2 = brstQ2 := by
    rw [hStar]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliX2, brstQ2, brstQ2Star]
  have hOdd : pauliZ2 * brstQ2 + brstQ2 * pauliZ2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliZ2, brstQ2]
  have hHodge : brstQ2 * brstQ2Star + brstQ2Star * brstQ2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [brstQ2, brstQ2Star]
  exact ⟨hNz, hNil, hKrein, hOdd, hHodge⟩

end ArchetypeF4_KreinBrstCohomology

/-! ## $\mathcal{F}_5$: McKean–Singer Supertrace & Jumping-Kernel Dirac Index -/

section ArchetypeF5_McKeanSingerIndex

/-- Graded supertrace `tr(γ * A)` on `Matrix (Fin m) (Fin m) ℂ`. -/
def superTrace {m : ℕ} (γ A : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  Matrix.trace (γ * A)

/-- **All-Powers McKean–Singer Supertrace Vanishing Theorem**:
for arbitrary dimension `m : ℕ` and arbitrary odd operator `D` (`γ D + D γ = 0`),
`superTrace γ (D ^ (k + 1)) = 0` for EVERY `k : ℕ`. -/
theorem superTrace_anticomm_pow_succ {m : ℕ} (γ D : Matrix (Fin m) (Fin m) ℂ)
    (hAnti : γ * D + D * γ = 0) (k : ℕ) :
    superTrace γ (D ^ (k + 1)) = 0 := by
  dsimp [superTrace]
  have hγD : γ * D = -(D * γ) := eq_neg_of_add_eq_zero_left hAnti
  have hPowL : γ * D ^ (k + 1) = -(D * (γ * D ^ k)) := by
    rw [pow_succ', ← mul_assoc, hγD, neg_mul, mul_assoc]
  have hSelfNeg : Matrix.trace (γ * D ^ (k + 1)) = -Matrix.trace (γ * D ^ (k + 1)) := by
    calc
      Matrix.trace (γ * D ^ (k + 1)) = Matrix.trace (-(D * (γ * D ^ k))) := by rw [hPowL]
      _ = -Matrix.trace (D * (γ * D ^ k)) := Matrix.trace_neg _
      _ = -Matrix.trace ((γ * D ^ k) * D) := by rw [Matrix.trace_mul_comm D (γ * D ^ k)]
      _ = -Matrix.trace (γ * (D ^ k * D)) := by rw [mul_assoc]
      _ = -Matrix.trace (γ * D ^ (k + 1)) := by rw [← pow_succ]
  exact scalar_double_half_zero hSelfNeg

/-- Truncated polynomial heat-kernel operator `c₀ 1 + ∑_{k=0}^{N-1} c_{k+1} (-t)^{k+1} D^{2(k+1)}`. -/
def heatKernelPoly {m : ℕ} (N : ℕ) (c : ℕ → ℂ) (t : ℂ)
    (D : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  c 0 • 1 + ∑ k ∈ Finset.range N, (c (k + 1) * (-t) ^ (k + 1)) • D ^ (2 * (k + 1))

/-- **Polynomial McKean–Singer Supertrace Invariance**:
for ALL `N : ℕ`, ALL scale parameters `t : ℂ`, ALL polynomial weights `c`, and ALL odd
operators `D`, `superTrace γ (heatKernelPoly N c t D) = c 0 * Matrix.trace γ`. -/
theorem superTrace_heatKernelPoly_invariant {m : ℕ} (N : ℕ) (c : ℕ → ℂ) (t : ℂ)
    (γ D : Matrix (Fin m) (Fin m) ℂ) (hAnti : γ * D + D * γ = 0) :
    superTrace γ (heatKernelPoly N c t D) = c 0 * Matrix.trace γ := by
  dsimp [superTrace, heatKernelPoly]
  rw [mul_add, Matrix.trace_add, mul_smul_comm, mul_one, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.mul_sum, Matrix.trace_sum]
  have hZero :
      (∑ x ∈ Finset.range N,
        Matrix.trace (γ * ((c (x + 1) * (-t) ^ (x + 1)) • D ^ (2 * (x + 1))))) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
    have hPow : Matrix.trace (γ * D ^ (2 * k + 1 + 1)) = 0 :=
      superTrace_anticomm_pow_succ γ D hAnti (2 * k + 1)
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, hPow, mul_zero]
  rw [hZero, add_zero]

/-- Explicit `3 × 3` grading `diag(1, 1, -1)` and jumping-kernel self-adjoint Dirac family `diracJump3 s`. -/
def grading3 : Mat3C := !![1, 0, 0; 0, 1, 0; 0, 0, -1]
def diracJump3 (s : ℂ) : Mat3C := !![0, 0, s; 0, 0, 0; star s, 0, 0]

/-- **Kernel-Jumping Self-Adjoint Dirac Index Invariance Theorem**:
1. `diracJump3 s` is self-adjoint and `grading3`-odd for EVERY `s : ℂ`.
2. At `s = 0`, all 3 basis vectors lie in `ker (diracJump3 0)`, whereas for `s ≠ 0` only `![0, 1, 0]` lies in `ker (diracJump3 s)`.
3. Regardless of this `3 → 1` kernel jump and regardless of `N, c, t`, when `c 0 = 1`,
   `superTrace grading3 (heatKernelPoly N c t (diracJump3 s)) = 1`. -/
theorem diracJump3_invariant_index (s : ℂ) (N : ℕ) (c : ℕ → ℂ) (hc0 : c 0 = 1) (t : ℂ) :
    star (diracJump3 s) = diracJump3 s ∧
      grading3 * diracJump3 s + diracJump3 s * grading3 = 0 ∧
      (Matrix.mulVec (diracJump3 0) ![1, 0, 0] = 0 ∧
        Matrix.mulVec (diracJump3 0) ![0, 1, 0] = 0 ∧
        Matrix.mulVec (diracJump3 0) ![0, 0, 1] = 0) ∧
      (s ≠ 0 →
        Matrix.mulVec (diracJump3 s) ![1, 0, 0] ≠ 0 ∧
        Matrix.mulVec (diracJump3 s) ![0, 1, 0] = 0 ∧
        Matrix.mulVec (diracJump3 s) ![0, 0, 1] ≠ 0) ∧
      superTrace grading3 (heatKernelPoly N c t (diracJump3 s)) = 1 := by
  have hAdj : star (diracJump3 s) = diracJump3 s := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diracJump3, Matrix.star_apply]
  have hAnti : grading3 * diracJump3 s + diracJump3 s * grading3 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [grading3, diracJump3]
  have hKer0 :
      Matrix.mulVec (diracJump3 0) ![1, 0, 0] = 0 ∧
        Matrix.mulVec (diracJump3 0) ![0, 1, 0] = 0 ∧
        Matrix.mulVec (diracJump3 0) ![0, 0, 1] = 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;>
      simp [diracJump3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hKerS :
      s ≠ 0 →
        Matrix.mulVec (diracJump3 s) ![1, 0, 0] ≠ 0 ∧
        Matrix.mulVec (diracJump3 s) ![0, 1, 0] = 0 ∧
        Matrix.mulVec (diracJump3 s) ![0, 0, 1] ≠ 0 := by
    intro hs
    refine ⟨?_, ?_, ?_⟩
    · intro h0
      have h2 := congrArg (fun v : Fin 3 → ℂ => v 2) h0
      simp [diracJump3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h2
      exact hs h2
    · ext i
      fin_cases i <;> simp [diracJump3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · intro h0
      have h0e := congrArg (fun v : Fin 3 → ℂ => v 0) h0
      simp [diracJump3, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0e
      exact hs h0e
  have hIdx : superTrace grading3 (heatKernelPoly N c t (diracJump3 s)) = 1 := by
    rw [superTrace_heatKernelPoly_invariant N c t grading3 (diracJump3 s) hAnti, hc0, one_mul]
    dsimp [Matrix.trace, Matrix.diag, grading3]
    simp [Fin.sum_univ_three]
  exact ⟨hAdj, hAnti, hKer0, hKerS, hIdx⟩

end ArchetypeF5_McKeanSingerIndex

/-! ## $\mathcal{F}_6$: 6-Node Diamond Causal Poset & Certified Compilation -/

section CausalPoset

/-- Nodes of the 6-node diamond causal poset $(\mathcal{F}, \preceq)$ for Freed QFT & Index Theory. -/
inductive FreedQFTArchetype
  | F1
  | F2
  | F3
  | F4
  | F5
  | F6
  deriving DecidableEq, Repr, Inhabited

private def freedArchetypeEquivFin : FreedQFTArchetype ≃ Fin 6 where
  toFun
    | .F1 => 0
    | .F2 => 1
    | .F3 => 2
    | .F4 => 3
    | .F5 => 4
    | .F6 => 5
  invFun
    | 0 => .F1
    | 1 => .F2
    | 2 => .F3
    | 3 => .F4
    | 4 => .F5
    | _ => .F6
  left_inv x := by
    cases x <;> rfl
  right_inv i := by
    fin_cases i <;> rfl

instance : Fintype FreedQFTArchetype :=
  Fintype.ofEquiv (Fin 6) freedArchetypeEquivFin.symm

def freedPrerequisites : FreedQFTArchetype → Finset FreedQFTArchetype
  | .F1 => {.F1}
  | .F2 => {.F1, .F2}
  | .F3 => {.F1, .F3}
  | .F4 => {.F1, .F4}
  | .F5 => {.F1, .F2, .F4, .F5}
  | .F6 => {.F1, .F2, .F3, .F4, .F5, .F6}

instance : PartialOrder FreedQFTArchetype where
  le a b := freedPrerequisites a ⊆ freedPrerequisites b
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;> revert hab hba <;> decide

instance : DecidableLE FreedQFTArchetype := fun a b =>
  inferInstanceAs (Decidable (freedPrerequisites a ⊆ freedPrerequisites b))

instance : DecidableLT FreedQFTArchetype := fun a b =>
  decidable_of_iff (a ≤ b ∧ ¬ b ≤ a) lt_iff_le_not_ge.symm

/-- Non-linear diamond incomparabilities among `{F2, F3, F4, F5}`. -/
theorem freed_poset_diamond_incomparabilities :
    (¬ FreedQFTArchetype.F2 ≤ .F4 ∧ ¬ FreedQFTArchetype.F4 ≤ .F2) ∧
      (¬ FreedQFTArchetype.F3 ≤ .F5 ∧ ¬ FreedQFTArchetype.F5 ≤ .F3) := by
  change (¬ freedPrerequisites .F2 ⊆ freedPrerequisites .F4 ∧
      ¬ freedPrerequisites .F4 ⊆ freedPrerequisites .F2) ∧
    (¬ freedPrerequisites .F3 ⊆ freedPrerequisites .F5 ∧
      ¬ freedPrerequisites .F5 ⊆ freedPrerequisites .F3)
  decide

end CausalPoset

section MasterSynthesisAndQMS

/-- **Master Freed Wick-Reflection, Anomaly Cancellation & Index Invariance Synthesis**. -/
theorem master_freed_wick_index_synthesis
    (γ ω : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (b : ZMod 2 × ZMod 2 → ℂˣ)
    (s : ℂ) (N : ℕ) (c : ℕ → ℂ) (hc0 : c 0 = 1) (t : ℂ) :
    (∃ A B : Mat2C, A * B ≠ B * A) ∧
      (∃ A B : NestedMat2C, A * B ≠ B * A) ∧
      (∃ A B : Mat3C, A * B ≠ B * A) ∧
      (0 ≤ (osTraceForm pauliZ2 (1 : Mat2C) (1 : Mat2C)).re ∧
        (osTraceForm pauliZ2 pauliX2 pauliX2).re < 0) ∧
      ((Matrix.trace (star (euclidStep2 γ) * euclidStep2 γ)).re < 2 ∧
        star (cayleyStep2 ω) * cayleyStep2 ω = 1) ∧
      (((b (1, 0) : ℂ) • (pauliProjUnit (1, 0) : Mat2C)) *
          ((b (0, 1) : ℂ) • (pauliProjUnit (0, 1) : Mat2C)) ≠
        ((b (0, 1) : ℂ) • (pauliProjUnit (0, 1) : Mat2C)) *
          ((b (1, 0) : ℂ) • (pauliProjUnit (1, 0) : Mat2C)) ∧
        (doubledPauliHom (Multiplicative.ofAdd (1, 0)) : NestedMat2C) ≠ 1) ∧
      (∀ Q : Mat2C, star Q = Q → Q * Q = 0 → Q = 0) ∧
      brstQ2 ≠ 0 ∧
      superTrace grading3 (heatKernelPoly N c t (diracJump3 s)) = 1 := by
  have h1 := osTraceForm_nonneg_of_reflect_invariant pauliZ2 (1 : Mat2C) (by
    dsimp [osReflect]
    rw [mul_one, pauliZ2_sq])
  have h1neg := osTraceForm_pauliZ2_pauliX2_negative.2.2
  have h2e := (euclidStep2_contractive_trace hγ0 hγ1).2
  have h2l := (cayleyStep2_solves_cayley_and_unitary ω).2.1
  have h3a := pauliProjUnit_anomaly_irremovable b
  have h3d := doubledPauliHom_nontrivial_action.1
  have h4 := krein_brst_witness.1
  have h5 := (diracJump3_invariant_index s N c hc0 t).2.2.2.2
  exact ⟨mat2c_freed_noncommutative, nestedMat2c_freed_noncommutative, mat3c_freed_noncommutative,
    ⟨h1, h1neg⟩, ⟨h2e, h2l⟩, ⟨h3a, h3d⟩,
    fun Q hAdj hNil => hilbert_selfAdj_nilpotent_zero Q hAdj hNil, h4, h5⟩

def freedNodeStatement : FreedQFTArchetype → Prop
  | .F1 =>
      ∀ {n : ℕ} (η X : Matrix (Fin n) (Fin n) ℂ),
        osReflect η X = X → 0 ≤ (osTraceForm η X X).re
  | .F2 =>
      ∀ (γ ω : ℝ), 0 ≤ γ → γ < 1 →
        (Matrix.trace (star (euclidStep2 γ) * euclidStep2 γ)).re < 2 ∧
          star (cayleyStep2 ω) * cayleyStep2 ω = 1
  | .F3 =>
      (∀ b : ZMod 2 × ZMod 2 → ℂˣ,
        ((b (1, 0) : ℂ) • (pauliProjUnit (1, 0) : Mat2C)) *
            ((b (0, 1) : ℂ) • (pauliProjUnit (0, 1) : Mat2C)) ≠
          ((b (0, 1) : ℂ) • (pauliProjUnit (0, 1) : Mat2C)) *
            ((b (1, 0) : ℂ) • (pauliProjUnit (1, 0) : Mat2C))) ∧
        (doubledPauliHom (Multiplicative.ofAdd (1, 0)) : NestedMat2C) ≠ 1
  | .F4 =>
      (∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℂ), star Q = Q → Q * Q = 0 → Q = 0) ∧
        brstQ2 ≠ 0 ∧ brstQ2 * brstQ2 = 0
  | .F5 =>
      ∀ (s : ℂ) (N : ℕ) (c : ℕ → ℂ), c 0 = 1 → ∀ (t : ℂ),
        superTrace grading3 (heatKernelPoly N c t (diracJump3 s)) = 1
  | .F6 =>
      (∃ A B : Mat2C, A * B ≠ B * A) ∧
        (∃ A B : NestedMat2C, A * B ≠ B * A) ∧
        (∃ A B : Mat3C, A * B ≠ B * A) ∧
        (osTraceForm pauliZ2 pauliX2 pauliX2).re < 0 ∧
        superTrace grading3 (heatKernelPoly 2 (fun _ => 1) 7 (diracJump3 0)) = 1

theorem freed_poset_rules : ProofRules freedNodeStatement := by
  intro target _
  cases target
  · intro n η X hRef
    exact osTraceForm_nonneg_of_reflect_invariant η X hRef
  · intro γ ω hγ0 hγ1
    exact ⟨(euclidStep2_contractive_trace hγ0 hγ1).2,
      (cayleyStep2_solves_cayley_and_unitary ω).2.1⟩
  · exact ⟨pauliProjUnit_anomaly_irremovable, doubledPauliHom_nontrivial_action.1⟩
  · exact ⟨fun n Q => hilbert_selfAdj_nilpotent_zero Q,
      krein_brst_witness.1, krein_brst_witness.2.1⟩
  · intro s N c hc0 t
    exact (diracJump3_invariant_index s N c hc0 t).2.2.2.2
  · exact ⟨mat2c_freed_noncommutative, nestedMat2c_freed_noncommutative, mat3c_freed_noncommutative,
      osTraceForm_pauliZ2_pauliX2_negative.2.2,
      (diracJump3_invariant_index 0 2 (fun _ => 1) rfl 7).2.2.2.2⟩

theorem freed_wick_topological_executable_certified_compilation :
    ∃ schedule : List FreedQFTArchetype,
      compile ∅ [.F1, .F2, .F3, .F4, .F5, .F6] = some schedule ∧
      ValidSchedule ∅ schedule ∧
      schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) ∧
      schedule.Nodup ∧
      schedule.length = 6 ∧
      schedule.toFinset = Finset.univ ∧
      ∀ target : FreedQFTArchetype, freedNodeStatement target := by
  have hDist : ([.F1, .F2, .F3, .F4, .F5, .F6] : List FreedQFTArchetype).Nodup := by
    decide
  have hCov : ([.F1, .F2, .F3, .F4, .F5, .F6] : List FreedQFTArchetype).toFinset = Finset.univ := by
    decide
  have hCard : Fintype.card FreedQFTArchetype = 6 := by
    rw [Fintype.card_congr freedArchetypeEquivFin, Fintype.card_fin]
  have hComp := executable_certified_compilation freedNodeStatement freed_poset_rules
    [.F1, .F2, .F3, .F4, .F5, .F6] hDist hCov
  simpa [hCard] using hComp

noncomputable def archF1OSReflection : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.FreedWickReflectionAndTopologicalIndexPoset.archF1OSReflection
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ => freedNodeStatement .F1 ∧ (osTraceForm pauliZ2 pauliX2 pauliX2).re < 0
  evidence := fun _ => by
    refine ⟨?_, osTraceForm_pauliZ2_pauliX2_negative.2.2⟩
    intro n η X hRef
    exact osTraceForm_nonneg_of_reflect_invariant η X hRef

noncomputable def archF2WickCayleyDichotomy : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.FreedWickReflectionAndTopologicalIndexPoset.archF2WickCayleyDichotomy
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ => freedNodeStatement .F2 ∧ projDiag2 * projPlus2 ≠ projPlus2 * projDiag2
  evidence := fun _ => by
    refine ⟨?_, projDiag2_projPlus2_noncomm_idempotents.2.2⟩
    intro γ ω hγ0 hγ1
    exact ⟨(euclidStep2_contractive_trace hγ0 hγ1).2,
      (cayleyStep2_solves_cayley_and_unitary ω).2.1⟩

noncomputable def archF3ProjectiveAnomaly : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.FreedWickReflectionAndTopologicalIndexPoset.archF3ProjectiveAnomaly
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ => freedNodeStatement .F3
  evidence := fun _ => by
    exact ⟨pauliProjUnit_anomaly_irremovable, doubledPauliHom_nontrivial_action.1⟩

noncomputable def archF4KreinBrstCohomology : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.FreedWickReflectionAndTopologicalIndexPoset.archF4KreinBrstCohomology
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ => freedNodeStatement .F4 ∧ brstQ2 * brstQ2Star + brstQ2Star * brstQ2 = 1
  evidence := fun _ => by
    exact ⟨⟨fun n Q => hilbert_selfAdj_nilpotent_zero Q,
      krein_brst_witness.1, krein_brst_witness.2.1⟩, krein_brst_witness.2.2.2.2⟩

noncomputable def archF5McKeanSingerIndex : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.FreedWickReflectionAndTopologicalIndexPoset.archF5McKeanSingerIndex
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ => freedNodeStatement .F5
  evidence := fun _ => by
    intro s N c hc0 t
    exact (diracJump3_invariant_index s N c hc0 t).2.2.2.2

noncomputable def archF6MasterTopologicalIndex : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.FreedWickReflectionAndTopologicalIndexPoset.archF6MasterTopologicalIndex
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ => freedNodeStatement .F6
  evidence := fun _ => by
    exact ⟨mat2c_freed_noncommutative, nestedMat2c_freed_noncommutative, mat3c_freed_noncommutative,
      osTraceForm_pauliZ2_pauliX2_negative.2.2,
      (diracJump3_invariant_index 0 2 (fun _ => 1) rfl 7).2.2.2.2⟩

noncomputable def freedWickTopologicalPosetArchetype : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.FreedWickReflectionAndTopologicalIndexPoset.freedWickTopologicalPosetArchetype
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    (¬ FreedQFTArchetype.F2 ≤ .F4 ∧ ¬ FreedQFTArchetype.F4 ≤ .F2) ∧
      (¬ FreedQFTArchetype.F3 ≤ .F5 ∧ ¬ FreedQFTArchetype.F5 ≤ .F3) ∧
      (∃ schedule : List FreedQFTArchetype,
        compile ∅ [.F1, .F2, .F3, .F4, .F5, .F6] = some schedule ∧
        ValidSchedule ∅ schedule ∧
        schedule.length = 6 ∧
        ∀ target : FreedQFTArchetype, freedNodeStatement target)
  evidence := fun _ => by
    obtain ⟨sch, hComp, hVal, _, _, hLen, _, hAll⟩ :=
      freed_wick_topological_executable_certified_compilation
    exact ⟨freed_poset_diamond_incomparabilities.1,
      freed_poset_diamond_incomparabilities.2, ⟨sch, hComp, hVal, hLen, hAll⟩⟩

#register_archetype archF1OSReflection
#register_archetype archF2WickCayleyDichotomy
#register_archetype archF3ProjectiveAnomaly
#register_archetype archF4KreinBrstCohomology
#register_archetype archF5McKeanSingerIndex
#register_archetype archF6MasterTopologicalIndex
#register_archetype freedWickTopologicalPosetArchetype

#audit_archetype archF1OSReflection
#audit_archetype archF2WickCayleyDichotomy
#audit_archetype archF3ProjectiveAnomaly
#audit_archetype archF4KreinBrstCohomology
#audit_archetype archF5McKeanSingerIndex
#audit_archetype archF6MasterTopologicalIndex
#audit_archetype freedWickTopologicalPosetArchetype

end MasterSynthesisAndQMS

end InfoGeometry.OperatorAlgebra.FreedWickReflectionAndTopologicalIndexPoset
