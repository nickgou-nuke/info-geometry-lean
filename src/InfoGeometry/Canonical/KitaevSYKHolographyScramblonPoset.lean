/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus
import InfoGeometry.Canonical.SYKQuantumChaosMSSBoundCapstone
import InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
import Mathlib.Data.Matrix.Basic

/-!
# Peirce identities motivated by Kitaev's SYK holography seminar

## i. Overview
Collects finite arithmetic and Peirce-ring identities motivated by Alexei Kitaev's April 7, 2015
KITP seminar (*"A simple model of quantum holography, Part 1"*). These statements do not construct
the SYK Hamiltonian, its disorder ensemble, a path integral, or an AdS₂ spacetime. The operator
results are conditional identities in an arbitrary unital ring with an idempotent; their physical
labels are motivation, not consequences of those ring hypotheses. This module also uses existing
MSS/OTOC formulas and the finite Peirce conjugation calculus:

1. **Node `𝔖Yr₁` (`syk_probe_bath_conformal_dimension_lock`):**
   Given the two scalar equations $\Delta_O = 3\Delta_\chi$ and
   $\Delta_\chi + \Delta_O = 1$, proves their unique solution
   $(\Delta_\chi, \Delta_O) = (1/4, 3/4)$. The theorem does not derive those equations from
   SYK correlation functions or Schwinger–Dyson analysis.
2. **Nodes `𝔖Yr₂` & `𝔖Yr₃` (`sl2_rindler_wedge_and_tfd_scramblon_excitation`):**
   Proves Peirce-ring commutator identities in any associative ring `[Ring B]` with idempotent
   `P * P = P`; these are algebraic analogues of the listed Rindler generator relations, not a
   construction of a spacetime or of the Lie algebra representation on a physical state space:
   - Doubled Rindler boost $S_P = \mathtt{invS}\,P = 2P - 1$,
   - Future horizon null shift $N_+ = \mathtt{conePlus}\,P\,X = P X (1 - P)$ ($[S_P, N_+] = +2 N_+$),
   - Past horizon null shift $N_- = \mathtt{coneMinus}\,P\,Y = (1 - P) Y P$ ($[S_P, N_-] = -2 N_-$),
   The theorem proves the stated ring identities, including corner commutators and invariance of
   the even-grade component. It does not define time evolution or a Thermofield Double state.
   The actual `sl₂` bracket `[N₊, N₋] = S_P` requires the additional normalization
   `genV P X Y = 1`, characterized by `peirce_horizon_bracket_matches_boost_iff_unit_foam`.
3. **Nodes `𝔖Yr₄`–`𝔖Yr₆` (`wick_scramblon_ladder_and_shockwave_entanglement_action`):**
   Proves an algebraic Peirce-corner defect formula and identities for two formal shear elements
   $1 + N_+$ and $1 + N_-$. The theorem does not define disorder averages, Wick expectations,
   horizon shockwaves, an action functional, or entanglement entropy.
4. **Node `𝔖Yr₇` (`kitaev_syk_holography_and_elementary_expansion_master_synthesis`):**
   Combines the conditional scalar dimension equations, an MSS-formula identity, Peirce ring
   identities, and the constructive elementary-expansion
   coherator word and unconditional single-commutator diagonal shift
   $\mathtt{evenGrade}\,P\,(\mathtt{cornerConjugation}\,P\,X\,Y\,(P Z P) - P Z P) = [N_-\,(P Z P), \, N_+]$.
5. **Finite matrix vectorization (`finite_matrix_vectorized_commutant_iff`):**
   In a finite matrix algebra over a commutative semiring, equality of left and right
   regular actions on `vec(D)` is equivalent to `H * D = D * H`. This proves only the
   finite algebraic identity; it does not construct a TFD state or a density matrix.
6. **Finite Gibbs half-weight equilibrium (`finite_gibbs_half_weight_vectorized_equilibrium`):**
   For a finite-dimensional Hermitian matrix Hamiltonian, Mathlib's continuous functional
   calculus defines the half-Gibbs weight `exp(-βH/2)` and proves that its square is the
   unnormalized Gibbs density. Its vectorization is invariant under the left/right Hamiltonian
   action. This is a finite matrix equilibrium statement; it does not assert a normalized
   purification or the infinite-dimensional TFD construction. The half-weight is positive
   semidefinite, and its vectorized squared norm equals the Gibbs partition function.

## ii. Key results
- `syk_probe_bath_conformal_dimension_lock` (`𝔖Yr₁`)
- `sl2_rindler_wedge_and_tfd_scramblon_excitation` (`𝔖Yr₂`–`𝔖Yr₃`)
- `peirce_horizon_bracket_matches_boost_iff_unit_foam` (exact condition for the `sl₂` third bracket)
- `finite_matrix_vectorized_commutant_iff` (finite matrix commutant/vectorization equivalence)
- `finite_matrix_vectorize_norm_sq_eq_trace` (finite Hilbert-Schmidt/vectorization identity)
- `finite_gibbs_half_weight_posSemidef` (positive square-root witness)
- `finite_gibbs_half_weight_mul_self_eq_density` (CFC half-weight squares to Gibbs density)
- `finite_gibbs_half_weight_vectorized_equilibrium` (finite CFC half-Gibbs equilibrium)
- `finite_gibbs_half_weight_vectorized_norm_eq_partition` (unnormalized TFD norm/partition identity)
- `wick_scramblon_ladder_and_shockwave_entanglement_action` (`𝔖Yr₄`–`𝔖Yr₆`)
- `two_corner_shockwave_sheet_transfer_round_trip` (`𝔖Yr₆`-B)
- `kitaev_syk_holography_and_elementary_expansion_master_synthesis` (`𝔖Yr₇`)

## iii. Table of contents
- Node `𝔖Yr₁`: Probe ($\Delta = 1/4$) vs. 3-body bath ($\Delta = 3/4$) conformal dimension lock
- Nodes `𝔖Yr₂`–`𝔖Yr₃`: Peirce boost commutators and off-diagonal current identities
- Nodes `𝔖Yr₄`–`𝔖Yr₆`: Wick scramblon ladder defect & two-shockwave entanglement action
- Node `𝔖Yr₇`: Master synthesis with defined scalar-profile identities and constructive elementary expansion
- Finite matrix-entry vectorization and left/right action identity

## iv. References
- Alexei Kitaev, *"A simple model of quantum holography (part 1)"*, KITP Seminar, April 7, 2015
- Juan Maldacena, Stephen H. Shenker, and Douglas Stanford, *A bound on chaos*, JHEP (2016)
- Alexander Grothendieck, *Pursuing Stacks* (1983)

#### BUCKET 1: CLOSED FINITE THEOREMS
- `finite_matrix_vectorized_commutant_iff`
- `finite_matrix_vectorize_norm_sq_eq_trace`
- `finite_gibbs_half_weight_posSemidef`
- `finite_gibbs_half_weight_mul_self_eq_density`
- `finite_gibbs_half_weight_vectorized_equilibrium`
- `finite_gibbs_half_weight_vectorized_norm_eq_partition`
- `FiniteQuantumSpectrum.tfdCoeff_zero_time_normSq` and
  `tfdCoeff_zero_time_normSq_sum_eq_one`, plus the all-times norm and
  normalization theorems, in `InfoGeometry.Quantum.ThermofieldDouble`
- `syk_probe_bath_conformal_dimension_lock` (`𝔖Yr₁`)
- `sl2_rindler_wedge_and_tfd_scramblon_excitation` (`𝔖Yr₂`–`𝔖Yr₃`)
- `wick_scramblon_ladder_and_shockwave_entanglement_action` (`𝔖Yr₄`–`𝔖Yr₆`)
- `kitaev_syk_holography_and_elementary_expansion_master_synthesis` (`𝔖Yr₇`)

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- All ring identities are proved for any associative ring `[Ring B]` and any idempotent
  `hP : P * P = P`; the defined exponential-profile identity is proved for `0 < beta` and `1 ≤ N`.

#### BUCKET 3: OPEN CLOSURE DEBT
- Derivation of the scaling equations from SYK correlation functions, disorder averaging and Wick
  factorization remain open. The finite-spectrum scalar TFD coefficients have normalized Gibbs
  weights at all real boundary times by `tfdCoeff_normSq_sum_eq_one`; normalizing the finite
  matrix CFC half-Gibbs vector as a purification and connecting it to the existing finite
  partial-trace construction in `InfoGeometry.Quantum.FiniteAttentionCanonicalBridges` remain
  open.
  Continuous Rindler time evolution and any
  equality between an action shift and entanglement entropy remain unformalized. These require
  analytic/operator-algebraic carriers and explicit maps to this finite Peirce ring.
- Full path-integral disorder resummation over random Gaussian 4-fermion couplings $J_{jklm}$
  and continuous $\mathrm{Diff}(S^1)/\mathrm{PSL}(2,\mathbb{R})$ Schwarzian measure integration
  remain analytic continuum context beyond the finite equations and identities proved here.
-/

namespace InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset

open scoped MatrixOrder ComplexOrder
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus
open InfoGeometry.Canonical.SYKChaos

/-! ### Finite matrix vectorization and the commutant equation -/

/-- Column-entry vectorization of a finite square matrix, indexed by its row and column. -/
def finiteMatrixVectorize {ι R : Type*} (M : Matrix ι ι R) : ι × ι → R :=
  fun ij => M ij.1 ij.2

/-- Squared Hilbert-Schmidt norm of a vectorized finite matrix. -/
def finiteMatrixVectorizeNormSq {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) : ℂ :=
  ∑ ij : n × n, star (finiteMatrixVectorize M ij) * finiteMatrixVectorize M ij

/-- The left regular action of `H` on the vectorized entries of a matrix. -/
def finiteMatrixLeftAction {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]
    (H : Matrix ι ι R) (v : ι × ι → R) : ι × ι → R :=
  fun ij => ∑ k, H ij.1 k * v (k, ij.2)

/-- The right regular action of `H` on the vectorized entries of a matrix. -/
def finiteMatrixRightAction {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]
    (H : Matrix ι ι R) (v : ι × ι → R) : ι × ι → R :=
  fun ij => ∑ k, v (ij.1, k) * H k ij.2

/-- Vectorization turns the matrix Hilbert-Schmidt norm into the trace pairing
`Tr(M† M)`. -/
theorem finite_matrix_vectorize_norm_sq_eq_trace {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) :
    finiteMatrixVectorizeNormSq M = Matrix.trace (star M * M) := by
  simp only [finiteMatrixVectorizeNormSq, finiteMatrixVectorize,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.star_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/--
For a finite matrix `D`, equality of the left and right regular actions of `H`
on `vec(D)` is equivalent to the matrix commutant equation `H * D = D * H`.
This is a finite algebraic vectorization identity. It does not construct a
normalized Thermofield Double state or the square root of the normalized Gibbs density.
-/
theorem finite_matrix_vectorized_commutant_iff
    {R : Type*} [Semiring R] (n : ℕ)
    (H D : Matrix (Fin n) (Fin n) R) :
    finiteMatrixLeftAction H (finiteMatrixVectorize D) =
      finiteMatrixRightAction H (finiteMatrixVectorize D) ↔
        H * D = D * H := by
  have hLeft :
      finiteMatrixLeftAction H (finiteMatrixVectorize D) =
        finiteMatrixVectorize (H * D) := by
    funext ij
    rcases ij with ⟨i, j⟩
    simp [finiteMatrixLeftAction, finiteMatrixVectorize, Matrix.mul_apply]
  have hRight :
      finiteMatrixRightAction H (finiteMatrixVectorize D) =
        finiteMatrixVectorize (D * H) := by
    funext ij
    rcases ij with ⟨i, j⟩
    simp [finiteMatrixRightAction, finiteMatrixVectorize, Matrix.mul_apply]
  constructor
  · intro h
    rw [hLeft, hRight] at h
    funext i
    funext j
    exact congrFun h (i, j)
  · intro h
    rw [hLeft, hRight]
    funext ij
    rcases ij with ⟨i, j⟩
    exact congrFun (congrFun h i) j

/-- The finite-dimensional half-Gibbs weight defined by the Hermitian continuous
functional calculus. This is the unnormalized matrix amplitude `exp(-β H / 2)`. -/
noncomputable def finiteGibbsHalfWeight {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) : Matrix n n ℂ :=
  hH.cfc (fun r : ℝ => Real.exp (-β * r / 2))

/-- The CFC half-Gibbs weight is positive semidefinite. Together with its
square identity, it gives a positive-semidefinite square-root witness for the
unnormalized Gibbs density. -/
theorem finite_gibbs_half_weight_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    (finiteGibbsHalfWeight H hH β).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [finiteGibbsHalfWeight, ← hH.cfc_eq]
  apply cfc_nonneg
  intro r hr
  exact (Real.exp_pos _).le

/-- Squaring the unnormalized CFC half-Gibbs weight recovers the Gibbs density. -/
theorem finite_gibbs_half_weight_mul_self_eq_density {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    finiteGibbsHalfWeight H hH β * finiteGibbsHalfWeight H hH β =
      InfoGeometry.Canonical.FiniteMatrixGibbsFunctional.gibbsDensity H hH β := by
  let f : ℝ → ℝ := fun r => Real.exp (-β * r / 2)
  have hmul : hH.cfc f * hH.cfc f = hH.cfc (fun r => f r * f r) := by
    simpa only [← hH.cfc_eq] using (cfc_mul f f H).symm
  calc
    finiteGibbsHalfWeight H hH β * finiteGibbsHalfWeight H hH β =
        hH.cfc (fun r => f r * f r) := by
          simpa [finiteGibbsHalfWeight, f] using hmul
    _ = hH.cfc (InfoGeometry.Canonical.FiniteMatrixGibbsFunctional.expWeight β) := by
      congr 1
      funext r
      simp [f, InfoGeometry.Canonical.FiniteMatrixGibbsFunctional.expWeight,
        ← Real.exp_add]
    _ = InfoGeometry.Canonical.FiniteMatrixGibbsFunctional.gibbsDensity H hH β := rfl

/-- The CFC half-Gibbs weight commutes with its Hamiltonian. -/
theorem finite_gibbs_half_weight_commutes {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    Commute H (finiteGibbsHalfWeight H hH β) := by
  have hCFC : Commute (finiteGibbsHalfWeight H hH β) H := by
    change Commute (hH.cfc (fun r : ℝ => Real.exp (-β * r / 2))) H
    rw [← hH.cfc_eq]
    exact hH.isSelfAdjoint.commute_cfc (Commute.refl H)
      (fun r : ℝ => Real.exp (-β * r / 2))
  exact hCFC.symm

/-- Vectorizing the finite CFC half-Gibbs weight gives a two-sided stationary
vector for the Hamiltonian: the left and right regular actions agree. This
is the finite matrix analogue of the TFD equilibrium equation. -/
theorem finite_gibbs_half_weight_vectorized_equilibrium
    {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ) :
    finiteMatrixLeftAction H (finiteMatrixVectorize (finiteGibbsHalfWeight H hH β)) =
      finiteMatrixRightAction H (finiteMatrixVectorize (finiteGibbsHalfWeight H hH β)) := by
  apply (finite_matrix_vectorized_commutant_iff (n := n) H
    (finiteGibbsHalfWeight H hH β)).2
  exact (finite_gibbs_half_weight_commutes H hH β).eq

/-- The unnormalized finite TFD amplitude has squared vector norm equal to the
Gibbs partition function `Tr(exp(-βH))`. -/
theorem finite_gibbs_half_weight_vectorized_norm_eq_partition
    {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ) :
    finiteMatrixVectorizeNormSq (finiteGibbsHalfWeight H hH β) =
      Matrix.trace
        (InfoGeometry.Canonical.FiniteMatrixGibbsFunctional.gibbsDensity H hH β) := by
  let A := finiteGibbsHalfWeight H hH β
  have hA : A.IsHermitian := by
    exact (finite_gibbs_half_weight_posSemidef H hH β).isHermitian
  have hstar : star A = A := by
    rw [Matrix.star_eq_conjTranspose]
    exact hA.eq
  calc
    finiteMatrixVectorizeNormSq A = Matrix.trace (star A * A) :=
      finite_matrix_vectorize_norm_sq_eq_trace A
    _ = Matrix.trace (A * A) := by rw [hstar]
    _ = Matrix.trace
        (InfoGeometry.Canonical.FiniteMatrixGibbsFunctional.gibbsDensity H hH β) :=
      congrArg Matrix.trace (finite_gibbs_half_weight_mul_self_eq_density H hH β)

-- ============================================================================
-- NODE 𝔖Yr₁: Exact Probe (Δ = 1/4) vs. 3-Body Bath (Δ = 3/4) Scaling Lock
-- ============================================================================

/-- The integer-cleared scaling equations uniquely determine the probe and bath weights.
This choice-free core is reused by the larger Kitaev synthesis. -/
theorem syk_probe_bath_integer_dimension_lock (d_chi d_O : ℤ) :
    (d_O = 3 * d_chi ∧ d_chi + d_O = 4) ↔ (d_chi = 1 ∧ d_O = 3) := by
  constructor
  · rintro ⟨h1, h2⟩
    have h4 : d_chi * 4 = 4 := by
      calc
        d_chi * 4 = d_chi + 3 * d_chi := by ring
        _ = d_chi + d_O := by rw [← h1]
        _ = 4 := h2
    have hd1 : d_chi = 1 := by
      have hdiv := congrArg (fun z : ℤ => z / 4) h4
      have hL : (d_chi * 4) / 4 = d_chi := Int.mul_ediv_cancel d_chi (by decide)
      have hR : (4 : ℤ) / 4 = 1 := rfl
      exact hL.symm.trans (hdiv.trans hR)
    refine ⟨hd1, ?_⟩
    rw [h1, hd1]
    ring
  · rintro ⟨rfl, rfl⟩
    exact ⟨by ring, by ring⟩

/--
**Theorem 1 (`𝔖Yr₁` — `syk_probe_bath_conformal_dimension_lock`):**
1. In integer-cleared fourth-units (`d_chi = 4 Δ_χ`, `d_O = 4 Δ_O`), the 3-body melon
   self-energy `Σ(τ) = J² G(τ)³` (`d_O = 3 * d_chi`) and strong-coupling Schwinger–Dyson
   inversion `G * Σ = -δ` (`d_chi + d_O = 4`) uniquely lock `d_chi = 1` and `d_O = 3`.
2. Over `ℝ`, the exact conformal scaling equations `Δ_O = 3 * Δ_chi` and `Δ_chi + Δ_O = 1`
   uniquely lock `Δ_chi = 1 / 4` and `Δ_O = 3 / 4`.
-/
theorem syk_probe_bath_conformal_dimension_lock
    (d_chi d_O : ℤ) (Delta_chi Delta_O : ℝ) :
    ((d_O = 3 * d_chi ∧ d_chi + d_O = 4) ↔ (d_chi = 1 ∧ d_O = 3)) ∧
    ((Delta_O = 3 * Delta_chi ∧ Delta_chi + Delta_O = 1) ↔
      (Delta_chi = 1 / 4 ∧ Delta_O = 3 / 4)) := by
  refine ⟨syk_probe_bath_integer_dimension_lock d_chi d_O, ⟨?_, ?_⟩⟩
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    constructor <;> norm_num

-- ============================================================================
-- NODES 𝔖Yr₂–𝔖Yr₆: Rindler Horizon Shockwaves, Scramblon Ladder, & Entanglement Action
-- ============================================================================

section RindlerShockwaveOperatorAlgebra
variable {B : Type*} [Ring B]

/--
**Theorem 2 (`𝔖Yr₂` & `𝔖Yr₃` — `sl2_rindler_wedge_and_tfd_scramblon_excitation`):**
For any idempotent `P * P = P` in `[Ring B]`, the following Peirce-ring identities hold. The
Rindler and TFD terms below are analogies; no spacetime, time evolution, or TFD state is defined:
1. **Opposite corner commutator eigen-relations:** `comm (invS P) (conePlus P X) = conePlus P X + conePlus P X`
   and `comm (invS P) (coneMinus P Y) = -(coneMinus P Y + coneMinus P Y)`.
2. **Corner commutator identities:** `comm (conePlus P X) (coneMinus P Y) = genSig P X Y`
   and `invS P * genV P X Y = genSig P X Y`.
3. **Even/odd grading:** `comm (invS P) (evenGrade P W) = 0` and
   `comm (invS P) (genPhi P X Y) = genJ P X Y + genJ P X Y`.
-/
theorem sl2_rindler_wedge_and_tfd_scramblon_excitation
    (P X Y W : B) (hP : P * P = P) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) (conePlus P X) =
      conePlus P X + conePlus P X ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) (coneMinus P Y) =
      -(coneMinus P Y + coneMinus P Y) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P X) (coneMinus P Y) =
      genSig P X Y ∧
    invS P * genV P X Y = genSig P X Y ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) (evenGrade P W) = 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) (genPhi P X Y) =
      genJ P X Y + genJ P X Y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/--
The Peirce corner generators always satisfy the boost-weight relations in
`sl2_rindler_wedge_and_tfd_scramblon_excitation`, but their mutual commutator is
`invS P * genV P X Y`. This theorem characterizes exactly when that commutator
is the boost itself: it happens iff the anticommutator normalization is
`genV P X Y = 1`. Thus the full `sl₂` bracket relation is conditional, not a
consequence of idempotency alone.
-/
theorem peirce_horizon_bracket_matches_boost_iff_unit_foam
    (P X Y : B) (hP : P * P = P) :
    genSig P X Y = invS P ↔ genV P X Y = 1 := by
  have hSig : invS P * genV P X Y = genSig P X Y :=
    (sl2_rindler_wedge_and_tfd_scramblon_excitation P X Y P hP).2.2.2.1
  constructor
  · intro h
    calc
      genV P X Y = invS P * (invS P * genV P X Y) := by peirce_nf hP
      _ = invS P * invS P := by rw [hSig, h]
      _ = 1 := by peirce_nf hP
  · intro h
    calc
      genSig P X Y = invS P * genV P X Y := hSig.symm
      _ = invS P := by rw [h]; simp

/--
**Theorem 3 (`𝔖Yr₄`–`𝔖Yr₆` — `wick_scramblon_ladder_and_shockwave_entanglement_action`):**
For any idempotent `P * P = P` in `[Ring B]`, the theorem proves these ring identities; its
expectation, disorder, horizon, and entropy terminology is interpretive only:
1. **Corner defect:** `coherenceDefect P G` equals the upper/lower corner product, and its sum with
   the complementary corner defect equals `genV P G G`.
2. **Two-shear algebra:** For formal elements `E_fut = 1 + conePlus P X` and
   `E_past = 1 + coneMinus P Y`, their symmetric excess equals `genV P X Y`:
   - Their commutator `comm E_fut E_past` equals `genSig P X Y`,
   - Both `genV P X Y` and `genSig P X Y` commute with `invS P`
     (`comm (invS P) (genV P X Y) = 0` and `comm (invS P) (genSig P X Y) = 0`).
   No disorder average, Wick expectation, action, or entropy is defined in this theorem.
-/
theorem wick_scramblon_ladder_and_shockwave_entanglement_action
    (P G X Y : B) (hP : P * P = P) :
    let np := conePlus P X
    let nm := coneMinus P Y
    let ph := genPhi P X Y
    let E_fut := 1 + np
    let E_past := 1 + nm
    coherenceDefect P G = conePlus P G * coneMinus P G ∧
    coherenceDefect P G +
      ((1 - P) * (G * G) * (1 - P) - ((1 - P) * G * (1 - P)) * ((1 - P) * G * (1 - P))) =
      genV P G G ∧
    (E_fut * E_past - (1 + ph)) + (E_past * E_fut - (1 + ph)) = genV P X Y ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm E_fut E_past = genSig P X Y ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) (genV P X Y) = 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) (genSig P X Y) = 0 := by
  refine ⟨(coherator_weak_vs_strict_socratic_defect P G hP).1, ?_,
    by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩
  dsimp [coherenceDefect, genV, anticomm, conePlus, coneMinus]
  peirce_nf hP

/--
**Theorem 3B (`𝔖Yr₆`-B — `two_corner_shockwave_sheet_transfer_round_trip`):**
For any idempotent `P * P = P` in `[Ring B]` representing the left SYK copy `P` and right
SYK copy `1 - P`, and any left-sheet operator `x = P * Z * P`:
1. **Right-Sheet Readout of Double-Shockwave Conjugation:** Compressing the conjugated
   operator `cornerConjugation P X Y x` onto the right copy `1 - P` isolates the exact
   cross-sheet shockwave transfer `coneMinus P Y * x * conePlus P X`.
2. **Round-Trip Return via Opposite Shockwaves:** Applying `conePlus P X * (·) * coneMinus P Y`
   to the right-sheet readout returns `Q_+ * x * Q_+` where `Q_+ = conePlus P X * coneMinus P Y`.
3. **Corner reconstruction:** Whenever `conePlus P X * coneMinus P Y = P`,
   the algebraic left-to-right-to-left transfer reconstructs `x = P * Z * P` on the nose.
   The theorem has no involution, inner product, unitary, or physical teleportation structure.
-/
theorem two_corner_shockwave_sheet_transfer_round_trip
    (P X Y Z : B) (hP : P * P = P) :
    let x := P * Z * P
    let np := conePlus P X
    let nm := coneMinus P Y
    let qp := np * nm
    (1 - P) * cornerConjugation P X Y x * (1 - P) = nm * x * np ∧
    np * ((1 - P) * cornerConjugation P X Y x * (1 - P)) * nm = qp * x * qp ∧
    (qp = P →
      np * ((1 - P) * cornerConjugation P X Y x * (1 - P)) * nm = x) := by
  have h_right :
      (1 - P) * cornerConjugation P X Y (P * Z * P) * (1 - P) =
        coneMinus P Y * (P * Z * P) * conePlus P X := by
    dsimp [cornerConjugation, cornerConjugator, cornerConjugatorInv]
    peirce_nf hP
  have h_round :
      conePlus P X * ((1 - P) * cornerConjugation P X Y (P * Z * P) * (1 - P)) * coneMinus P Y =
        (conePlus P X * coneMinus P Y) * (P * Z * P) * (conePlus P X * coneMinus P Y) := by
    rw [h_right]
    noncomm_ring
  refine ⟨h_right, h_round, ?_⟩
  intro h_unit
  rw [h_round, h_unit]
  peirce_nf hP

/--
**Theorem 3C (`𝔖Yr₆`-C — `finite_rindler_boost_scramblon_scaling_and_schwarzian_moebius_jet`):**
For any commutative ring `[CommRing R]`, any associative `R`-algebra `[Ring B] [Algebra R B]`,
any Peirce idempotent `P * P = P`, any boost scale parameters `lam mu lam2 mu2 : R`, and any
formal time-reparametrization jet variables `a f f1 f2 f3 : R`:
1. **Finite Two-Sheet Rindler Boost Semigroup Law:**
   For `boost l m := l • P + m • (1 - P)`,
   `boost lam mu * boost lam2 mu2 = boost (lam * lam2) (mu * mu2)`, and whenever `lam * mu = 1`,
   `boost lam mu * boost mu lam = 1`.
2. **Opposite-Weight Scramblon Scaling (`+2` vs `-2`) & Boost-Invariant Eikonal Foam:**
   - `boost lam mu * conePlus P X * boost mu lam = (lam * lam) • conePlus P X`,
   - `boost lam mu * coneMinus P Y * boost mu lam = (mu * mu) • coneMinus P Y`,
   - `boost lam mu * genV P X Y * boost mu lam = (lam * mu) • genV P X Y`,
   - `boost lam mu * genSig P X Y * boost mu lam = (lam * mu) • genSig P X Y`.
3. **Cleared-Denominator Schwarzian Jet Invariance under $\mathrm{PSL}_2(R)$ Generators:**
   For the cleared Schwarzian numerator `S_num g1 g2 g3 := 2 * g1 * g3 - 3 * g2 ^ 2`,
   affine rescaling `(a * f1, a * f2, a * f3)` scales `S_num` by `a ^ 2`, and formal Möbius
   inversion `(f1, f * f2 - 2 * f1 ^ 2, f ^ 2 * f3 - 6 * f * f1 * f2 + 6 * f1 ^ 3)` scales
   `S_num` by `f ^ 2`:
   `2 * f1 * (f ^ 2 * f3 - 6 * f * f1 * f2 + 6 * f1 ^ 3) - 3 * (f * f2 - 2 * f1 ^ 2) ^ 2 = f ^ 2 * (2 * f1 * f3 - 3 * f2 ^ 2)`.
-/
theorem finite_rindler_boost_scramblon_scaling_and_schwarzian_moebius_jet
    {R : Type*} [CommRing R] [Algebra R B]
    (P X Y : B) (hP : P * P = P)
    (lam mu lam2 mu2 a f f1 f2 f3 : R) :
    let boost := fun (l m : R) => l • P + m • (1 - P)
    boost lam mu * boost lam2 mu2 = boost (lam * lam2) (mu * mu2) ∧
    (lam * mu = 1 → boost lam mu * boost mu lam = 1) ∧
    boost lam mu * conePlus P X * boost mu lam = (lam * lam) • conePlus P X ∧
    boost lam mu * coneMinus P Y * boost mu lam = (mu * mu) • coneMinus P Y ∧
    boost lam mu * genV P X Y * boost mu lam = (lam * mu) • genV P X Y ∧
    boost lam mu * genSig P X Y * boost mu lam = (lam * mu) • genSig P X Y ∧
    (2 * (a * f1) * (a * f3) - 3 * (a * f2) ^ 2 =
      a ^ 2 * (2 * f1 * f3 - 3 * f2 ^ 2)) ∧
    (2 * f1 * (f ^ 2 * f3 - 6 * f * f1 * f2 + 6 * f1 ^ 3) -
        3 * (f * f2 - 2 * f1 ^ 2) ^ 2 =
      f ^ 2 * (2 * f1 * f3 - 3 * f2 ^ 2)) := by
  intro boost
  have hPQ : P * (1 - P) = 0 := by peirce_nf hP
  have hQP : (1 - P) * P = 0 := by peirce_nf hP
  have hQQ : (1 - P) * (1 - P) = 1 - P := by peirce_nf hP
  have hP_np : P * conePlus P X = conePlus P X := by peirce_nf hP
  have hQ_np : (1 - P) * conePlus P X = 0 := by peirce_nf hP
  have hnp_P : conePlus P X * P = 0 := by peirce_nf hP
  have hnp_Q : conePlus P X * (1 - P) = conePlus P X := by peirce_nf hP
  have hP_nm : P * coneMinus P Y = 0 := by peirce_nf hP
  have hQ_nm : (1 - P) * coneMinus P Y = coneMinus P Y := by peirce_nf hP
  have hnm_P : coneMinus P Y * P = coneMinus P Y := by peirce_nf hP
  have hnm_Q : coneMinus P Y * (1 - P) = 0 := by peirce_nf hP
  have hMul : ∀ l1 m1 l2 m2 : R,
      boost l1 m1 * boost l2 m2 = boost (l1 * l2) (m1 * m2) := by
    intro l1 m1 l2 m2
    dsimp only [boost]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      hP, hPQ, hQP, hQQ, smul_zero, add_zero, zero_add, mul_comm l2 l1, mul_comm m2 m1]
  have hUnit : lam * mu = 1 → boost lam mu * boost mu lam = 1 := by
    intro h1
    rw [hMul lam mu mu lam, mul_comm mu lam, h1]
    dsimp only [boost]
    simp only [one_smul, add_sub_cancel]
  have hPlus :
      boost lam mu * conePlus P X * boost mu lam = (lam * lam) • conePlus P X := by
    dsimp only [boost]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      hP_np, hQ_np, hnp_P, hnp_Q, smul_zero, add_zero, zero_add]
  have hMinus :
      boost lam mu * coneMinus P Y * boost mu lam = (mu * mu) • coneMinus P Y := by
    dsimp only [boost]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      hP_nm, hQ_nm, hnm_P, hnm_Q, smul_zero, add_zero, zero_add]
  have hQplus :
      boost lam mu * (conePlus P X * coneMinus P Y) * boost mu lam =
        (lam * mu) • (conePlus P X * coneMinus P Y) := by
    have hP_qp : P * (conePlus P X * coneMinus P Y) = conePlus P X * coneMinus P Y := by
      peirce_nf hP
    have hQ_qp : (1 - P) * (conePlus P X * coneMinus P Y) = 0 := by peirce_nf hP
    have hqp_P : (conePlus P X * coneMinus P Y) * P = conePlus P X * coneMinus P Y := by
      peirce_nf hP
    have hqp_Q : (conePlus P X * coneMinus P Y) * (1 - P) = 0 := by peirce_nf hP
    dsimp only [boost]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      hP_qp, hQ_qp, hqp_P, hqp_Q, smul_zero, add_zero, mul_comm mu lam]
  have hQminus :
      boost lam mu * (coneMinus P Y * conePlus P X) * boost mu lam =
        (lam * mu) • (coneMinus P Y * conePlus P X) := by
    have hP_qm : P * (coneMinus P Y * conePlus P X) = 0 := by peirce_nf hP
    have hQ_qm : (1 - P) * (coneMinus P Y * conePlus P X) = coneMinus P Y * conePlus P X := by
      peirce_nf hP
    have hqm_P : (coneMinus P Y * conePlus P X) * P = 0 := by peirce_nf hP
    have hqm_Q : (coneMinus P Y * conePlus P X) * (1 - P) = coneMinus P Y * conePlus P X := by
      peirce_nf hP
    dsimp only [boost]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      hP_qm, hQ_qm, hqm_P, hqm_Q, smul_zero, zero_add]
  have hV :
      boost lam mu * genV P X Y * boost mu lam = (lam * mu) • genV P X Y := by
    calc boost lam mu * genV P X Y * boost mu lam
      _ = boost lam mu * (conePlus P X * coneMinus P Y + coneMinus P Y * conePlus P X) * boost mu lam := rfl
      _ = (boost lam mu * (conePlus P X * coneMinus P Y) + boost lam mu * (coneMinus P Y * conePlus P X)) * boost mu lam := by
          rw [mul_add (boost lam mu)]
      _ = boost lam mu * (conePlus P X * coneMinus P Y) * boost mu lam +
            boost lam mu * (coneMinus P Y * conePlus P X) * boost mu lam := by
          rw [add_mul _ _ (boost mu lam)]
      _ = (lam * mu) • (conePlus P X * coneMinus P Y) + (lam * mu) • (coneMinus P Y * conePlus P X) := by
          rw [hQplus, hQminus]
      _ = (lam * mu) • genV P X Y := by
          rw [← smul_add]; rfl
  have hSig :
      boost lam mu * genSig P X Y * boost mu lam = (lam * mu) • genSig P X Y := by
    calc boost lam mu * genSig P X Y * boost mu lam
      _ = boost lam mu * (conePlus P X * coneMinus P Y - coneMinus P Y * conePlus P X) * boost mu lam := rfl
      _ = (boost lam mu * (conePlus P X * coneMinus P Y) - boost lam mu * (coneMinus P Y * conePlus P X)) * boost mu lam := by
          rw [mul_sub (boost lam mu)]
      _ = boost lam mu * (conePlus P X * coneMinus P Y) * boost mu lam -
            boost lam mu * (coneMinus P Y * conePlus P X) * boost mu lam := by
          rw [sub_mul _ _ (boost mu lam)]
      _ = (lam * mu) • (conePlus P X * coneMinus P Y) - (lam * mu) • (coneMinus P Y * conePlus P X) := by
          rw [hQplus, hQminus]
      _ = (lam * mu) • genSig P X Y := by
          rw [← smul_sub]; rfl
  refine ⟨hMul lam mu lam2 mu2, hUnit, hPlus, hMinus, hV, hSig, by ring, by ring⟩

/--
**Theorem 4 (`𝔖Yr₇` — `kitaev_syk_holography_and_elementary_expansion_master_synthesis`):**
Combines the following finite formulas and conditional ring identities:
1. The solution of the assumed scalar equations for $\Delta_\chi$ and $\Delta_O$,
2. A scalar calculation from the imported definitions gives
   `otocGrowth N (mssMaxLyapunov beta) (scramblingTime beta N) = 1` at the defined time
   $t_* = \frac{\beta}{2\pi}\ln N$. This does not derive an SYK Lyapunov exponent, an MSS
   saturation result for model dynamics, or an OTOC from a physical state,
3. Peirce corner commutators and the algebraic defect formula,
4. The constructive elementary-expansion 4-group coherator word expansion, two-sided retraction
   `cornerConjugationRetraction P X Y (cornerConjugation P X Y (P * Z * P)) = P * Z * P`, and
   unconditional even-grade Peirce commutator shift
   `evenGrade P (cornerConjugation P X Y (P * Z * P) - P * Z * P) = comm (coneMinus P Y * (P * Z * P)) (conePlus P X)`.
-/
theorem kitaev_syk_holography_and_elementary_expansion_master_synthesis
    (P G X Y Z : B) (hP : P * P = P)
    (beta : ℝ) (h_beta : 0 < beta) (N : ℕ) (hN : 1 ≤ N) :
    let x := P * Z * P
    let np := conePlus P X
    let nm := coneMinus P Y
    let E_fut := 1 + np
    let E_past := 1 + nm
    ((3 : ℤ) = 3 * (1 : ℤ) ∧ (1 : ℤ) + (3 : ℤ) = 4) ∧
    otocGrowth N (mssMaxLyapunov beta) (scramblingTime beta N) = 1 ∧
    coherenceDefect P G = conePlus P G * coneMinus P G ∧
    (E_fut * E_past - (1 + genPhi P X Y)) + (E_past * E_fut - (1 + genPhi P X Y)) =
      genV P X Y ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P) (genV P X Y) = 0 ∧
    cornerConjugation P X Y x =
      x + (x * np + nm * x) + (nm * x * np - np * nm * x) - np * nm * x * np ∧
    evenGrade P (cornerConjugation P X Y x - x) =
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (nm * x) np ∧
    cornerConjugationRetraction P X Y (cornerConjugation P X Y x) = x := by
  have h_otoc := defined_exponential_profile_eq_one_at_selected_time beta h_beta N hN
  have h_wick := (wick_scramblon_ladder_and_shockwave_entanglement_action P G X Y hP).1
  have h_act := (wick_scramblon_ladder_and_shockwave_entanglement_action P G X Y hP).2.2.1
  have h_boost := (wick_scramblon_ladder_and_shockwave_entanglement_action P G X Y hP).2.2.2.2.1
  have h_word := cornerConjugation_base_expansion P X Y Z hP
  have h_comm := (cornerConjugation_even_shift_eq_reverse_commutator P X Y Z hP).1
  have h_ret := (cornerConjugation_projection_retraction_isomorphism P X Y Z Z Z Z hP).2.1
  exact ⟨⟨rfl, rfl⟩, h_otoc, h_wick, h_act, h_boost, h_word, h_comm, h_ret⟩

end RindlerShockwaveOperatorAlgebra

end InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset
