/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
import InfoGeometry.Canonical.LoxodromicHorizonThreeProjectorFlow
import InfoGeometry.Canonical.KerrUnruhFermionicHorizonBridge
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Instability of Rotating Local Spin Frames: Singlet and Triplet Channels on the Doubled Minkowski Vacuum

Formalizes the finite-dimensional spin-frame algebra, pair-breaking threshold, Krein-collision
dynamical instability, and pure-real `Cl(1,1) ≅ M₂(ℝ)` Dirac spin-exchange condensation across
rotating local spin frames over the doubled Minkowski signature-`(4,4)` vacuum:

1. **Two-Spin Singlet–Triplet Decomposition (`ℂ²₊ ⊗ ℂ²₋ ≅ 1 ⊕ 3`)**:
   Explicit `4 × 4` Hermitian `su(2)` generators `(spinX, spinY, spinZ)` with Casimir
   `spinCasimir = 2 • projTriplet`, proving exact `SU(2)` spin-frame invariance of the singlet
   projector (`spin_i * projSinglet = 0`), linear `±1` co-rotating splitting of transverse triplet
   modes `tripletPlus`/`tripletMinus`, transverse `spinX` precession mixing `tripletZero ↦
   tripletPlus + tripletMinus`, and staggered sheet-boost mixing `singletVec ↔ tripletZero`.
2. **Rotating Singlet BdG Pair-Breaking Threshold (`|Ω| = 2|m|`)**:
   For `singletRotBdG ξ m Ω = bdgHamiltonian ξ m - (Ω / 2) • 1`, subcritical rotations
   `|Ω| < 2 |m|` retain a uniform positive quadratic lower bound `(|m| - |Ω| / 2)² ‖ψ‖² ≤ ‖H_rot ψ‖²`
   and trivial kernel; the critical point `Ω = 2m` closes the gap on `Sum.elim u u`; and
   `Ω > 2m` inverts both energy (`⟨ψ, H_rot ψ⟩ < 0`) and co-rotating Fermi occupation
   (`1 / 2 < kerrFermiOcc β Ω m (1 / 2)`).
3. **Doubled-Minkowski Bosonic Triplet Krein-Collision & Exponential Instability**:
   For the `𝒦`-self-adjoint two-sheet triplet generator `tripletKreinGen δ γ = zCut2 * !![δ, γ; γ, δ]`,
   critical resonance `δ = γ ≠ 0` collapses to a non-zero nilpotent Jordan cell (`G² = 0`) with
   linear secular growth `1 + t • G`, while supercriticality `|δ| < |γ|` produces a real positive
   exponential growth rate `lam0 = √(γ² - δ²)` on an exact **Krein-null** eigenvector `v_grow`.
4. **Lift onto `Fin 2 × Fin 4` & Loxodromic Frame Precession**:
   Lifts the Krein-collision instability directly onto the `(4,4)` doubled Minkowski carrier
   `doubledMinkowskiTripletGen` and links local spin non-commutativity to the 4D loxodromic
   obstruction `K1 * J3 ≠ J3 * K1`.
5. **Real `Cl(1,1) ≅ M₂(ℝ)` Dirac Spin-Exchange & Singlet → Triplet Condensation (`ΔE = J - Ω`)**:
   Constructs `spinExchange4 = X ⊗ X + Z ⊗ Z - ε ⊗ ε` purely over `ℝ` (`swapOp4² = 1`, `Tr = 2`),
   splits `ℝ² ⊗ ℝ²` into orthogonal rank-1 singlet (`-3`) and rank-3 triplet (`+1`) sectors, and
   proves the exact rotating-frame instability gap `E_T1 - E_S = J - Ω`.

Scope boundary: These are finite-dimensional matrix/operator stability and Krein-collision
theorems; no continuum 4D curved-spacetime quantum field theory existence is claimed.
-/

set_option autoImplicit false

noncomputable section

open scoped Kronecker
open Matrix Complex
open InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
open InfoGeometry.Canonical.LoxodromicHorizonThreeProjectorFlow
open InfoGeometry.Canonical.KerrUnruhFermionicHorizonBridge

namespace InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability

/-! ### Part 1: Two-Spin `ℂ²₊ ⊗ ℂ²₋ ≅ 1 ⊕ 3` Singlet–Triplet Algebra -/

/-- Total spin-`X` generator `(σ_x ⊗ I + I ⊗ σ_x) / 2` in the two-spin basis `(↑↑, ↑↓, ↓↑, ↓↓)`. -/
def spinX : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2 : ℂ) • !![0, 1, 1, 0;
                    1, 0, 0, 1;
                    1, 0, 0, 1;
                    0, 1, 1, 0]

/-- Total spin-`Y` generator `(σ_y ⊗ I + I ⊗ σ_y) / 2` in the two-spin basis `(↑↑, ↑↓, ↓↑, ↓↓)`. -/
def spinY : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2 : ℂ) • !![0, -I, -I, 0;
                    I,  0,  0, -I;
                    I,  0,  0, -I;
                    0,  I,  I, 0]

/-- Total spin-`Z` generator `(σ_z ⊗ I + I ⊗ σ_z) / 2 = diag(1, 0, 0, -1)`. -/
def spinZ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0,  0;
     0, 0, 0,  0;
     0, 0, 0,  0;
     0, 0, 0, -1]

/-- Relative sheet spin-difference operator `(σ_z ⊗ I - I ⊗ σ_z) / 2 = diag(0, 1, -1, 0)`. -/
def staggeredSpinZ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0,  0, 0;
     0, 1,  0, 0;
     0, 0, -1, 0;
     0, 0,  0, 0]

/-- Orthogonal rank-1 singlet projector `P_sing` onto `ℂ · (|↑↓⟩ - |↓↑⟩)`. -/
def projSinglet : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2 : ℂ) • !![0,  0,  0, 0;
                    0,  1, -1, 0;
                    0, -1,  1, 0;
                    0,  0,  0, 0]

/-- Orthogonal rank-3 triplet projector `P_trip = I₄ - P_sing`. -/
def projTriplet : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 : Matrix (Fin 4) (Fin 4) ℂ) - projSinglet

/-- Total spin Casimir `S² = S_x² + S_y² + S_z²`. -/
def spinCasimir : Matrix (Fin 4) (Fin 4) ℂ :=
  spinX * spinX + spinY * spinY + spinZ * spinZ

/-- Unnormalized singlet vector `|↑↓⟩ - |↓↑⟩` (`S = 0, m_s = 0`). -/
def singletVec : Fin 4 → ℂ := ![0, 1, -1, 0]

/-- Triplet `m_s = +1` basis vector `|↑↑⟩`. -/
def tripletPlus : Fin 4 → ℂ := ![1, 0, 0, 0]

/-- Unnormalized longitudinal triplet vector `|↑↓⟩ + |↓↑⟩` (`S = 1, m_s = 0`). -/
def tripletZero : Fin 4 → ℂ := ![0, 1, 1, 0]

/-- Triplet `m_s = -1` basis vector `|↓↓⟩`. -/
def tripletMinus : Fin 4 → ℂ := ![0, 0, 0, 1]

/-- Exact `su(2)` angular-momentum commutation relations `[S_i, S_j] = i ε_{ijk} S_k`. -/
theorem su2_commutation_relations :
    spinX * spinY - spinY * spinX = I • spinZ ∧
    spinY * spinZ - spinZ * spinY = I • spinX ∧
    spinZ * spinX - spinX * spinZ = I • spinY := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    { ext i j
      fin_cases i <;> fin_cases j <;>
        (simp [spinX, spinY, spinZ, Complex.ext_iff]; try norm_num) }

/-- Explicit non-commutativity witness for the `4 × 4` complex spin-frame carrier. -/
theorem exists_noncomm_mat4_complex :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℂ, A * B ≠ B * A := by
  refine ⟨spinX, spinY, fun h => ?_⟩
  have hComm := su2_commutation_relations.1
  rw [h, sub_self] at hComm
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) hComm
  simp [spinZ, Complex.ext_iff] at h00

/-- All three `su(2)` spin-frame generators are Hermitian. -/
theorem spin_generators_isHermitian :
    spinX.IsHermitian ∧ spinY.IsHermitian ∧ spinZ.IsHermitian := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    { rw [Matrix.IsHermitian]
      ext i j
      fin_cases i <;> fin_cases j <;>
        (simp [spinX, spinY, spinZ]; try norm_num) }

/-- Exact orthogonal completeness and ranks of the singlet and triplet projectors (`1 + 3 = 4`). -/
theorem singlet_triplet_projector_algebra :
    projSinglet + projTriplet = 1 ∧
    projSinglet * projSinglet = projSinglet ∧
    projTriplet * projTriplet = projTriplet ∧
    projSinglet * projTriplet = 0 ∧
    projTriplet * projSinglet = 0 ∧
    Matrix.trace projSinglet = 1 ∧
    Matrix.trace projTriplet = 3 := by
  refine ⟨by simp [projTriplet], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      (simp [projSinglet, Matrix.mul_apply, Fin.sum_univ_four, Complex.ext_iff]; try norm_num)
  · ext i j; fin_cases i <;> fin_cases j <;>
      (simp [projTriplet, projSinglet, Matrix.mul_apply, Fin.sum_univ_four, Complex.ext_iff];
        try norm_num)
  · ext i j; fin_cases i <;> fin_cases j <;>
      (simp [projTriplet, projSinglet, Matrix.mul_apply, Fin.sum_univ_four, Complex.ext_iff];
        try norm_num)
  · ext i j; fin_cases i <;> fin_cases j <;>
      (simp [projTriplet, projSinglet, Matrix.mul_apply, Fin.sum_univ_four, Complex.ext_iff];
        try norm_num)
  · simp [projSinglet, Matrix.trace, Matrix.diag, Fin.sum_univ_four, Complex.ext_iff]
    norm_num
  · simp [projTriplet, projSinglet, Matrix.trace, Matrix.diag, Fin.sum_univ_four, Complex.ext_iff]
    norm_num

/-- Total spin Casimir equals `2 • projTriplet` (`S(S+1) = 0` on singlet, `2` on triplet). -/
theorem spinCasimir_eq_two_projTriplet : spinCasimir = (2 : ℂ) • projTriplet := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [spinCasimir, spinX, spinY, spinZ, projTriplet, projSinglet, Complex.ext_iff];
      try norm_num)

/-- The spin-singlet subspace is strictly invariant under all local `su(2)` spin-frame generators. -/
theorem singlet_su2_frame_invariant :
    spinX * projSinglet = 0 ∧ spinY * projSinglet = 0 ∧ spinZ * projSinglet = 0 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    { ext i j
      fin_cases i <;> fin_cases j <;>
        (simp [spinX, spinY, spinZ, projSinglet, Matrix.mul_apply, Fin.sum_univ_four];
          try norm_num) }

/-- Spin-`Z` eigenvalues on the singlet and triplet basis vectors, transverse `spinX` precession
mixing (`m_s = 0 ↦ m_s = ±1`), and staggered sheet-boost singlet–triplet mixing. -/
theorem triplet_spinZ_splitting_and_precession_mixing :
    spinZ.mulVec singletVec = 0 ∧
    spinZ.mulVec tripletPlus = (1 : ℂ) • tripletPlus ∧
    spinZ.mulVec tripletZero = 0 ∧
    spinZ.mulVec tripletMinus = (-1 : ℂ) • tripletMinus ∧
    spinX.mulVec singletVec = 0 ∧
    spinX.mulVec tripletZero = tripletPlus + tripletMinus ∧
    staggeredSpinZ.mulVec singletVec = tripletZero ∧
    staggeredSpinZ.mulVec tripletZero = singletVec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    { ext i
      fin_cases i <;>
        (simp [spinZ, spinX, staggeredSpinZ, singletVec, tripletPlus, tripletZero, tripletMinus,
          Matrix.mulVec, dotProduct, Fin.sum_univ_four, Complex.ext_iff]; try norm_num) }

/-! ### Part 2: Rotating Local Spin Frame — Singlet BdG Pair-Breaking Threshold (`|Ω| = 2|m|`) -/

/-- Rotating-frame shifted BdG Hamiltonian `H_rot(ξ, m, Ω) = H_BdG(ξ, m) - (Ω / 2) I_{2n}`
in the singlet quasiparticle spin-`1/2` channel. -/
def singletRotBdG {n : ℕ} (ξ : Matrix (Fin n) (Fin n) ℝ) (m Ω : ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  bdgHamiltonian ξ m - (Ω / 2) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)

private lemma cauchy_schwarz_dotProduct {α : Type*} [Fintype α] (u v : α → ℝ) :
    (dotProduct u v) ^ 2 ≤ dotProduct u u * dotProduct v v := by
  simpa [dotProduct, pow_two] using
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α) u v

private lemma shifted_norm_sq_lower_bound {nH nPsi ip m c : ℝ}
    (hH : 0 ≤ nH) (hPsi : 0 ≤ nPsi) (hGap : m ^ 2 * nPsi ≤ nH)
    (hCS : ip ^ 2 ≤ nPsi * nH) (hSub : |c| ≤ |m|) :
    (|m| - |c|) ^ 2 * nPsi ≤ nH - 2 * c * ip + c ^ 2 * nPsi := by
  have hip : |ip| ≤ Real.sqrt nPsi * Real.sqrt nH := by
    rw [← Real.sqrt_mul hPsi]
    exact Real.abs_le_sqrt hCS
  have hc_abs : c * ip ≤ |c| * |ip| := by
    calc
      c * ip ≤ |c * ip| := le_abs_self _
      _ = |c| * |ip| := abs_mul c ip
  have hbd : c * ip ≤ |c| * (Real.sqrt nPsi * Real.sqrt nH) :=
    hc_abs.trans (mul_le_mul_of_nonneg_left hip (abs_nonneg c))
  have hsq_rhs : (Real.sqrt nH - |c| * Real.sqrt nPsi) ^ 2 =
      nH - 2 * |c| * (Real.sqrt nPsi * Real.sqrt nH) + c ^ 2 * nPsi := by
    have h1 : (Real.sqrt nH) ^ 2 = nH := Real.sq_sqrt hH
    have h2 : (|c| * Real.sqrt nPsi) ^ 2 = c ^ 2 * nPsi := by
      rw [mul_pow, sq_abs, Real.sq_sqrt hPsi]
    linarith [show (Real.sqrt nH - |c| * Real.sqrt nPsi) ^ 2 =
      (Real.sqrt nH) ^ 2 - 2 * |c| * (Real.sqrt nPsi * Real.sqrt nH) +
        (|c| * Real.sqrt nPsi) ^ 2 by ring]
  have hgap_sqrt : (|m| - |c|) * Real.sqrt nPsi ≤ Real.sqrt nH - |c| * Real.sqrt nPsi := by
    have hm_le : |m| * Real.sqrt nPsi ≤ Real.sqrt nH := by
      rw [← Real.sqrt_sq (mul_nonneg (abs_nonneg m) (Real.sqrt_nonneg nPsi))]
      exact Real.sqrt_le_sqrt (by rw [mul_pow, sq_abs, Real.sq_sqrt hPsi]; exact hGap)
    linarith [show (|m| - |c|) * Real.sqrt nPsi =
      |m| * Real.sqrt nPsi - |c| * Real.sqrt nPsi by ring]
  have hsq_le : ((|m| - |c|) * Real.sqrt nPsi) ^ 2 ≤
      (Real.sqrt nH - |c| * Real.sqrt nPsi) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr hSub) (Real.sqrt_nonneg nPsi)) hgap_sqrt 2
  have hsq_lhs : ((|m| - |c|) * Real.sqrt nPsi) ^ 2 = (|m| - |c|) ^ 2 * nPsi := by
    rw [mul_pow, Real.sq_sqrt hPsi]
  linarith

private lemma real_dot_shift_expand {α : Type*} [Fintype α] (h v : α → ℝ) (c : ℝ) :
    dotProduct (h - c • v) (h - c • v) =
      dotProduct h h - 2 * c * dotProduct v h + c ^ 2 * dotProduct v v := by
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [dotProduct_comm h v]
  ring

private lemma real_two_mul_abs_div_two {Ω : ℝ} : |Ω / 2| = |Ω| / 2 := by
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

private lemma real_abs_div_two_le_of_lt {Ω m : ℝ} (h : |Ω| < 2 * |m|) : |Ω / 2| ≤ |m| := by
  rw [real_two_mul_abs_div_two]
  linarith [h]

private lemma real_sub_abs_div_two_pos {Ω m : ℝ} (h : |Ω| < 2 * |m|) : 0 < |m| - |Ω| / 2 := by
  linarith [h]

private lemma real_sq_eq_zero_dot {α : Type*} [Fintype α] (v : α → ℝ) (hDot0 : dotProduct v v = 0) :
    v = 0 := by
  ext i
  have hAll := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (v j))).mp hDot0
  exact mul_self_eq_zero.mp (hAll i (Finset.mem_univ i))

private lemma real_zero_dot_of_sq_le_zero {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hle : a * b ≤ 0) :
    b = 0 := by
  nlinarith [ha, hb, hle]

private lemma real_sub_mul_lt_zero_of_lt {m Ω s : ℝ} (hSuper : 2 * m < Ω) (hs : 0 < s) :
    (m - Ω / 2) * s < 0 := by
  have hneg : m - Ω / 2 < 0 := by linarith [hSuper]
  exact mul_neg_of_neg_of_pos hneg hs

/-- **Subcritical Singlet BdG Stability (`|Ω| < 2|m|`)**:
Below the Chandrasekhar–Clogston / Barnett pair-breaking threshold `|Ω| < 2|m|`, the rotating-frame
singlet BdG Hamiltonian retains a strict positive spectral gap `(|m| - |Ω| / 2)² ‖ψ‖² ≤ ‖H_rot ψ‖²`
and trivial kernel. -/
theorem singletRotBdG_stable_below_threshold {n : ℕ}
    (ξ : Matrix (Fin n) (Fin n) ℝ) (hξ : ξᵀ = ξ) (m Ω : ℝ) (hSub : |Ω| < 2 * |m|)
    (ψ : Fin n ⊕ Fin n → ℝ) :
    (|m| - |Ω| / 2) ^ 2 * dotProduct ψ ψ ≤
        dotProduct ((singletRotBdG ξ m Ω).mulVec ψ) ((singletRotBdG ξ m Ω).mulVec ψ) ∧
      ((singletRotBdG ξ m Ω).mulVec ψ = 0 → ψ = 0) := by
  have hBdg := bdg_gapped_spectrum_and_particle_hole_symmetry ξ hξ m ψ
  have hGap0 : m ^ 2 * dotProduct ψ ψ ≤
      dotProduct ((bdgHamiltonian ξ m).mulVec ψ) ((bdgHamiltonian ξ m).mulVec ψ) := by
    rw [← hBdg.2.2.2.1]
    exact hBdg.2.2.2.2.1
  have hVec : (singletRotBdG ξ m Ω).mulVec ψ = (bdgHamiltonian ξ m).mulVec ψ - (Ω / 2) • ψ := by
    unfold singletRotBdG
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hExp : dotProduct ((singletRotBdG ξ m Ω).mulVec ψ) ((singletRotBdG ξ m Ω).mulVec ψ) =
      dotProduct ((bdgHamiltonian ξ m).mulVec ψ) ((bdgHamiltonian ξ m).mulVec ψ) -
        2 * (Ω / 2) * dotProduct ψ ((bdgHamiltonian ξ m).mulVec ψ) +
        (Ω / 2) ^ 2 * dotProduct ψ ψ := by
    rw [hVec]
    exact real_dot_shift_expand ((bdgHamiltonian ξ m).mulVec ψ) ψ (Ω / 2)
  have hH_nn : 0 ≤ dotProduct ((bdgHamiltonian ξ m).mulVec ψ) ((bdgHamiltonian ξ m).mulVec ψ) :=
    Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hPsi_nn : 0 ≤ dotProduct ψ ψ := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hCS := cauchy_schwarz_dotProduct ψ ((bdgHamiltonian ξ m).mulVec ψ)
  have hBound := shifted_norm_sq_lower_bound hH_nn hPsi_nn hGap0 hCS (real_abs_div_two_le_of_lt hSub)
  rw [real_two_mul_abs_div_two] at hBound
  have hLow : (|m| - |Ω| / 2) ^ 2 * dotProduct ψ ψ ≤
      dotProduct ((singletRotBdG ξ m Ω).mulVec ψ) ((singletRotBdG ξ m Ω).mulVec ψ) := by
    rw [hExp]
    exact hBound
  refine ⟨hLow, ?_⟩
  intro hZero
  have h0 : dotProduct ((singletRotBdG ξ m Ω).mulVec ψ) ((singletRotBdG ξ m Ω).mulVec ψ) = 0 := by
    rw [hZero, dotProduct_zero]
  have hLe : (|m| - |Ω| / 2) ^ 2 * dotProduct ψ ψ ≤ 0 := h0 ▸ hLow
  have hGapPos : 0 < (|m| - |Ω| / 2) ^ 2 := sq_pos_of_pos (real_sub_abs_div_two_pos hSub)
  exact real_sq_eq_zero_dot ψ (real_zero_dot_of_sq_le_zero hGapPos hPsi_nn hLe)

/-- **Critical Singlet Gap Closure (`Ω = 2m`)**:
At zero kinetic term `ξ = 0`, the uniform rotating singlet mode `Sum.elim u u` becomes an exact
zero mode of `singletRotBdG 0 m (2 * m)`. -/
theorem singletRotBdG_gap_closure_at_critical {n : ℕ} (m : ℝ) (u : Fin n → ℝ) :
    (singletRotBdG (0 : Matrix (Fin n) (Fin n) ℝ) m (2 * m)).mulVec (Sum.elim u u) = 0 := by
  ext (i | i) <;>
    simp [singletRotBdG, bdgHamiltonian, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.one_apply]

/-- **Supercritical Singlet Energy Inversion (`Ω > 2m`)**:
Above critical rotation speed `Ω > 2m`, the singlet quasiparticle expectation energy turns strictly
negative on every nonzero symmetric two-sheet state `Sum.elim u u`. -/
theorem singletRotBdG_supercritical_energy_inversion {n : ℕ} (m Ω : ℝ) (hSuper : 2 * m < Ω)
    (u : Fin n → ℝ) (hu : u ≠ 0) :
    dotProduct (Sum.elim u u)
      ((singletRotBdG (0 : Matrix (Fin n) (Fin n) ℝ) m Ω).mulVec (Sum.elim u u)) < 0 := by
  have hMulBdg : (bdgHamiltonian (0 : Matrix (Fin n) (Fin n) ℝ) m).mulVec (Sum.elim u u) =
      m • Sum.elim u u := by
    ext (i | i) <;>
      simp [bdgHamiltonian, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
  have hMul : (singletRotBdG (0 : Matrix (Fin n) (Fin n) ℝ) m Ω).mulVec (Sum.elim u u) =
      (m - Ω / 2) • Sum.elim u u := by
    unfold singletRotBdG
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hMulBdg, ← sub_smul]
  rw [hMul, dotProduct_smul, smul_eq_mul]
  have hSumPos : 0 < dotProduct (Sum.elim u u) (Sum.elim u u) := by
    have hnn : 0 ≤ dotProduct (Sum.elim u u) (Sum.elim u u) :=
      Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    refine lt_of_le_of_ne hnn fun heq => hu ?_
    have hZeroVec := real_sq_eq_zero_dot (Sum.elim u u) heq.symm
    ext i
    exact congrArg (fun f => f (Sum.inl i)) hZeroVec
  exact real_sub_mul_lt_zero_of_lt hSuper hSumPos

private lemma real_fermi_inversion_aux {x : ℝ} : (1 / 2 : ℝ) < 1 / (Real.exp x + 1) ↔ x < 0 := by
  have hden : 0 < Real.exp x + 1 := add_pos (Real.exp_pos x) one_pos
  rw [div_lt_div_iff₀ (by norm_num) hden]
  have hexp : Real.exp x < 1 ↔ x < 0 := Real.exp_lt_one_iff
  constructor
  · intro h
    exact hexp.mp (by linarith [h])
  · intro hx
    have hlt : Real.exp x < 1 := hexp.mpr hx
    linarith [hlt]

/-- **Singlet Rotation–Horizon Bridge**:
For positive inverse temperature `β > 0`, the co-rotating Fermi-Dirac occupation
`KerrUnruhFermionicHorizonBridge.kerrFermiOcc β Ω m (1 / 2)` exceeds `1 / 2` (population inversion)
if and only if `Ω > 2m`. -/
theorem singlet_kerr_occupation_inversion {β m Ω : ℝ} (hβ : 0 < β) :
    (1 / 2 : ℝ) < kerrFermiOcc β Ω m (1 / 2) ↔ 2 * m < Ω := by
  unfold kerrFermiOcc InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry.fermiOccupation
  rw [real_fermi_inversion_aux, mul_neg_iff]
  constructor
  · rintro (⟨_, hm⟩ | ⟨hbn, _⟩)
    · linarith
    · linarith
  · intro hSuper
    refine Or.inl ⟨hβ, ?_⟩
    linarith

/-! ### Part 3: Doubled Minkowski Bosonic Triplet Krein-Collision & Exponential Instability -/

/-- Two-sheet bosonic triplet Hamiltonian density `H_B = [[δ, γ], [γ, δ]]` with co-rotating
detuning `δ` (including `-Ω m_s` shift) and inter-sheet parametric pair coupling `γ`. -/
def tripletKreinEnergy (δ γ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![δ, γ; γ, δ]

/-- Real `𝒦`-self-adjoint time-evolution generator `G(δ, γ) = Z * H_B = [[δ, γ], [-γ, -δ]]`. -/
def tripletKreinGen (δ γ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  zCut2 * tripletKreinEnergy δ γ

/-- Complexified `2 × 2` Krein generator `G(δ, γ)`. -/
def tripletKreinGenC (δ γ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (tripletKreinGen δ γ).map Complex.ofRealHom

/-- Complexified `2 × 2` sheet-Krein signature matrix `Z`. -/
def zCut2C : Matrix (Fin 2) (Fin 2) ℂ :=
  zCut2.map Complex.ofRealHom

theorem exists_noncomm_mat2_real_spin :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  exists_noncomm_mat2_real

theorem exists_noncomm_mat2_complex_spin :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  refine ⟨tripletKreinGenC 1 1, zCut2C, fun h => ?_⟩
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  simp [tripletKreinGenC, tripletKreinGen, zCut2C, zCut2, tripletKreinEnergy,
    Matrix.mul_apply, Complex.ext_iff] at h01
  norm_num at h01

/-- Fundamental Krein algebraic properties of `tripletKreinGen δ γ`:
1. `𝒦`-self-adjointness `Z G = Gᵀ Z`,
2. Minimal polynomial square `G² = (δ² - γ²) I₂`,
3. Vanishing trace and exact determinant `γ² - δ²`. -/
theorem tripletKreinGen_krein_selfAdjoint_and_sq (δ γ : ℝ) :
    zCut2 * tripletKreinGen δ γ = (tripletKreinGen δ γ)ᵀ * zCut2 ∧
    tripletKreinGen δ γ * tripletKreinGen δ γ = (δ ^ 2 - γ ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    Matrix.trace (tripletKreinGen δ γ) = 0 ∧
    Matrix.det (tripletKreinGen δ γ) = γ ^ 2 - δ ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [tripletKreinGen, zCut2, tripletKreinEnergy, Matrix.mul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      (simp [tripletKreinGen, zCut2, tripletKreinEnergy, Matrix.mul_apply]; try ring)
  · simp [tripletKreinGen, zCut2, tripletKreinEnergy, Matrix.trace, Matrix.diag, Matrix.mul_apply]
  · rw [Matrix.det_fin_two]
    simp [tripletKreinGen, zCut2, tripletKreinEnergy, Matrix.mul_apply]
    ring

/-- **Critical Krein-Collision Nilpotent Jordan Cell (`δ = γ ≠ 0`)**:
At the exact superradiant threshold `δ = γ ≠ 0`, `G(γ, γ)` is nonzero (`≠ 0`), nilpotent
(`G(γ, γ)² = 0`), and its evolution flow `(1 + t • G)` satisfies `(1 + t G)(1 + s G) = 1 + (t + s) G`
(non-semisimple linear-in-`t` secular instability). -/
theorem tripletKreinGen_critical_jordan_cell {γ : ℝ} (hγ : γ ≠ 0) :
    tripletKreinGen γ γ ≠ 0 ∧
    tripletKreinGen γ γ * tripletKreinGen γ γ = 0 ∧
    ∀ t s : ℝ,
      (1 + t • tripletKreinGen γ γ) * (1 + s • tripletKreinGen γ γ) =
        1 + (t + s) • tripletKreinGen γ γ := by
  have hSq0 : tripletKreinGen γ γ * tripletKreinGen γ γ = 0 := by
    have hSq := (tripletKreinGen_krein_selfAdjoint_and_sq γ γ).2.1
    rw [sub_self, zero_smul] at hSq
    exact hSq
  refine ⟨?_, hSq0, ?_⟩
  · intro hZero
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hZero
    simp [tripletKreinGen, zCut2, tripletKreinEnergy, Matrix.mul_apply] at h00
    exact hγ h00
  · intro t s
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      hSq0, smul_zero, add_zero, add_assoc, add_smul]

private lemma complex_exp_add_deriv_aux {a b : ℝ} (hab : 0 < b ^ 2 - a ^ 2) :
    let lam0 := Real.sqrt (b ^ 2 - a ^ 2)
    ((-I) • tripletKreinGenC a b).mulVec ![(b : ℂ), -(a : ℂ) + I * (lam0 : ℂ)] =
      (lam0 : ℂ) • ![(b : ℂ), -(a : ℂ) + I * (lam0 : ℂ)] ∧
    dotProduct (star ![(b : ℂ), -(a : ℂ) + I * (lam0 : ℂ)])
      (zCut2C.mulVec ![(b : ℂ), -(a : ℂ) + I * (lam0 : ℂ)]) = 0 := by
  have hMulSq : Real.sqrt (b ^ 2 - a ^ 2) * Real.sqrt (b ^ 2 - a ^ 2) = b ^ 2 - a ^ 2 :=
    Real.mul_self_sqrt hab.le
  constructor
  · ext i
    fin_cases i
    · simp only [Matrix.mulVec, dotProduct, tripletKreinGenC, tripletKreinGen, zCut2,
        tripletKreinEnergy, Complex.ext_iff]
      constructor
      · simp [Fin.sum_univ_two]; ring
      · simp [Fin.sum_univ_two]; ring
    · simp only [Matrix.mulVec, dotProduct, tripletKreinGenC, tripletKreinGen, zCut2,
        tripletKreinEnergy, Complex.ext_iff]
      constructor
      · simp [Fin.sum_univ_two]; ring
      · simp [Fin.sum_univ_two, hMulSq]; ring
  · rw [Complex.ext_iff]
    constructor
    · simp [zCut2C, zCut2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hMulSq]
      ring
    · simp [zCut2C, zCut2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring

/-- **Supercritical Dynamical Krein Instability (`|δ| < |γ|`) & Krein-Null Cone Localization**:
Whenever `|δ| < |γ|`, setting `lam0 = √(γ² - δ²) > 0` and `v_grow = [γ, -δ + i lam0]ᵀ`:
1. `((-i) G).mulVec v_grow = lam0 • v_grow` (strictly positive real exponential growth eigenvalue),
2. `dotProduct (star v_grow) (Z.mulVec v_grow) = 0` (the growing mode has zero Krein norm),
3. `t ↦ exp(lam0 * t) • v_grow` is an exact exponentially growing solution to `dψ/dt = (-i G) ψ`. -/
theorem tripletKreinGen_supercritical_exponential_instability {δ γ : ℝ} (hInst : |δ| < |γ|) :
    let lam0 := Real.sqrt (γ ^ 2 - δ ^ 2)
    let v_grow : Fin 2 → ℂ := ![(γ : ℂ), -(δ : ℂ) + I * (lam0 : ℂ)]
    0 < lam0 ∧
    v_grow ≠ 0 ∧
    ((-I) • tripletKreinGenC δ γ).mulVec v_grow = (lam0 : ℂ) • v_grow ∧
    dotProduct (star v_grow) (zCut2C.mulVec v_grow) = 0 ∧
    ∀ t : ℝ, ∀ i : Fin 2,
      HasDerivAt (fun τ : ℝ => (Real.exp (lam0 * τ) : ℂ) * v_grow i)
        ((((-I) • tripletKreinGenC δ γ).mulVec
          (fun j => (Real.exp (lam0 * t) : ℂ) * v_grow j)) i) t := by
  have hDiff : 0 < γ ^ 2 - δ ^ 2 := sub_pos.mpr (sq_lt_sq.mpr hInst)
  have hLamPos : 0 < Real.sqrt (γ ^ 2 - δ ^ 2) := Real.sqrt_pos.mpr hDiff
  have hGammaNe : γ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hInst
    exact not_lt_of_ge (abs_nonneg δ) hInst
  have hEigAndNull := complex_exp_add_deriv_aux hDiff
  have hvNe : (![(γ : ℂ), -(δ : ℂ) + I * (Real.sqrt (γ ^ 2 - δ ^ 2) : ℂ)] : Fin 2 → ℂ) ≠ 0 := by
    intro h0
    have h00 := congrArg (fun f : Fin 2 → ℂ => f 0) h0
    simp [Complex.ext_iff] at h00
    exact hGammaNe h00
  refine ⟨hLamPos, hvNe, hEigAndNull.1, hEigAndNull.2, ?_⟩
  intro t i
  have hlin : HasDerivAt (fun τ : ℝ => Real.sqrt (γ ^ 2 - δ ^ 2) * τ)
      (Real.sqrt (γ ^ 2 - δ ^ 2) * 1) t :=
    (hasDerivAt_id t).const_mul (Real.sqrt (γ ^ 2 - δ ^ 2))
  have hexpR : HasDerivAt (fun τ : ℝ => Real.exp (Real.sqrt (γ ^ 2 - δ ^ 2) * τ))
      (Real.exp (Real.sqrt (γ ^ 2 - δ ^ 2) * t) * (Real.sqrt (γ ^ 2 - δ ^ 2) * 1)) t :=
    hlin.exp
  have hexpC : HasDerivAt (fun τ : ℝ => (Real.exp (Real.sqrt (γ ^ 2 - δ ^ 2) * τ) : ℂ))
      ((Real.exp (Real.sqrt (γ ^ 2 - δ ^ 2) * t) * Real.sqrt (γ ^ 2 - δ ^ 2) : ℝ) : ℂ) t := by
    have hcomp := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hexpR
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, mul_one] using hcomp
  have hDeriv := hexpC.mul_const (![(γ : ℂ), -(δ : ℂ) + I * (Real.sqrt (γ ^ 2 - δ ^ 2) : ℂ)] i)
  have hScale :
      ((((-I) • tripletKreinGenC δ γ).mulVec
        (fun j => (Real.exp (Real.sqrt (γ ^ 2 - δ ^ 2) * t) : ℂ) *
          ![(γ : ℂ), -(δ : ℂ) + I * (Real.sqrt (γ ^ 2 - δ ^ 2) : ℂ)] j)) i) =
        ((Real.exp (Real.sqrt (γ ^ 2 - δ ^ 2) * t) * Real.sqrt (γ ^ 2 - δ ^ 2) : ℝ) : ℂ) *
          ![(γ : ℂ), -(δ : ℂ) + I * (Real.sqrt (γ ^ 2 - δ ^ 2) : ℂ)] i := by
    let sC : ℂ := (Real.exp (Real.sqrt (γ ^ 2 - δ ^ 2) * t) : ℂ)
    have hVec :
        (fun j => (Real.exp (Real.sqrt (γ ^ 2 - δ ^ 2) * t) : ℂ) *
          ![(γ : ℂ), -(δ : ℂ) + I * (Real.sqrt (γ ^ 2 - δ ^ 2) : ℂ)] j) =
          sC • ![(γ : ℂ), -(δ : ℂ) + I * (Real.sqrt (γ ^ 2 - δ ^ 2) : ℂ)] := rfl
    rw [hVec, Matrix.mulVec_smul, Pi.smul_apply, hEigAndNull.1, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, ← mul_assoc]
    dsimp [sC]
    rw [← Complex.ofReal_mul]
  rw [hScale]
  exact hDeriv

/-! ### Part 4: Lift onto Signature-`(4,4)` Doubled Minkowski Carrier & Loxodromic Precession -/

/-- Signature-`(4,4)` doubled-Minkowski Krein triplet instability generator
`𝒦_diag * (H_B(δ, γ) ⊗ η_{1,3})` on `Fin 2 × Fin 4`. -/
def doubledMinkowskiTripletGen (δ γ : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  doubledMinkowskiDiag * (tripletKreinEnergy δ γ ⊗ₖ minkowski4)

theorem exists_noncomm_mat2x4_real_spin :
    ∃ A B : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ, A * B ≠ B * A :=
  exists_noncomm_mat2x4_real

/-- Exact Kronecker factorization `doubledMinkowskiTripletGen δ γ = tripletKreinGen δ γ ⊗ₖ I₄`
using `η_{1,3}² = I₄`. -/
theorem doubledMinkowskiTripletGen_eq_kronecker (δ γ : ℝ) :
    doubledMinkowskiTripletGen δ γ = tripletKreinGen δ γ ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  have hM2 : minkowski4 * minkowski4 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [minkowski4, Matrix.mul_apply, Fin.sum_univ_four]
  unfold doubledMinkowskiTripletGen doubledMinkowskiDiag tripletKreinGen
  rw [← Matrix.mul_kronecker_mul, hM2]

/-- Squared generator `(δ² - γ²) • I₈` on the doubled `(4,4)` Minkowski carrier. -/
theorem doubledMinkowskiTripletGen_sq (δ γ : ℝ) :
    doubledMinkowskiTripletGen δ γ * doubledMinkowskiTripletGen δ γ =
      (δ ^ 2 - γ ^ 2) • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) := by
  rw [doubledMinkowskiTripletGen_eq_kronecker, ← Matrix.mul_kronecker_mul, one_mul,
    (tripletKreinGen_krein_selfAdjoint_and_sq δ γ).2.1]
  ext ⟨a, i⟩ ⟨b, j⟩
  by_cases ha : a = b <;> by_cases hi : i = j <;>
    simp [Matrix.kroneckerMap_apply, ha, hi]

/-- Critical Jordan nilpotency lifted onto the `8 × 8` doubled Minkowski carrier (`δ = γ ≠ 0`). -/
theorem doubledMinkowskiTripletGen_critical_nilpotent {γ : ℝ} (hγ : γ ≠ 0) :
    doubledMinkowskiTripletGen γ γ ≠ 0 ∧
    doubledMinkowskiTripletGen γ γ * doubledMinkowskiTripletGen γ γ = 0 := by
  refine ⟨?_, ?_⟩
  · intro hZero
    have h00 := congrArg
      (fun M : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ => M (0, 0) (0, 0)) hZero
    rw [doubledMinkowskiTripletGen_eq_kronecker] at h00
    simp [tripletKreinGen, zCut2, tripletKreinEnergy] at h00
    exact hγ h00
  · rw [doubledMinkowskiTripletGen_sq, sub_self, zero_smul]

/-- Joint non-Abelian local frame obstruction tying 4D Minkowski loxodromic non-commutativity
(`K1 * J3 ≠ J3 * K1`) to local `su(2)` spin-frame non-commutativity (`spinX * spinY ≠ spinY * spinX`). -/
theorem loxodromic_boost_rotation_frame_obstruction :
    K1 * J3 ≠ J3 * K1 ∧ spinX * spinY ≠ spinY * spinX := by
  refine ⟨K1_mul_J3_ne, ?_⟩
  intro h
  have hComm := su2_commutation_relations.1
  rw [h, sub_self] at hComm
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) hComm
  simp [spinZ, Complex.ext_iff] at h00

/-! ### Part 5: Real `Cl(1,1) ≅ M₂(ℝ)` Dirac Spin-Exchange & Singlet → Triplet Condensation (`ΔE = J - Ω`) -/

/-- Antisymmetric real `Cl(1,1)` symplectic generator `ε = [[0, 1], [-1, 0]]` (`ε² = -I₂`). -/
def eps2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- Realified 3D spin-exchange operator `Σ_spin = X ⊗ X + Z ⊗ Z - ε ⊗ ε ∈ M_{2×2}(ℝ)`. -/
def spinExchange4 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  xMir2 ⊗ₖ xMir2 + zCut2 ⊗ₖ zCut2 - eps2 ⊗ₖ eps2

/-- Permutation / swap operator `P_swap = ½ (I₄ + Σ_spin)` on `ℝ² ⊗ ℝ²`. -/
def swapOp4 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  (1 / 2 : ℝ) • (1 + spinExchange4)

/-- Real 1D Spin-0 Singlet projector `P_singlet = ½ (I₄ - P_swap)` (`Tr = 1`). -/
def singletProj4 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  (1 / 2 : ℝ) • (1 - swapOp4)

/-- Real 3D Spin-1 Triplet projector `P_triplet = ½ (I₄ + P_swap)` (`Tr = 3`). -/
def tripletProj4 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  (1 / 2 : ℝ) • (1 + swapOp4)

/-- Real longitudinal spin generator `S_z = ½ (Z ⊗ I₂ + I₂ ⊗ Z)` on `ℝ² ⊗ ℝ²`. -/
def totalSpinZ4 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  (1 / 2 : ℝ) • (zCut2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) +
    (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ zCut2)

theorem exists_noncomm_mat2x2_real_spin :
    ∃ A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨zCut2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ),
    xMir2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ), fun h => ?_⟩
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, one_mul] at h
  have h01 := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ => M (0, 0) (1, 0)) h
  simp [zCut2, xMir2] at h01
  norm_num at h01

private lemma neg_kron_neg (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    (-A) ⊗ₖ (-B) = A ⊗ₖ B := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [Matrix.kroneckerMap_apply]

private lemma neg_kron_left (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [Matrix.kroneckerMap_apply]

private lemma kron_neg_right (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [Matrix.kroneckerMap_apply]

private lemma one_kron_one_real :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 :=
  Matrix.one_kronecker_one

private lemma pauli2_mul_table :
    (zCut2 * zCut2 = (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (xMir2 * xMir2 = (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (eps2 * eps2 = -(1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (zCut2 * xMir2 = eps2) ∧ (xMir2 * zCut2 = -eps2) ∧
    (zCut2 * eps2 = xMir2) ∧ (eps2 * zCut2 = -xMir2) ∧
    (xMir2 * eps2 = -zCut2) ∧ (eps2 * xMir2 = zCut2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [zCut2, xMir2, eps2, Matrix.mul_apply, Fin.sum_univ_two])

private lemma spinExchange4_sq :
    spinExchange4 * spinExchange4 =
      (3 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) - (2 : ℝ) • spinExchange4 := by
  have hT := pauli2_mul_table
  unfold spinExchange4
  rw [sub_mul, add_mul, mul_sub, mul_sub, mul_sub, mul_add, mul_add, mul_add]
  simp only [← Matrix.mul_kronecker_mul, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2.1, hT.2.2.2.2.1,
    hT.2.2.2.2.2.1, hT.2.2.2.2.2.2.1, hT.2.2.2.2.2.2.2.1, hT.2.2.2.2.2.2.2.2,
    neg_kron_neg, one_kron_one_real]
  module

private lemma totalSpinZ4_mul_singlet_blocks :
    (zCut2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) + (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ zCut2) *
        (xMir2 ⊗ₖ xMir2 - eps2 ⊗ₖ eps2) = 0 ∧
    (zCut2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) + (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ zCut2) *
        (1 - zCut2 ⊗ₖ zCut2) = 0 ∧
    (xMir2 ⊗ₖ xMir2 - eps2 ⊗ₖ eps2) *
        (zCut2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) + (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ zCut2) = 0 ∧
    (1 - zCut2 ⊗ₖ zCut2) *
        (zCut2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) + (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ zCut2) = 0 := by
  have hT := pauli2_mul_table
  rw [← one_kron_one_real]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [add_mul, mul_sub, mul_sub]
    simp only [← Matrix.mul_kronecker_mul, one_mul, hT.2.2.2.1, hT.2.2.2.2.2.1]
    abel
  · rw [add_mul, mul_sub, mul_sub]
    simp only [← Matrix.mul_kronecker_mul, one_mul, mul_one, hT.1]
    abel
  · rw [mul_add, sub_mul, sub_mul]
    simp only [← Matrix.mul_kronecker_mul, mul_one, hT.2.2.2.2.1, hT.2.2.2.2.2.2.1,
      neg_kron_left, kron_neg_right]
    abel
  · rw [mul_add, sub_mul, sub_mul]
    simp only [← Matrix.mul_kronecker_mul, one_mul, mul_one, hT.1]
    abel

/-- **Real `Cl(1,1)` Singlet–Triplet Decomposition (`2 ⊗ 2 = 1 ⊕ 3`) & Casimir Splitting**:
Purely over `ℝ` (zero complex `i`), `P_swap² = I₄`, `singletProj4` (`Tr = 1`) and `tripletProj4`
(`Tr = 3`) form complete orthogonal projectors splitting `spinExchange4` into eigenvalues `-3` and
`+1`, with the singlet projector strictly invariant under `totalSpinZ4`. -/
theorem real_singlet_triplet_decomposition_and_casimir_splitting :
    (swapOp4 * swapOp4 = 1 ∧ Matrix.trace swapOp4 = 2) ∧
    (singletProj4 + tripletProj4 = 1 ∧
     singletProj4 * singletProj4 = singletProj4 ∧
     tripletProj4 * tripletProj4 = tripletProj4 ∧
     singletProj4 * tripletProj4 = 0 ∧
     Matrix.trace singletProj4 = 1 ∧
     Matrix.trace tripletProj4 = 3) ∧
    (spinExchange4 * singletProj4 = (-3 : ℝ) • singletProj4 ∧
     spinExchange4 * tripletProj4 = tripletProj4) ∧
    (totalSpinZ4 * singletProj4 = 0 ∧
     totalSpinZ4 * tripletProj4 = tripletProj4 * totalSpinZ4) := by
  have hSq : spinExchange4 * spinExchange4 =
      (3 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) - (2 : ℝ) • spinExchange4 :=
    spinExchange4_sq
  have hSwap2 : swapOp4 * swapOp4 = 1 := by
    unfold swapOp4
    simp only [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add,
      one_mul, mul_one, hSq]
    module
  have hAdd : singletProj4 + tripletProj4 = 1 := by
    unfold singletProj4 tripletProj4
    module
  have hS2 : singletProj4 * singletProj4 = singletProj4 := by
    unfold singletProj4
    simp only [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub,
      one_mul, mul_one, hSwap2]
    module
  have hT2 : tripletProj4 * tripletProj4 = tripletProj4 := by
    unfold tripletProj4
    simp only [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add,
      one_mul, mul_one, hSwap2]
    module
  have hST : singletProj4 * tripletProj4 = 0 := by
    unfold singletProj4 tripletProj4
    simp only [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_add,
      one_mul, mul_one, hSwap2]
    module
  have hExS : spinExchange4 * singletProj4 = (-3 : ℝ) • singletProj4 := by
    unfold singletProj4 swapOp4
    rw [Matrix.mul_smul, mul_sub, mul_one, Matrix.mul_smul, mul_add, mul_one, hSq]
    module
  have hExT : spinExchange4 * tripletProj4 = tripletProj4 := by
    unfold tripletProj4 swapOp4
    rw [Matrix.mul_smul, mul_add, mul_one, Matrix.mul_smul, mul_add, mul_one, hSq]
    module
  have hZBlocks := totalSpinZ4_mul_singlet_blocks
  have hSingletForm : singletProj4 =
      (1 / 4 : ℝ) • ((1 - zCut2 ⊗ₖ zCut2) - (xMir2 ⊗ₖ xMir2 - eps2 ⊗ₖ eps2)) := by
    unfold singletProj4 swapOp4 spinExchange4
    module
  have hZS : totalSpinZ4 * singletProj4 = 0 := by
    rw [hSingletForm]
    unfold totalSpinZ4
    rw [Matrix.smul_mul, Matrix.mul_smul, mul_sub, hZBlocks.2.1, hZBlocks.1, sub_zero, smul_zero,
      smul_zero]
  have hSZ : singletProj4 * totalSpinZ4 = 0 := by
    rw [hSingletForm]
    unfold totalSpinZ4
    rw [Matrix.smul_mul, Matrix.mul_smul, sub_mul, hZBlocks.2.2.2, hZBlocks.2.2.1, sub_zero,
      smul_zero, smul_zero]
  have hZT : totalSpinZ4 * tripletProj4 = tripletProj4 * totalSpinZ4 := by
    have hTriForm : tripletProj4 = 1 - singletProj4 := eq_sub_of_add_eq' hAdd
    rw [hTriForm, mul_sub, sub_mul, mul_one, one_mul, hZS, hSZ]
  refine ⟨⟨hSwap2, ?_⟩, ⟨hAdd, hS2, hT2, hST, ?_, ?_⟩, ⟨hExS, hExT⟩, ⟨hZS, hZT⟩⟩
  · simp [swapOp4, spinExchange4, zCut2, xMir2, eps2, Matrix.trace, Matrix.diag,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num
  · simp [singletProj4, swapOp4, spinExchange4, zCut2, xMir2, eps2, Matrix.trace, Matrix.diag,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num
  · simp [tripletProj4, swapOp4, spinExchange4, zCut2, xMir2, eps2, Matrix.trace, Matrix.diag,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num

/-- Rotating-frame two-spin Hamiltonian `H_rot(J, Ω) = (J / 4) • Σ_spin - Ω • S_z` over `ℝ`. -/
def rotatingSpinHamiltonian (J Ω : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  (J / 4 : ℝ) • spinExchange4 - Ω • totalSpinZ4

/-- Unnormalized real Singlet state `ψ_S = e₀ ⊗ e₁ - e₁ ⊗ e₀`. -/
def singletState : Fin 2 × Fin 2 → ℝ
  | (0, 0) => 0
  | (0, 1) => 1
  | (1, 0) => -1
  | (1, 1) => 0

/-- Co-rotating real `m = +1` Triplet state `ψ_{T,+1} = e₀ ⊗ e₀`. -/
def tripletPlusState : Fin 2 × Fin 2 → ℝ
  | (0, 0) => 1
  | (0, 1) => 0
  | (1, 0) => 0
  | (1, 1) => 0

private lemma real_rot_gap_iff (J Ω : ℝ) :
    ((1 / 4 : ℝ) * J - Ω) - -(3 / 4 : ℝ) * J = J - Ω ∧
    (Ω < J ↔ -(3 / 4 : ℝ) * J < (1 / 4 : ℝ) * J - Ω) ∧
    (Ω = J ↔ (1 / 4 : ℝ) * J - Ω = -(3 / 4 : ℝ) * J) ∧
    (J < Ω ↔ (1 / 4 : ℝ) * J - Ω < -(3 / 4 : ℝ) * J) := by
  refine ⟨by ring, ⟨fun h => by linarith [h], fun h => by linarith [h]⟩,
    ⟨fun h => by linarith [h], fun h => by linarith [h]⟩,
    ⟨fun h => by linarith [h], fun h => by linarith [h]⟩⟩

private lemma real_rot_eig_scalars (J : ℝ) :
    (J / 4 : ℝ) * (-3 : ℝ) = -(3 / 4 : ℝ) * J ∧ (J / 4 : ℝ) = (1 / 4 : ℝ) * J := by
  constructor <;> ring

/-- **Real Rotating-Frame Spin-Exchange Spectrum & Singlet → Triplet Condensation (`ΔE = J - Ω`)**:
The Singlet state remains fixed at energy `E_S = -(3 / 4) * J` while the co-rotating `m = +1`
Triplet state shifts to `E_{T,+1} = (1 / 4) * J - Ω`, yielding exact excitation gap `E_{T,+1} - E_S = J - Ω`
and destabilizing the Singlet vacuum whenever `J < Ω`. -/
theorem real_rotating_frame_singlet_triplet_instability (J Ω : ℝ) :
    let H := rotatingSpinHamiltonian J Ω
    let E_S := -(3 / 4 : ℝ) * J
    let E_T1 := (1 / 4 : ℝ) * J - Ω
    (singletProj4.mulVec singletState = singletState) ∧
    (H.mulVec singletState = E_S • singletState) ∧
    (tripletProj4.mulVec tripletPlusState = tripletPlusState) ∧
    (totalSpinZ4.mulVec tripletPlusState = tripletPlusState) ∧
    (H.mulVec tripletPlusState = E_T1 • tripletPlusState) ∧
    (E_T1 - E_S = J - Ω) ∧
    (Ω < J ↔ E_S < E_T1) ∧
    (Ω = J ↔ E_T1 = E_S) ∧
    (J < Ω ↔ E_T1 < E_S) := by
  dsimp
  have hGap := real_rot_gap_iff J Ω
  have hDecomp := real_singlet_triplet_decomposition_and_casimir_splitting
  have hPS_vec : singletProj4.mulVec singletState = singletState := by
    ext ⟨i₁, i₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;>
      (simp [singletProj4, swapOp4, spinExchange4, singletState, zCut2, xMir2, eps2,
        Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; try norm_num)
  have hPT_vec : tripletProj4.mulVec tripletPlusState = tripletPlusState := by
    ext ⟨i₁, i₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;>
      (simp [tripletProj4, swapOp4, spinExchange4, tripletPlusState, zCut2, xMir2, eps2,
        Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; try norm_num)
  have hZT_vec : totalSpinZ4.mulVec tripletPlusState = tripletPlusState := by
    ext ⟨i₁, i₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;>
      (simp [totalSpinZ4, tripletPlusState, zCut2,
        Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; try norm_num)
  have hExS_vec : spinExchange4.mulVec singletState = (-3 : ℝ) • singletState := by
    calc
      spinExchange4.mulVec singletState = spinExchange4.mulVec (singletProj4.mulVec singletState) := by
        rw [hPS_vec]
      _ = (spinExchange4 * singletProj4).mulVec singletState := Matrix.mulVec_mulVec _ _ _
      _ = ((-3 : ℝ) • singletProj4).mulVec singletState := by rw [hDecomp.2.2.1.1]
      _ = (-3 : ℝ) • singletState := by rw [Matrix.smul_mulVec, hPS_vec]
  have hZS_vec : totalSpinZ4.mulVec singletState = 0 := by
    calc
      totalSpinZ4.mulVec singletState = totalSpinZ4.mulVec (singletProj4.mulVec singletState) := by
        rw [hPS_vec]
      _ = (totalSpinZ4 * singletProj4).mulVec singletState := Matrix.mulVec_mulVec _ _ _
      _ = (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ).mulVec singletState := by
        rw [hDecomp.2.2.2.1]
      _ = 0 := Matrix.zero_mulVec _
  have hExT_vec : spinExchange4.mulVec tripletPlusState = tripletPlusState := by
    calc
      spinExchange4.mulVec tripletPlusState =
          spinExchange4.mulVec (tripletProj4.mulVec tripletPlusState) := by rw [hPT_vec]
      _ = (spinExchange4 * tripletProj4).mulVec tripletPlusState := Matrix.mulVec_mulVec _ _ _
      _ = tripletProj4.mulVec tripletPlusState := by rw [hDecomp.2.2.1.2]
      _ = tripletPlusState := hPT_vec
  have hScalars := real_rot_eig_scalars J
  refine ⟨hPS_vec, ?_, hPT_vec, hZT_vec, ?_, hGap.1, hGap.2.1, hGap.2.2.1, hGap.2.2.2⟩
  · unfold rotatingSpinHamiltonian
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hExS_vec, hZS_vec,
      smul_zero, sub_zero, smul_smul, hScalars.1]
  · unfold rotatingSpinHamiltonian
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hExT_vec, hZT_vec,
      ← sub_smul, hScalars.2]

end InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
