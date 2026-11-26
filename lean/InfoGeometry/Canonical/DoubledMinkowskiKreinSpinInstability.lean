/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Singlet/Triplet Rotating-Spin-Frame Instability in the Doubled Minkowski Vacuum

Formalizes the finite-dimensional spinor and Krein matrix mechanisms governing local spin-frame
rotations and singlet vs. triplet stability on the doubled Minkowski vacuum:

1. **Spinor-Pair Singlet (`S = 0`) vs. Triplet (`S = 1`) Decomposition**:
   On `M₂(ℂ)` carrying `ℂ²₊ ⊗ ℂ²₋` with simultaneous local spin-frame action `U * M * Uᵀ`,
   every matrix decomposes uniquely into the Frobenius-orthogonal skew `singletMat` (`S = 0`)
   and symmetric `tripletPlus`/`tripletZero`/`tripletMinus` (`S = 1`, `m_s ∈ {+1, 0, -1}`).
   The singlet is invariant under all `U ∈ SL₂(ℂ)` (in particular non-commuting `SU(2)`
   rotations `spinRotZ` and `spinRotYC`), whereas `spinRotZ θ` splits `m_s = ±1` by `e^{±iθ}`.
2. **Doubled Minkowski Hyperbolic Bogoliubov Boosts & Spatial Frame Rotations**:
   Reuses `doubledMinkowskiDiag` from `DoubledMinkowskiBdGColimitBridge`: both hyperbolic
   Bogoliubov boosts `bogoliubovDoubled θ` and rotating spatial frames `rotatingFrameDoubled φ`
   preserve `doubledMinkowskiDiag` and commute, while `θ ≠ 0` generates nonzero inter-sheet
   Bogoliubov excitation `sinh θ ^ 2 > 0` from the `P₊` vacuum projector.
3. **Krein-Collision Dynamical Instability (`L = 𝒦 H`) vs. Fermionic BdG Stability**:
   For the Krein-self-adjoint generator `kreinGen2 ξ Δ Ω m_s = zCut2 * bosonicKreinH2 ξ Δ Ω m_s`,
   opposite-Krein-sign modes collide when `ξ² < Δ²`: eigenvalues acquire positive imaginary
   growth rate `γ = √(Δ² - ξ²) > 0` with zero real eigenvalues, contrasting with the
   unconditionally gapped fermionic BdG square `(ξ² + Δ²) • I`. At threshold `Δ = ξ ≠ 0`, the
   shifted generator is a nonzero nilpotent Jordan block (`L_shift² = 0`); in the stable regime
   `Δ² < ξ²` (`0 < ξ`), the two eigenvectors carry strictly opposite Krein inner-product signs.
4. **Rotating-Frame Coriolis Depairing of the Singlet vs. Triplet Immunity**:
   For the singlet pairing channel `singletRotatingBdg2 ξ m Ω = fermionicBdg2 ξ m - Ω I`, rotation
   stays gapped below the critical rate `Ω² < m²`, closes the gap with an explicit nonzero zero
   mode at `m² ≤ Ω²` (`Ω ≠ 0`), and turns the quasiparticle branch negative when
   `ξ² + m² < Ω²`. By contrast, the equal-spin triplet block `tripletRotatingBdg2 ξ m Ω` obeys
   `H_trip² = ((ξ - Ω)² + m²) I` and retains the uniform spectral gap `m² ‖v‖² ≤ ⟨v, H_trip² v⟩`
   for arbitrary rotation `Ω`.

Scope boundary: This module establishes finite-matrix operator identities and spectral/Krein
theorems; it does not assert continuum QFT Wightman axioms or interacting Yang–Mills dynamics.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open scoped Kronecker
open Matrix

namespace InfoGeometry.Canonical.DoubledMinkowskiKreinSpinInstability

open InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge

private lemma transpose_kronecker_real {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rfl

/-! ### Part 1: Singlet (`S = 0`) vs. Triplet (`S = 1`) Decomposition & `SU(2)` Frame Action -/

/-- Antisymmetric spin-singlet state (`S = 0`) on `ℂ²₊ ⊗ ℂ²₋`. -/
def singletMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- Symmetric spin-triplet state with `m_s = +1`. -/
def tripletPlus : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- Symmetric spin-triplet state with `m_s = 0`. -/
def tripletZero : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Symmetric spin-triplet state with `m_s = -1`. -/
def tripletMinus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

/-- Simultaneous local spin-frame action `U M Uᵀ` on two-sheet spinor bilinears. -/
def spinFrameAct (U M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  U * M * Uᵀ

/-- Local `SU(2)` spin-frame rotation around the `z`-axis by angle `θ`. -/
def spinRotZ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (Complex.I * ((θ : ℂ) / 2)), 0;
     0, Complex.exp (-(Complex.I * ((θ : ℂ) / 2)))]

/-- Local `SU(2)` spin-frame rotation around the `y`-axis by angle `θ`. -/
def spinRotYC (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (θ / 2) : ℂ), -(Real.sin (θ / 2) : ℂ);
     (Real.sin (θ / 2) : ℂ), (Real.cos (θ / 2) : ℂ)]

/-- Spin-`z` generator `S_z = (1 / 2) σ_z`. -/
def szGen : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 / 2 : ℂ), 0; 0, -(1 / 2 : ℂ)]

/-- Infinitesimal spin-frame action `J M + M Jᵀ` on two-sheet spinor bilinears. -/
def spinAdAction (J M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  J * M + M * Jᵀ

/-- Every `2 × 2` spinor-pair matrix decomposes into skew `singletMat` plus symmetric triplet
components, which are pairwise Frobenius-orthogonal (`Tr(Sᴴ T) = 0`). -/
theorem singlet_triplet_direct_sum (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = ((M 0 1 - M 1 0) / 2) • singletMat +
        (M 0 0 • tripletPlus + ((M 0 1 + M 1 0) / 2) • tripletZero + M 1 1 • tripletMinus) ∧
    Matrix.trace (singletMatᴴ * tripletPlus) = 0 ∧
    Matrix.trace (singletMatᴴ * tripletZero) = 0 ∧
    Matrix.trace (singletMatᴴ * tripletMinus) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [singletMat, tripletPlus, tripletZero, tripletMinus] <;> ring
  · simp [singletMat, tripletPlus, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_two]
  · simp [singletMat, tripletZero, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_two]
  · simp [singletMat, tripletMinus, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Under any `2 × 2` spin-frame change `U`, the singlet scales strictly by `U.det`. -/
theorem singlet_spinFrame_invariant (U : Matrix (Fin 2) (Fin 2) ℂ) :
    spinFrameAct U singletMat = U.det • singletMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinFrameAct, singletMat, Matrix.det_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

/-- Every unimodular frame transformation (`det U = 1`, including all of `SU(2)`) leaves the
spin-singlet invariant. -/
theorem singlet_spinFrame_invariant_of_det_one {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hdet : U.det = 1) :
    spinFrameAct U singletMat = singletMat := by
  rw [singlet_spinFrame_invariant, hdet, one_smul]

/-- `spinRotZ θ` and `spinRotYC θ` belong to `SU(2)` (`Uᴴ U = 1`, `det U = 1`) and do not
commute for general axes. -/
theorem spinRot_su2_and_noncomm (θ : ℝ) :
    ((spinRotZ θ)ᴴ * spinRotZ θ = 1 ∧ (spinRotZ θ).det = 1) ∧
    ((spinRotYC θ)ᴴ * spinRotYC θ = 1 ∧ (spinRotYC θ).det = 1) ∧
    spinRotZ Real.pi * spinRotYC Real.pi ≠ spinRotYC Real.pi * spinRotZ Real.pi := by
  have hexpZ : (starRingEnd ℂ) (Complex.exp (Complex.I * ((θ : ℂ) / 2))) *
      Complex.exp (Complex.I * ((θ : ℂ) / 2)) = 1 := by
    have hconj : (starRingEnd ℂ) (Complex.exp (Complex.I * ((θ : ℂ) / 2))) =
        Complex.exp (-(Complex.I * ((θ : ℂ) / 2))) := by
      rw [← Complex.exp_conj]
      simp only [map_mul, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      ring_nf
    rw [hconj, ← Complex.exp_add]
    simp
  have hexpZ' : (starRingEnd ℂ) (Complex.exp (-(Complex.I * ((θ : ℂ) / 2)))) *
      Complex.exp (-(Complex.I * ((θ : ℂ) / 2))) = 1 := by
    have hconj : (starRingEnd ℂ) (Complex.exp (-(Complex.I * ((θ : ℂ) / 2)))) =
        Complex.exp (Complex.I * ((θ : ℂ) / 2)) := by
      rw [← Complex.exp_conj]
      simp only [map_neg, map_mul, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      ring_nf
    rw [hconj, ← Complex.exp_add]
    simp
  have hdetZ : Complex.exp (Complex.I * ((θ : ℂ) / 2)) *
      Complex.exp (-(Complex.I * ((θ : ℂ) / 2))) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hsc : (Real.cos (θ / 2) : ℂ) ^ 2 + (Real.sin (θ / 2) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (θ / 2)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spinRotZ, Matrix.mul_apply, Fin.sum_univ_two]
    · exact hexpZ
    · exact hexpZ'
  · simp [spinRotZ, Matrix.det_fin_two, hdetZ]
  · have hc2 : (starRingEnd ℂ) (Complex.cos ((θ : ℂ) / 2)) = Complex.cos ((θ : ℂ) / 2) := by
      rw [← Complex.cos_conj]; simp only [map_div₀, Complex.conj_ofReal, map_ofNat]
    have hs2 : (starRingEnd ℂ) (Complex.sin ((θ : ℂ) / 2)) = Complex.sin ((θ : ℂ) / 2) := by
      rw [← Complex.sin_conj]; simp only [map_div₀, Complex.conj_ofReal, map_ofNat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spinRotYC, Matrix.mul_apply, Fin.sum_univ_two, hc2, hs2]
    · simpa [sq] using Complex.cos_sq_add_sin_sq ((θ : ℂ) / 2)
    · ring
    · ring
    · simpa [sq, add_comm] using Complex.cos_sq_add_sin_sq ((θ : ℂ) / 2)
  · simp only [spinRotYC, Matrix.det_fin_two_of]
    linear_combination hsc
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    have hexpPi : Complex.exp (Complex.I * ((Real.pi : ℂ) / 2)) = Complex.I := by
      rw [show Complex.I * ((Real.pi : ℂ) / 2) = (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) by
        push_cast; ring]
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      norm_num
    have hexpNegPi : Complex.exp (-(Complex.I * ((Real.pi : ℂ) / 2))) = -Complex.I := by
      rw [show -(Complex.I * ((Real.pi : ℂ) / 2)) = (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) by
        push_cast; ring]
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
      norm_num
    simp [spinRotZ, spinRotYC, Matrix.mul_apply, Fin.sum_univ_two, hexpPi, hexpNegPi] at h01
    have him := congrArg Complex.im h01
    norm_num at him

/-- Standalone non-commutativity witness for `SU(2)` local spin-frame rotations. -/
theorem exists_noncomm_spinRot :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  ⟨spinRotZ Real.pi, spinRotYC Real.pi, (spinRot_su2_and_noncomm 0).2.2⟩

/-- `spinRotZ θ` leaves `singletMat` and `tripletZero` fixed while phase-splitting
`tripletPlus` and `tripletMinus` by `e^{±iθ}`. -/
theorem triplet_spinRotZ_splitting (θ : ℝ) :
    spinFrameAct (spinRotZ θ) singletMat = singletMat ∧
    spinFrameAct (spinRotZ θ) tripletZero = tripletZero ∧
    spinFrameAct (spinRotZ θ) tripletPlus = Complex.exp (Complex.I * (θ : ℂ)) • tripletPlus ∧
    spinFrameAct (spinRotZ θ) tripletMinus =
      Complex.exp (-(Complex.I * (θ : ℂ))) • tripletMinus := by
  have h1 : Complex.exp (Complex.I * ((θ : ℂ) / 2)) *
      Complex.exp (-(Complex.I * ((θ : ℂ) / 2))) = 1 := by
    rw [← Complex.exp_add]; simp
  have hp : Complex.exp (Complex.I * ((θ : ℂ) / 2)) *
      Complex.exp (Complex.I * ((θ : ℂ) / 2)) = Complex.exp (Complex.I * (θ : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hm : Complex.exp (-(Complex.I * ((θ : ℂ) / 2))) *
      Complex.exp (-(Complex.I * ((θ : ℂ) / 2))) = Complex.exp (-(Complex.I * (θ : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  refine ⟨singlet_spinFrame_invariant_of_det_one (spinRot_su2_and_noncomm θ).1.2, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spinFrameAct, spinRotZ, tripletZero, Matrix.mul_apply, Fin.sum_univ_two]
    · rw [h1]
    · rw [mul_comm (Complex.exp (-(Complex.I * ((θ : ℂ) / 2)))), h1]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spinFrameAct, spinRotZ, tripletPlus, Matrix.mul_apply, Fin.sum_univ_two, hp]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spinFrameAct, spinRotZ, tripletMinus, Matrix.mul_apply, Fin.sum_univ_two, hm]

/-- Infinitesimal spin-`z` generator `szGen` annihilates `singletMat` and `tripletZero`, and has
eigenvalues `+1` on `tripletPlus` and `-1` on `tripletMinus`. -/
theorem spinAdAction_szGen_eigenvalues :
    spinAdAction szGen singletMat = 0 ∧
    spinAdAction szGen tripletZero = 0 ∧
    spinAdAction szGen tripletPlus = tripletPlus ∧
    spinAdAction szGen tripletMinus = -tripletMinus := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      rw [spinAdAction, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply,
        Fin.sum_univ_two, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;>
        simp [szGen, singletMat, tripletZero, tripletPlus, tripletMinus] <;> norm_num }

/-! ### Part 2: Hyperbolic Bogoliubov Boost & Rotating Spatial Frame on `Fin 2 × Fin 4` -/

/-- `2 × 2` hyperbolic Bogoliubov sheet boost `cosh θ I₂ + sinh θ X`. -/
def bogoliubovBoost2 (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Real.cosh θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sinh θ • xMir2

/-- Lifted hyperbolic Bogoliubov boost `B(θ) ⊗ I₄` on the doubled Minkowski carrier. -/
def bogoliubovDoubled (θ : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  bogoliubovBoost2 θ ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)

/-- Spatial `SO(3)` rotation about the `x₃`-axis inside Minkowski `Fin 4`. -/
def spatialRot4 (φ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     0, Real.cos φ, -Real.sin φ, 0;
     0, Real.sin φ, Real.cos φ, 0;
     0, 0, 0, 1]

/-- Lifted rotating spatial frame `I₂ ⊗ R(φ)` on the doubled Minkowski carrier. -/
def rotatingFrameDoubled (φ : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ spatialRot4 φ

/-- Sheet-`+` vacuum projector `P₊ = [[1, 0], [0, 0]]`. -/
def sheetProjPlus2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- Both hyperbolic Bogoliubov boosts and spatial frame rotations preserve `doubledMinkowskiDiag`
and commute, while any nonzero Bogoliubov boost excites `sinh θ ^ 2 > 0` hole-sheet density. -/
theorem doubled_minkowski_boost_and_rotation_symmetries (θ φ : ℝ) :
    ((bogoliubovDoubled θ)ᵀ * doubledMinkowskiDiag * bogoliubovDoubled θ = doubledMinkowskiDiag) ∧
    ((rotatingFrameDoubled φ)ᵀ * doubledMinkowskiDiag * rotatingFrameDoubled φ =
      doubledMinkowskiDiag) ∧
    (bogoliubovDoubled θ * rotatingFrameDoubled φ =
      rotatingFrameDoubled φ * bogoliubovDoubled θ) ∧
    ((bogoliubovBoost2 θ * sheetProjPlus2 * (bogoliubovBoost2 θ)ᵀ) 1 1 = Real.sinh θ ^ 2) ∧
    (θ ≠ 0 → 0 < (bogoliubovBoost2 θ * sheetProjPlus2 * (bogoliubovBoost2 θ)ᵀ) 1 1) := by
  have hBT : (bogoliubovBoost2 θ)ᵀ = bogoliubovBoost2 θ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bogoliubovBoost2, xMir2]
  have hBKB : (bogoliubovBoost2 θ)ᵀ * zCut2 * bogoliubovBoost2 θ = zCut2 := by
    rw [hBT]
    have hch := Real.cosh_sq_sub_sinh_sq θ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [bogoliubovBoost2, zCut2, xMir2, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring_nf <;> linarith [hch]
  have hRMR : (spatialRot4 φ)ᵀ * minkowski4 * spatialRot4 φ = minkowski4 := by
    have hsc := Real.sin_sq_add_cos_sq φ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spatialRot4, minkowski4, Matrix.mul_apply, Fin.sum_univ_four] <;>
      ring_nf <;> linarith [hsc]
  have hVac :
      (bogoliubovBoost2 θ * sheetProjPlus2 * (bogoliubovBoost2 θ)ᵀ) 1 1 = Real.sinh θ ^ 2 := by
    rw [hBT]
    simp [bogoliubovBoost2, sheetProjPlus2, xMir2, Matrix.mul_apply, Fin.sum_univ_two, sq]
  refine ⟨?_, ?_, ?_, hVac, ?_⟩
  · unfold bogoliubovDoubled doubledMinkowskiDiag
    rw [transpose_kronecker_real, Matrix.transpose_one, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hBKB]
  · unfold rotatingFrameDoubled doubledMinkowskiDiag
    rw [transpose_kronecker_real, Matrix.transpose_one, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hRMR]
  · unfold bogoliubovDoubled rotatingFrameDoubled
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]
  · intro hθ
    rw [hVac]
    have hsne : Real.sinh θ ≠ 0 := by
      intro hs
      rw [Real.sinh_eq] at hs
      have hexp : Real.exp θ = Real.exp (-θ) := by linarith
      exact hθ (by have := Real.exp_injective hexp; linarith)
    exact sq_pos_of_ne_zero hsne

/-! ### Part 3: Krein-Collision Dynamical Instability (`L = 𝒦 H`) vs. Fermionic BdG Stability -/

/-- `2 × 2` fermionic Bogoliubov–de Gennes block `[[ξ, Δ], [Δ, -ξ]]`. -/
def fermionicBdg2 (ξ Δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ξ, Δ; Δ, -ξ]

/-- `2 × 2` bosonic doubled Hamiltonian `H_Krein = [[ξ - Ω m_s, Δ], [Δ, ξ + Ω m_s]]` carrying
positive kinetic energy on both sheets prior to Krein-metric multiplication `L = 𝒦 H_Krein`. -/
def bosonicKreinH2 (ξ Δ Ω m_s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ξ - Ω * m_s, Δ; Δ, ξ + Ω * m_s]

/-- `2 × 2` Krein dynamical generator `L = [[ξ - Ω m_s, Δ], [-Δ, -(ξ + Ω m_s)]]`. -/
def kreinGen2 (ξ Δ Ω m_s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ξ - Ω * m_s, Δ; -Δ, -(ξ + Ω * m_s)]

/-- `kreinGen2` factors as `𝒦 H_Krein` (`zCut2 * bosonicKreinH2 ξ Δ Ω m_s`), is
`zCut2`-self-adjoint, and squares (after Coriolis shift) to `(ξ² - Δ²) I`, contrasting with the
gapped fermionic BdG square `(ξ² + Δ²) I`. -/
theorem kreinGen2_structure_and_sign_flip (ξ Δ Ω m_s : ℝ) :
    (kreinGen2 ξ Δ Ω m_s = zCut2 * bosonicKreinH2 ξ Δ Ω m_s) ∧
    (zCut2 * kreinGen2 ξ Δ Ω m_s = (kreinGen2 ξ Δ Ω m_s)ᵀ * zCut2) ∧
    ((kreinGen2 ξ Δ Ω m_s + (Ω * m_s) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
      (kreinGen2 ξ Δ Ω m_s + (Ω * m_s) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
      (ξ ^ 2 - Δ ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (fermionicBdg2 ξ Δ * fermionicBdg2 ξ Δ =
      (ξ ^ 2 + Δ ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        simp [kreinGen2, bosonicKreinH2, fermionicBdg2, zCut2, Matrix.mul_apply,
          Fin.sum_univ_two] <;> ring }

/-- **Krein-Collision Dynamical Instability (`ξ² < Δ²`)**:
Whenever pairing exceeds detuning (`ξ² < Δ²`), `kreinGen2 ξ Δ Ω m_s` admits an explicit nonzero
complex eigenvector with strictly positive exponential growth rate `γ = √(Δ² - ξ²) > 0`, and
possesses zero real eigenvectors. -/
theorem krein_collision_instability (ξ Δ Ω m_s : ℝ) (h : ξ ^ 2 < Δ ^ 2) :
    let γ : ℝ := Real.sqrt (Δ ^ 2 - ξ ^ 2)
    let v : Fin 2 → ℂ := ![(Δ : ℂ), -(ξ : ℂ) + Complex.I * (γ : ℂ)]
    let ev : ℂ := -((Ω * m_s : ℝ) : ℂ) + Complex.I * (γ : ℂ)
    0 < γ ∧
    v ≠ 0 ∧
    ev.im = γ ∧
    ((kreinGen2 ξ Δ Ω m_s).map Complex.ofReal).mulVec v = ev • v ∧
    (∀ (μ : ℝ) (w : Fin 2 → ℝ), (kreinGen2 ξ Δ Ω m_s).mulVec w = μ • w → w = 0) := by
  dsimp
  have hsub_pos : 0 < Δ ^ 2 - ξ ^ 2 := sub_pos.mpr h
  have hγ_pos : 0 < Real.sqrt (Δ ^ 2 - ξ ^ 2) := Real.sqrt_pos.mpr hsub_pos
  have hγ_sq : (Real.sqrt (Δ ^ 2 - ξ ^ 2) : ℂ) ^ 2 = ((Δ ^ 2 - ξ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt hsub_pos.le
  have hΔ_ne : Δ ≠ 0 := by
    intro h0
    rw [h0] at h
    nlinarith [sq_nonneg ξ]
  refine ⟨hγ_pos, ?_, ?_, ?_, ?_⟩
  · intro hv0
    have h0 := congrFun hv0 0
    simp [hΔ_ne] at h0
  · simp
  · ext i
    fin_cases i
    · simp [kreinGen2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · simp [kreinGen2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      exact sub_eq_zero.mp (by
        calc _ = (Real.sqrt (Δ ^ 2 - ξ ^ 2) : ℂ) ^ 2 * (-Complex.I ^ 2) -
                ((Δ : ℂ) ^ 2 - (ξ : ℂ) ^ 2) := by ring
          _ = (Real.sqrt (Δ ^ 2 - ξ ^ 2) : ℂ) ^ 2 - ((Δ ^ 2 - ξ ^ 2 : ℝ) : ℂ) := by
              rw [Complex.I_sq]; push_cast; ring
          _ = 0 := sub_eq_zero.mpr hγ_sq)
  · intro μ w hw
    let A := kreinGen2 ξ Δ Ω m_s + (Ω * m_s) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
    have hAw : A.mulVec w = (μ + Ω * m_s) • w := by
      simp only [A, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hw, add_smul]
    have hA2w : (A * A).mulVec w = ((μ + Ω * m_s) ^ 2) • w := by
      rw [← Matrix.mulVec_mulVec, hAw, Matrix.mulVec_smul, hAw, smul_smul, sq]
    rw [(kreinGen2_structure_and_sign_flip ξ Δ Ω m_s).2.2.1, Matrix.smul_mulVec,
      Matrix.one_mulVec] at hA2w
    have hc_ne : (ξ ^ 2 - Δ ^ 2) - (μ + Ω * m_s) ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg (μ + Ω * m_s)]
    ext i
    have hi := congrFun hA2w i
    have hzero : ((ξ ^ 2 - Δ ^ 2) - (μ + Ω * m_s) ^ 2) * w i = 0 := by
      simpa [sub_mul] using sub_eq_zero.mpr hi
    exact (mul_eq_zero.mp hzero).resolve_left hc_ne

/-- In the stable regime `Δ² < ξ²` (`0 < ξ`), `kreinGen2 ξ Δ Ω m_s` has two real eigenvectors
carrying strictly opposite Krein inner-product signs (`+` vs. `-`), explaining why collision
requires mixing opposite-signature sheets. -/
theorem krein_stable_opposite_signatures (ξ Δ Ω m_s : ℝ) (h : Δ ^ 2 < ξ ^ 2) (hξ : 0 < ξ) :
    let ω : ℝ := Real.sqrt (ξ ^ 2 - Δ ^ 2)
    let vPlus : Fin 2 → ℝ := ![ξ + ω, -Δ]
    let vMinus : Fin 2 → ℝ := ![Δ, -(ξ + ω)]
    (kreinGen2 ξ Δ Ω m_s).mulVec vPlus = (-Ω * m_s + ω) • vPlus ∧
    (kreinGen2 ξ Δ Ω m_s).mulVec vMinus = (-Ω * m_s - ω) • vMinus ∧
    0 < dotProduct vPlus (zCut2.mulVec vPlus) ∧
    dotProduct vMinus (zCut2.mulVec vMinus) < 0 := by
  dsimp
  have hsub_pos : 0 < ξ ^ 2 - Δ ^ 2 := sub_pos.mpr h
  have hω_pos : 0 < Real.sqrt (ξ ^ 2 - Δ ^ 2) := Real.sqrt_pos.mpr hsub_pos
  have hω_sq : Real.sqrt (ξ ^ 2 - Δ ^ 2) ^ 2 = ξ ^ 2 - Δ ^ 2 := Real.sq_sqrt hsub_pos.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i
    fin_cases i
    · simp [kreinGen2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      nlinarith [hω_sq]
    · simp [kreinGen2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
  · ext i
    fin_cases i
    · simp [kreinGen2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · simp [kreinGen2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      nlinarith [hω_sq]
  · simp only [zCut2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, cons_val_zero, cons_val_one,
      of_apply, cons_val', empty_val', cons_val_fin_one, zero_mul, zero_add, mul_neg]
    nlinarith [mul_pos hξ hω_pos, sq_nonneg (Real.sqrt (ξ ^ 2 - Δ ^ 2))]
  · simp only [zCut2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, cons_val_zero, cons_val_one,
      of_apply, cons_val', empty_val', cons_val_fin_one, zero_mul, zero_add, mul_neg]
    nlinarith [mul_pos hξ hω_pos, sq_nonneg (Real.sqrt (ξ ^ 2 - Δ ^ 2))]

/-- At the Krein collision threshold `Δ = ξ` (`ξ ≠ 0`), the shifted generator is a nonzero
nilpotent Jordan block (`L_shift ≠ 0` and `L_shift² = 0`). -/
theorem krein_collision_jordan_block (ξ Ω m_s : ℝ) (hξ : ξ ≠ 0) :
    let Lshift := kreinGen2 ξ ξ Ω m_s + (Ω * m_s) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
    Lshift ≠ 0 ∧ Lshift * Lshift = 0 := by
  dsimp
  refine ⟨?_, ?_⟩
  · intro h0
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h0
    simp [kreinGen2] at h00
    exact hξ h00
  · rw [(kreinGen2_structure_and_sign_flip ξ ξ Ω m_s).2.2.1]
    simp

/-! ### Part 4: Rotating-Frame Coriolis Depairing — Singlet Gap Closure vs. Triplet Immunity -/

/-- Singlet (`↑_+ ↔ ↓_-`) BdG block in a rotating local spin frame at rate `Ω`. -/
def singletRotatingBdg2 (ξ m Ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fermionicBdg2 ξ m - Ω • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- Equal-spin triplet (`↑_+ ↔ ↑_-`) BdG block in a rotating local spin frame at rate `Ω`. -/
def tripletRotatingBdg2 (ξ m Ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fermionicBdg2 (ξ - Ω) m

/-- **Singlet Gap Survival Below Critical Rotation & Supercritical Collapse**:
1. `det (singletRotatingBdg2 ξ m Ω) = Ω² - (ξ² + m²)`; for `Ω² < m²`, the singlet stays strictly
   gapped (`det < 0`) for all momenta `ξ`.
2. For `m² ≤ Ω²` (`Ω ≠ 0`), the gap closes at `ξc = √(Ω² - m²)` with an explicit nonzero zero
   mode `v ≠ 0`.
3. Inside `ξ² + m² < Ω²`, the lower Bogoliubov quasiparticle branch crosses below zero
   (`√(ξ² + m²) < |Ω|`). -/
theorem singletRotatingBdg2_depairing_threshold :
    (∀ ξ m Ω : ℝ, (singletRotatingBdg2 ξ m Ω).det = Ω ^ 2 - (ξ ^ 2 + m ^ 2)) ∧
    (∀ ξ m Ω : ℝ, Ω ^ 2 < m ^ 2 → (singletRotatingBdg2 ξ m Ω).det < 0) ∧
    (∀ m Ω : ℝ, m ^ 2 ≤ Ω ^ 2 → Ω ≠ 0 →
      let ξc := Real.sqrt (Ω ^ 2 - m ^ 2)
      (singletRotatingBdg2 ξc m Ω).det = 0 ∧
      ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ (singletRotatingBdg2 ξc m Ω).mulVec v = 0) ∧
    (∀ ξ m Ω : ℝ, ξ ^ 2 + m ^ 2 < Ω ^ 2 → Real.sqrt (ξ ^ 2 + m ^ 2) < |Ω|) := by
  have hDet : ∀ ξ m Ω : ℝ, (singletRotatingBdg2 ξ m Ω).det = Ω ^ 2 - (ξ ^ 2 + m ^ 2) := by
    intro ξ m Ω
    simp [singletRotatingBdg2, fermionicBdg2, Matrix.det_fin_two]
    ring
  refine ⟨hDet, ?_, ?_, ?_⟩
  · intro ξ m Ω h
    rw [hDet]
    nlinarith [sq_nonneg ξ]
  · intro m Ω h hΩ
    have hsub : 0 ≤ Ω ^ 2 - m ^ 2 := sub_nonneg.mpr h
    have hξc_sq : Real.sqrt (Ω ^ 2 - m ^ 2) ^ 2 = Ω ^ 2 - m ^ 2 := Real.sq_sqrt hsub
    have hξc_nn : 0 ≤ Real.sqrt (Ω ^ 2 - m ^ 2) := Real.sqrt_nonneg _
    refine ⟨?_, ?_⟩
    · rw [hDet, hξc_sq]
      ring
    · by_cases hpos : 0 < Ω
      · refine ⟨![Ω + Real.sqrt (Ω ^ 2 - m ^ 2), m], ?_, ?_⟩
        · intro hv0
          have h0 := congrFun hv0 0
          simp at h0
          linarith
        · ext i
          fin_cases i
          · simp [singletRotatingBdg2, fermionicBdg2, Matrix.mulVec, dotProduct,
              Fin.sum_univ_two]
            nlinarith [hξc_sq]
          · simp [singletRotatingBdg2, fermionicBdg2, Matrix.mulVec, dotProduct,
              Fin.sum_univ_two]
            ring
      · have hneg : Ω < 0 := lt_of_le_of_ne (not_lt.mp hpos) hΩ
        refine ⟨![m, Ω - Real.sqrt (Ω ^ 2 - m ^ 2)], ?_, ?_⟩
        · intro hv0
          have h1 := congrFun hv0 1
          simp at h1
          linarith
        · ext i
          fin_cases i
          · simp [singletRotatingBdg2, fermionicBdg2, Matrix.mulVec, dotProduct,
              Fin.sum_univ_two]
            ring
          · simp [singletRotatingBdg2, fermionicBdg2, Matrix.mulVec, dotProduct,
              Fin.sum_univ_two]
            nlinarith [hξc_sq]
  · intro ξ m Ω h
    rw [← Real.sqrt_sq_eq_abs Ω]
    exact Real.sqrt_lt_sqrt (by positivity) h

/-- **Equal-Spin Triplet Immunity**:
For any rotation rate `Ω` and nonzero pairing `m ≠ 0`, `tripletRotatingBdg2 ξ m Ω` obeys
`H_trip² = ((ξ - Ω)² + m²) I`, has strictly negative determinant, and preserves the uniform
spectral gap `m² ‖v‖² ≤ ⟨v, H_trip² v⟩`. -/
theorem tripletRotatingBdg2_always_gapped (ξ m Ω : ℝ) (hm : m ≠ 0) :
    (tripletRotatingBdg2 ξ m Ω * tripletRotatingBdg2 ξ m Ω =
      ((ξ - Ω) ^ 2 + m ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    ((tripletRotatingBdg2 ξ m Ω).det = -((ξ - Ω) ^ 2 + m ^ 2)) ∧
    ((tripletRotatingBdg2 ξ m Ω).det < 0) ∧
    (∀ v : Fin 2 → ℝ, m ^ 2 * dotProduct v v ≤
      dotProduct v ((tripletRotatingBdg2 ξ m Ω * tripletRotatingBdg2 ξ m Ω).mulVec v)) := by
  have hSq := (kreinGen2_structure_and_sign_flip (ξ - Ω) m 0 0).2.2.2
  change tripletRotatingBdg2 ξ m Ω * tripletRotatingBdg2 ξ m Ω =
    ((ξ - Ω) ^ 2 + m ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) at hSq
  have hDet : (tripletRotatingBdg2 ξ m Ω).det = -((ξ - Ω) ^ 2 + m ^ 2) := by
    simp [tripletRotatingBdg2, fermionicBdg2, Matrix.det_fin_two]
    ring
  have hm2 : 0 < m ^ 2 := sq_pos_of_ne_zero hm
  refine ⟨hSq, hDet, ?_, ?_⟩
  · rw [hDet]
    nlinarith [sq_nonneg (ξ - Ω)]
  · intro v
    rw [hSq, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    have hvv : 0 ≤ dotProduct v v := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
    nlinarith [sq_nonneg (ξ - Ω)]

end InfoGeometry.Canonical.DoubledMinkowskiKreinSpinInstability
