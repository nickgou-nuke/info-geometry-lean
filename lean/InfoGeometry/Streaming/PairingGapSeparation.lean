import InfoGeometry.Physics.NuclearWignerSupermultipletSymmetry
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Hermitian pairing blocks and the regularity of an Andreev energy formula

The Pauli basis is reused. The two-level Hermitian block is not a spatial
scattering solution or a topological superconducting system. A zero in the
short-junction scalar formula does not prove protected Majorana localization.
-/

noncomputable section
namespace InfoGeometry.Streaming.PairingGapSeparation

open InfoGeometry.Physics.NuclearWignerSupermultiplet

abbrev PairMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- The finite Hermitian reduced pairing block with top-right entry Delta. -/
def pairingBlock (ξ : ℝ) (Δ : ℂ) : PairMatrix :=
  (ξ : ℂ) • pauli3 + (Δ.re : ℂ) • pauli1 - (Δ.im : ℂ) • pauli2

theorem pairingBlock_entries (ξ : ℝ) (Δ : ℂ) :
    pairingBlock ξ Δ = !![(ξ : ℂ), Δ; star Δ, -(ξ : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [pairingBlock, pauli1, pauli2, pauli3] <;> ring

theorem pairingBlock_hermitian (ξ : ℝ) (Δ : ℂ) :
    (pairingBlock ξ Δ).conjTranspose = pairingBlock ξ Δ := by
  rw [pairingBlock_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]

/-- Spectral square is positive, unlike the indefinite bosonic/Krein generator convention. -/
theorem pairingBlock_sq (ξ : ℝ) (Δ : ℂ) :
    pairingBlock ξ Δ * pairingBlock ξ Δ =
      ((ξ ^ 2 + Complex.normSq Δ : ℝ) : ℂ) • (1 : PairMatrix) := by
  rw [pairingBlock_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_pow,
      Complex.ofReal_re, Complex.ofReal_im] <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ofReal_pow, pow_two] <;> ring

/-- Exact characteristic equation for this finite block. -/
theorem pairingBlock_characteristic (ξ : ℝ) (Δ E : ℂ) :
    Matrix.det (pairingBlock ξ Δ - E • (1 : PairMatrix)) =
      E ^ 2 - ((ξ ^ 2 + Complex.normSq Δ : ℝ) : ℂ) := by
  rw [pairingBlock_entries, Matrix.det_fin_two]
  apply Complex.ext <;>
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two] <;> ring

/-- Radicand of the stated short-junction Andreev level formula. -/
def junctionRadicand (transmission phase : ℝ) : ℝ :=
  1 - transmission * Real.sin (phase / 2) ^ 2

def junctionEnergy (gap transmission phase : ℝ) : ℝ :=
  gap * Real.sqrt (junctionRadicand transmission phase)

theorem junctionRadicand_nonneg (T φ : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    0 ≤ junctionRadicand T φ := by
  have htrig := Real.sin_sq_add_cos_sq (φ / 2)
  have hs : Real.sin (φ / 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (Real.cos (φ / 2))]
  dsimp [junctionRadicand]
  nlinarith [mul_nonneg hT0 (sub_nonneg.mpr hs)]

/-- The zero requires both perfect transmission and the half-phase cosine to vanish. -/
theorem junctionRadicand_zero_iff (T φ : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    junctionRadicand T φ = 0 ↔ T = 1 ∧ Real.cos (φ / 2) = 0 := by
  have htrig := Real.sin_sq_add_cos_sq (φ / 2)
  constructor
  · intro h
    have hcos := mul_nonneg hT0 (sq_nonneg (Real.cos (φ / 2)))
    have hscaled := congrArg (fun z : ℝ => T * z) htrig
    have hT : T = 1 := by
      dsimp [junctionRadicand] at h
      nlinarith
    refine ⟨hT, ?_⟩
    rw [hT] at h
    dsimp [junctionRadicand] at h
    nlinarith
  · rintro ⟨rfl, hc⟩
    dsimp [junctionRadicand]
    rw [hc] at htrig
    nlinarith

theorem junctionEnergy_sq (gap T φ : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    junctionEnergy gap T φ ^ 2 = gap ^ 2 * junctionRadicand T φ := by
  rw [junctionEnergy, mul_pow, Real.sq_sqrt (junctionRadicand_nonneg T φ hT0 hT1)]

theorem junctionEnergy_zero_iff (gap T φ : ℝ) (hg : gap ≠ 0)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    junctionEnergy gap T φ = 0 ↔ T = 1 ∧ Real.cos (φ / 2) = 0 := by
  rw [← junctionRadicand_zero_iff T φ hT0 hT1]
  constructor
  · intro h
    have hs := junctionEnergy_sq gap T φ hT0 hT1
    have hz : gap ^ 2 * junctionRadicand T φ = 0 := by simpa [h] using hs.symm
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hg)
  · intro h
    simp [junctionEnergy, h]

/-- A transmission perturbation opens the zero at phase pi in this scalar formula. -/
theorem junction_pi_gap_sq (gap T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    junctionEnergy gap T Real.pi ^ 2 = gap ^ 2 * (1 - T) := by
  rw [junctionEnergy_sq gap T Real.pi hT0 hT1]
  simp [junctionRadicand]

end InfoGeometry.Streaming.PairingGapSeparation
