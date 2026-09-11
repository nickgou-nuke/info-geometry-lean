import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Matrix.Spectrum

/-!
# InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.SpectralRadius

Lean-native owner surface for AFP `Jordan_Normal_Form.Spectral_Radius`.

The AFP file uses the characteristic-polynomial/eigenvalue bridge and the
Jordan-normal-form existence theorem to turn spectral-radius assumptions into
growth bounds.  This module provides the spectral-radius API and keeps the JNF
growth conclusions witness-gated, so downstream code can consume the same
interfaces while the full AFP JNF growth machinery is ported incrementally.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.SpectralRadius

open scoped BigOperators
open Polynomial

/-- Local eigenvector predicate used by the spectral-radius growth witness. -/
def Eigenvector {K ι : Type*} [Semiring K] [Fintype ι]
    (A : Matrix ι ι K) (v : ι → K) (k : K) : Prop :=
  v ≠ 0 ∧ A.mulVec v = k • v

/-- Local characteristic-polynomial eigenvalue predicate. -/
def Eigenvalue {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (k : K) : Prop :=
  (Matrix.charpoly A).IsRoot k

/-- Characteristic polynomial abbreviation. -/
abbrev charPoly {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) : K[X] :=
  Matrix.charpoly A

/-- Eigenvectors are preserved by matrix powers. -/
theorem eigenvector_pow {K ι : Type*} [CommSemiring K] [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι K} {v : ι → K} {k : K}
    (hv : Eigenvector A v k) (i : Nat) :
    (A ^ i).mulVec v = (k ^ i) • v := by
  rcases hv with ⟨_, hAv⟩
  induction i with
  | zero =>
      simp
  | succ i ih =>
      calc
        (A ^ (i + 1)).mulVec v = A.mulVec ((A ^ i).mulVec v) := by
          rw [pow_succ']
          simp [Matrix.mulVec_mulVec]
        _ = A.mulVec ((k ^ i) • v) := by rw [ih]
        _ = (k ^ i) • (A.mulVec v) := by
          ext j
          simp [Matrix.mulVec]
        _ = (k ^ i) • (k • v) := by rw [hAv]
        _ = (k ^ (i + 1)) • v := by
          ext j
          simp [pow_succ, mul_assoc]

/-- AFP `spectrum A = Collect (eigenvalue A)`. -/
def matrixSpectrum {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) : Set K :=
  {k | Eigenvalue A k}

/-- Spectrum is exactly the root set of the characteristic polynomial. -/
theorem spectrum_root_charPoly {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) :
    matrixSpectrum A = {k | (charPoly A).eval k = 0} := by
  ext k
  simp [matrixSpectrum, Eigenvalue, Polynomial.IsRoot]

/-- Native finite-spectrum theorem for the matrix-spectrum root set. -/
theorem matrixSpectrum_finite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : (matrixSpectrum A).Finite := by
  have h : spectrum ℂ A = matrixSpectrum A := by
    ext k
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    rfl
  simpa [h] using (Matrix.finite_spectrum (A := A))

/-- Native nonempty-spectrum theorem for positive-dimensional complex matrices. -/
theorem matrixSpectrum_nonempty_of_pos {n : Nat}
    (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ) :
    (matrixSpectrum A).Nonempty := by
  have hdegNat : 0 < (Matrix.charpoly A).natDegree := by
    simpa [Matrix.charpoly_natDegree_eq_dim] using hn
  have hdeg : 0 < (Matrix.charpoly A).degree := by
    rw [Polynomial.degree_eq_natDegree (Matrix.charpoly_monic A).ne_zero]
    simpa using hdegNat
  have hdeg' : (Matrix.charpoly A).degree ≠ 0 := ne_of_gt hdeg
  rcases IsAlgClosed.exists_root (Matrix.charpoly A) hdeg' with ⟨x, hx⟩
  exact ⟨x, by simpa [matrixSpectrum, Polynomial.IsRoot] using hx⟩

/-- Native cardinality bound for the matrix spectrum. -/
theorem matrixSpectrum_ncard_le {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (matrixSpectrum A).ncard ≤ n := by
  have hs : matrixSpectrum A = (Matrix.charpoly A).rootSet ℂ := by
    ext k
    simpa [matrixSpectrum, Eigenvalue, Polynomial.IsRoot] using
      ((Matrix.charpoly_monic A).mem_rootSet (a := k)).symm
  rw [hs]
  simpa [Matrix.charpoly_natDegree_eq_dim] using
    (Polynomial.ncard_rootSet_le (p := Matrix.charpoly A) ℂ)

/-- Complex spectral radius: supremum of eigenvalue norms. -/
def spectralRadius {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ℝ :=
  sSup ((fun z : ℂ => ‖z‖) '' matrixSpectrum A)

/--
Finite-spectrum/cardinality packet corresponding to AFP
`card_finite_spectrum`.
-/
theorem SpectrumCardPacket.ofMatrix (A : Matrix (Fin n) (Fin n) ℂ) :
    (matrixSpectrum A).Finite ∧ (matrixSpectrum A).ncard ≤ n :=
  ⟨matrixSpectrum_finite A, matrixSpectrum_ncard_le A⟩

namespace SpectrumCardPacket

theorem finite {n : Nat} {A : Matrix (Fin n) (Fin n) ℂ}
    (P : (matrixSpectrum A).Finite ∧ (matrixSpectrum A).ncard ≤ n) :
    (matrixSpectrum A).Finite :=
  P.1

theorem card_finite_spectrum {n : Nat} {A : Matrix (Fin n) (Fin n) ℂ}
    (P : (matrixSpectrum A).Finite ∧ (matrixSpectrum A).ncard ≤ n) :
    (matrixSpectrum A).Finite ∧ (matrixSpectrum A).ncard ≤ n :=
  P

end SpectrumCardPacket

/-- Native constructor for the nonempty-spectrum packet. -/
theorem SpectrumNonemptyPacket.ofMatrix {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    0 < n ∧ (matrixSpectrum A).Nonempty :=
  ⟨hn, matrixSpectrum_nonempty_of_pos hn A⟩

/-- Native existence theorem for the spectral-radius maximum packet. -/
theorem exists_spectralRadiusMaxPacket_ofNonempty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (h : (matrixSpectrum A).Nonempty) :
    (∃ eigenvalue : ℂ,
      eigenvalue ∈ matrixSpectrum A ∧
        ‖eigenvalue‖ = spectralRadius A ∧
          ∀ z ∈ matrixSpectrum A, ‖z‖ ≤ spectralRadius A) := by
  let S : Set ℝ := (fun z : ℂ => ‖z‖) '' matrixSpectrum A
  have hS : S.Finite := by
    simpa [S] using (matrixSpectrum_finite (A := A)).image (fun z : ℂ => ‖z‖)
  have hSn : S.Nonempty := by
    rcases h with ⟨z, hz⟩
    exact ⟨‖z‖, ⟨z, hz, rfl⟩⟩
  have hmem : ∃ z : ℂ, z ∈ matrixSpectrum A ∧ ‖z‖ = spectralRadius A := by
    simpa [S, spectralRadius] using (Set.Nonempty.csSup_mem hSn hS)
  rcases hmem with ⟨z, hz, hzR⟩
  have hle : ∀ a ∈ matrixSpectrum A, ‖a‖ ≤ spectralRadius A := by
    intro a ha
    exact le_csSup hS.bddAbove ⟨a, ha, rfl⟩
  exact ⟨z, hz, hzR, hle⟩

namespace SpectralRadiusMaxPacket

theorem spectralRadius_mem_max {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (h : (matrixSpectrum A).Nonempty) :
    spectralRadius A ∈ (fun z : ℂ => ‖z‖) '' matrixSpectrum A := by
  let S : Set ℝ := (fun z : ℂ => ‖z‖) '' matrixSpectrum A
  have hS : S.Finite := by
    simpa [S] using (matrixSpectrum_finite (A := A)).image (fun z : ℂ => ‖z‖)
  have hSn : S.Nonempty := by
    rcases h with ⟨z, hz⟩
    exact ⟨‖z‖, ⟨z, hz, rfl⟩⟩
  simpa [spectralRadius, S] using (Set.Nonempty.csSup_mem hSn hS)

theorem le_spectralRadius {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ}
    (P : ∃ eigenvalue : ℂ,
      eigenvalue ∈ matrixSpectrum A ∧
        ‖eigenvalue‖ = spectralRadius A ∧
          ∀ z ∈ matrixSpectrum A, ‖z‖ ≤ spectralRadius A)
    {a : ℝ} (ha : a ∈ (fun z : ℂ => ‖z‖) '' matrixSpectrum A) :
    a ≤ spectralRadius A := by
  rcases P with ⟨_, _, _, hle⟩
  rcases ha with ⟨z, hz, rfl⟩
  exact hle z hz

end SpectralRadiusMaxPacket

/-- A simple norm-bound predicate for matrix powers. -/
def NormBound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (c : ℝ) : Prop :=
  ∀ i j : ι, ‖A i j‖ ≤ c

theorem spectralRadius_jnf_norm_bound_le_one {n : Nat}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (P : spectralRadius A ≤ 1 ∧
      ∃ c1 c2 : ℝ,
        ∀ k : Nat, NormBound (A ^ k) (c1 + c2 * (k : ℝ) ^ (n - 1))) :
    ∃ c1 c2 : ℝ, ∀ k : Nat,
      NormBound (A ^ k) (c1 + c2 * (k : ℝ) ^ (n - 1)) := by
  rcases P with ⟨_, c1, c2, hbound⟩
  exact ⟨c1, c2, hbound⟩

theorem spectralRadius_jnf_norm_bound_less_one {n : Nat}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (P : spectralRadius A < 1 ∧
      ∃ c : ℝ, ∀ k : Nat, NormBound (A ^ k) c) :
    ∃ c : ℝ, ∀ k : Nat, NormBound (A ^ k) c := by
  rcases P with ⟨_, c, hbound⟩
  exact ⟨c, hbound⟩

/-- Lemma 1: the eigenvector hypothesis contains nonzero vector data. -/
theorem eigenvector_nonzero_of_Eigenvector {n : Nat}
    {A : Matrix (Fin n) (Fin n) ℂ} {v : Fin n → ℂ} {c : ℂ}
    (hv : Eigenvector A v c) :
    v ≠ 0 := by
  exact hv.1

/-- Lemma 2: the spectral-growth condition is the strict norm inequality. -/
theorem eigenvalue_norm_gt_one_readout {c : ℂ}
    (hc : 1 < ‖c‖) :
    1 < ‖c‖ := by
  exact hc

/-- Lemma 3: an eigenvector remains an eigenvector for every matrix power. -/
theorem eigenvector_power_action {n : Nat}
    {A : Matrix (Fin n) (Fin n) ℂ} {v : Fin n → ℂ} {c : ℂ}
    (hv : Eigenvector A v c) :
    ∀ k : Nat, (A ^ k).mulVec v = (c ^ k) • v := by
  intro k
  exact eigenvector_pow hv k

/--
If an eigenvector has an eigenvalue of norm greater than one, powers grow along
that eigenvector by the corresponding exponential scalar.
-/
theorem eigenvalue_gt_one_power_growth {n : Nat}
    {A : Matrix (Fin n) (Fin n) ℂ} {v : Fin n → ℂ} {c : ℂ}
    (hv : Eigenvector A v c)
    (hc : 1 < ‖c‖) :
    v ≠ 0 ∧ 1 < ‖c‖ ∧
      ∀ k : Nat, (A ^ k).mulVec v = (c ^ k) • v := by
  exact ⟨eigenvector_nonzero_of_Eigenvector hv,
    eigenvalue_norm_gt_one_readout hc,
    eigenvector_power_action hv⟩

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.SpectralRadius
