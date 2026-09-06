import Mathlib

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
structure SpectrumCardPacket (n : Nat) where
  /-- Matrix whose spectrum is measured. -/
  A : Matrix (Fin n) (Fin n) ℂ
  /-- Finiteness of the spectral set. -/
  finite_spectrum : (matrixSpectrum A).Finite
  /-- Cardinality bound by matrix dimension. -/
  card_le : (matrixSpectrum A).ncard ≤ n

/-- Native constructor for the spectrum-cardinality packet. -/
def SpectrumCardPacket.ofMatrix (A : Matrix (Fin n) (Fin n) ℂ) : SpectrumCardPacket n where
  A := A
  finite_spectrum := matrixSpectrum_finite A
  card_le := matrixSpectrum_ncard_le A

namespace SpectrumCardPacket

theorem finite {n : Nat} (P : SpectrumCardPacket n) :
    (matrixSpectrum P.A).Finite :=
  P.finite_spectrum

theorem card_finite_spectrum {n : Nat} (P : SpectrumCardPacket n) :
    (matrixSpectrum P.A).Finite ∧ (matrixSpectrum P.A).ncard ≤ n :=
  ⟨P.finite_spectrum, P.card_le⟩

end SpectrumCardPacket

/-- Nonempty-spectrum packet corresponding to AFP `spectrum_non_empty`. -/
structure SpectrumNonemptyPacket (n : Nat) where
  /-- Matrix whose spectrum is nonempty. -/
  A : Matrix (Fin n) (Fin n) ℂ
  /-- Positive dimension. -/
  positive_dim : 0 < n
  /-- Nonempty spectrum witness. -/
  nonempty_spectrum : (matrixSpectrum A).Nonempty

/-- Native constructor for the nonempty-spectrum packet. -/
def SpectrumNonemptyPacket.ofMatrix {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) : SpectrumNonemptyPacket n := by
  refine { A := A, positive_dim := hn, nonempty_spectrum := matrixSpectrum_nonempty_of_pos hn A }

/-- Maximum-attainment packet for the spectral radius. -/
structure SpectralRadiusMaxPacket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) where
  /-- Eigenvalue attaining the spectral radius. -/
  eigenvalue : ℂ
  /-- The selected value is spectral. -/
  eigenvalue_mem : eigenvalue ∈ matrixSpectrum A
  /-- Its norm is the spectral radius. -/
  norm_eq_radius : ‖eigenvalue‖ = spectralRadius A
  /-- Spectral-radius upper bound on every spectral value. -/
  norm_le_radius : ∀ z ∈ matrixSpectrum A, ‖z‖ ≤ spectralRadius A

/-- Native constructor for the spectral-radius maximum packet. -/
def SpectralRadiusMaxPacket.ofNonempty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (h : (matrixSpectrum A).Nonempty) :
    SpectralRadiusMaxPacket A := by
  let S : Set ℝ := (fun z : ℂ => ‖z‖) '' matrixSpectrum A
  have hS : S.Finite := by
    simpa [S] using (matrixSpectrum_finite (A := A)).image (fun z : ℂ => ‖z‖)
  have hSn : S.Nonempty := by
    rcases h with ⟨z, hz⟩
    exact ⟨‖z‖, ⟨z, hz, rfl⟩⟩
  have hmem : ∃ z : ℂ, z ∈ matrixSpectrum A ∧ ‖z‖ = spectralRadius A := by
    simpa [S, spectralRadius] using (Set.Nonempty.csSup_mem hSn hS)
  let z : ℂ := Classical.choose hmem
  have hz : z ∈ matrixSpectrum A := (Classical.choose_spec hmem).1
  have hzR : ‖z‖ = spectralRadius A := (Classical.choose_spec hmem).2
  refine
    { eigenvalue := z
      eigenvalue_mem := hz
      norm_eq_radius := hzR
      norm_le_radius := ?_ }
  intro a ha
  exact le_csSup hS.bddAbove ⟨a, ha, rfl⟩

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
    {A : Matrix ι ι ℂ} (P : SpectralRadiusMaxPacket A)
    {a : ℝ} (ha : a ∈ (fun z : ℂ => ‖z‖) '' matrixSpectrum A) :
    a ≤ spectralRadius A := by
  rcases ha with ⟨z, hz, rfl⟩
  exact P.norm_le_radius z hz

end SpectralRadiusMaxPacket

/-- A simple norm-bound predicate for matrix powers. -/
def NormBound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (c : ℝ) : Prop :=
  ∀ i j : ι, ‖A i j‖ ≤ c

/--
Witness-gated polynomial growth statement for `spectralRadius A ≤ 1`, matching
AFP `spectral_radius_jnf_norm_bound_le_1`.
-/
structure PolynomialGrowthPacket (n : Nat) where
  /-- Matrix being bounded. -/
  A : Matrix (Fin n) (Fin n) ℂ
  /-- Spectral-radius assumption. -/
  radius_le_one : spectralRadius A ≤ 1
  /-- First growth constant. -/
  c1 : ℝ
  /-- Second growth constant. -/
  c2 : ℝ
  /-- Polynomial power bound. -/
  bound : ∀ k : Nat, NormBound (A ^ k) (c1 + c2 * (k : ℝ) ^ (n - 1))

/--
Witness-gated constant growth statement for `spectralRadius A < 1`, matching
AFP `spectral_radius_jnf_norm_bound_less_1`.
-/
structure ConstantGrowthPacket (n : Nat) where
  /-- Matrix being bounded. -/
  A : Matrix (Fin n) (Fin n) ℂ
  /-- Strict spectral-radius assumption. -/
  radius_lt_one : spectralRadius A < 1
  /-- Constant bound. -/
  c : ℝ
  /-- Constant power bound. -/
  bound : ∀ k : Nat, NormBound (A ^ k) c

theorem spectralRadius_jnf_norm_bound_le_one {n : Nat}
    (P : PolynomialGrowthPacket n) :
    ∃ c1 c2 : ℝ, ∀ k : Nat,
      NormBound (P.A ^ k) (c1 + c2 * (k : ℝ) ^ (n - 1)) :=
  ⟨P.c1, P.c2, P.bound⟩

theorem spectralRadius_jnf_norm_bound_less_one {n : Nat}
    (P : ConstantGrowthPacket n) :
    ∃ c : ℝ, ∀ k : Nat, NormBound (P.A ^ k) c :=
  ⟨P.c, P.bound⟩

/--
If an eigenvector has an eigenvalue of norm greater than one, powers grow along
that eigenvector by the corresponding exponential scalar.
-/
theorem spectralRadius_gt_one_witness {n : Nat}
    {A : Matrix (Fin n) (Fin n) ℂ} {v : Fin n → ℂ} {c : ℂ}
    (hv : Eigenvector A v c)
    (hc : 1 < ‖c‖) :
    v ≠ 0 ∧ 1 < ‖c‖ ∧
      ∀ k : Nat, (A ^ k).mulVec v = (c ^ k) • v := by
  exact ⟨hv.1, hc, fun k => eigenvector_pow hv k⟩

end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.SpectralRadius
