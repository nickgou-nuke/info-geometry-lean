import Mathlib.Tactic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
import InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge
import InfoGeometry.Geometry.RealRotorCore
import InfoGeometry.Geometry.FiniteMatrixResolventKernel
import InfoGeometry.Compatibility.MathlibUpperHalfPlaneShadow

/-!
# InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator

Finite Berry--Keating / `H = xp` surface attached to the prime Cantor--Dirac
operator.

This module does **not** construct the Hilbert--Polya operator and does **not**
claim RH.  It implements the finite algebraic layer suggested by the
Berry--Keating analogy:

* the continuous generator `H_BK = (XP + PX)/2` is represented on the finite
  square-free prime-Cantor carrier by the diagonal logarithmic dilation energy
  `E(S) = Σ_{p ∈ S} logPrime p`;
* critical-line Berry--Keating evolution has phase `exp(- i t E(S))`, and the
  single-prime holonomies are `exp(- i t logPrime p)`;
* the existing zeta-Cantor Dirac operator supplies `D_C^ζ(s) = Q(s) + Q♯(s)`.

The analytic specialization `holonomy s p = p^(1/2 - s)`, the passage to the
infinite prime set, analytic continuation, and spectral claims are intentionally
kept in deferred-interface records.
-/

noncomputable section

open scoped BigOperators
open Classical

namespace InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator

open InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
open InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator.FiniteCantorZetaDirac
open InfoGeometry.Geometry.FiniteMatrixResolventKernel

/-- Prime mode inside a finite cutoff. -/
abbrev PrimeMode (P : PrimeCantorZetaDiracOperator.PrimeCutoff) := PrimeCantorZetaDiracOperator.PrimeMode P

/-- Vertex of the finite prime Cantor/Fock lattice. -/
abbrev Vertex (P : PrimeCantorZetaDiracOperator.PrimeCutoff) := PrimeCantorZetaDiracOperator.Vertex P

/-- Complex-valued fields on the finite prime Cantor/Fock lattice. -/
abbrev CantorField (P : PrimeCantorZetaDiracOperator.PrimeCutoff) := PrimeCantorZetaDiracOperator.CantorField P

/-! ## 1. Finite Berry--Keating logarithmic dilation energy -/

/--
Finite logarithmic dilation energy of a square-free occupation state.

If `S` corresponds to the square-free integer `n = ∏_{p ∈ S} p`, then this is
formally `log n`.
-/
def bkEnergy {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (S : Vertex P) : ℝ :=
  Finset.sum S (fun p => logPrime p)

/-!
The Berry--Keating diagonal readout is the same finite observable as the
weighted Hodge-square readout in the prime exterior graph owner.  This is a
readout square only: it does not identify the finite carrier with a continuous
`xp` operator or add a spectral claim.
-/
theorem bkEnergy_eq_weightedHodgeSquareEnergy {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (S : Vertex P) :
    bkEnergy logPrime S =
      InfoGeometry.Arithmetic.PrimeExteriorGraphDirac.weightedHodgeSquareEnergy
        P logPrime S := by
  change
    InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.squareFreeEnergy
        logPrime S =
      InfoGeometry.Arithmetic.PrimeExteriorGraphDirac.weightedHodgeSquareEnergy
        P logPrime S
  exact
    (InfoGeometry.Arithmetic.PrimeExteriorGraphDirac.weightedHodgeSquareEnergy_eq_weightedNumberEnergy
      P logPrime S).symm

/-!
At the arithmetic specialization, the same square-free observable is the
exterior graph's canonical logarithmic prime-energy readout.
-/
theorem bkEnergy_primeEnergy_eq_stateEnergy {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (S : Vertex P) :
    bkEnergy (fun p : PrimeMode P => Real.log (p : ℝ)) S =
      InfoGeometry.Arithmetic.PrimeExteriorGraphDirac.stateEnergy S := by
  unfold bkEnergy InfoGeometry.Arithmetic.PrimeExteriorGraphDirac.stateEnergy
  rfl

/-- The finite Berry--Keating prime-log readout is the logarithm of the
    represented square-free integer. -/
theorem bkEnergy_primeEnergy_eq_log_stateNat {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (S : Vertex P) :
    bkEnergy (fun p : PrimeMode P => Real.log (p : ℝ)) S =
      Real.log (InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge.stateNat S : ℝ) := by
  rw [bkEnergy_primeEnergy_eq_stateEnergy]
  exact
    (InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge.stateNat_log_eq_squareFreeEnergy S).symm

/--
Finite Berry--Keating Hamiltonian on the prime-Cantor carrier.

This is the diagonal logarithmic dilation generator.  It is the finite algebraic
shadow of `H_BK = (XP + PX)/2`; no continuous-domain self-adjoint extension is
asserted here.
-/
def bkHamiltonian {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) :
    CantorField P → CantorField P :=
  fun f S => (bkEnergy logPrime S : ℂ) * f S

/-! The finite diagonal logarithmic Hamiltonian is self-adjoint for the
native finite Cantor pairing because its eigenvalues are real. -/
theorem bkHamiltonian_isSelfAdjoint {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) :
    IsAdjointPair (P := P) (bkHamiltonian logPrime) (bkHamiltonian logPrime) := by
  intro f g
  unfold pairing bkHamiltonian
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro S hS
  ring

theorem bkHamiltonian_basisDelta_eigenvector {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (T : Vertex P) :
    bkHamiltonian logPrime (basisDelta T) =
      (bkEnergy logPrime T : ℂ) • basisDelta T := by
  funext S
  by_cases hST : S = T
  · subst hST
    simp [bkHamiltonian, basisDelta]
  · simp [bkHamiltonian, basisDelta, hST]

/-! ### Finite Jost/determinant realization -/

/-- The diagonal matrix readout of the finite Berry--Keating Hamiltonian. -/
def bkHamiltonianMatrix {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) : Matrix (Vertex P) (Vertex P) ℂ :=
  Matrix.diagonal (fun S => (bkEnergy logPrime S : ℂ))

/-- The finite Jost determinant `det(z I - H_BK)`. -/
def bkJostDet {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (z : ℂ) : ℂ :=
  (z • (1 : Matrix (Vertex P) (Vertex P) ℂ) -
      bkHamiltonianMatrix logPrime).det

theorem bkHamiltonianMatrix_mulVec_eq_bkHamiltonian {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (f : CantorField P) :
    Matrix.mulVec (bkHamiltonianMatrix logPrime) f = bkHamiltonian logPrime f := by
  funext S
  simp [bkHamiltonianMatrix, bkHamiltonian, Matrix.mulVec]

theorem bkHamiltonianMatrix_isHermitian {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) :
    (bkHamiltonianMatrix logPrime).IsHermitian := by
  unfold Matrix.IsHermitian bkHamiltonianMatrix
  ext S T
  by_cases hST : S = T
  · subst hST
    simp
  · simp [hST, Ne.symm hST]

theorem bkJostDet_eq_prod {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (z : ℂ) :
    bkJostDet logPrime z =
      ∏ S : Vertex P, (z - (bkEnergy logPrime S : ℂ)) := by
  unfold bkJostDet bkHamiltonianMatrix
  rw [show z • (1 : Matrix (Vertex P) (Vertex P) ℂ) -
      Matrix.diagonal (fun S => (bkEnergy logPrime S : ℂ)) =
      Matrix.diagonal (fun S => z - (bkEnergy logPrime S : ℂ)) by
    ext S T
    by_cases hST : S = T
    · subst hST
      simp
    · simp [hST]]
  exact Matrix.det_diagonal

theorem hasDerivAt_bkJostDet {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (z : ℂ) :
    HasDerivAt (bkJostDet logPrime)
      (∑ S : Vertex P,
        ∏ T ∈ Finset.univ.erase S, (z - (bkEnergy logPrime T : ℂ))) z := by
  have hprod :
      HasDerivAt
        (fun w : ℂ => ∏ S : Vertex P, (w - (bkEnergy logPrime S : ℂ)))
        (∑ S : Vertex P,
          (∏ T ∈ Finset.univ.erase S,
            (z - (bkEnergy logPrime T : ℂ))) * 1) z := by
    apply HasDerivAt.fun_finset_prod
    intro S hS
    simpa using
      (hasDerivAt_id z).sub_const (bkEnergy logPrime S : ℂ)
  have hfun : bkJostDet logPrime =
      (fun w : ℂ => ∏ S : Vertex P, (w - (bkEnergy logPrime S : ℂ))) := by
    funext w
    exact bkJostDet_eq_prod logPrime w
  rw [hfun]
  simpa [mul_one] using hprod

/-! The finite Jost logarithmic derivative is the sum of the resolvent poles.

This is a purely finite algebraic identity: the nonvanishing hypothesis keeps
the logarithmic derivative away from the finitely many eigenvalues. -/
theorem bkJostDet_logDeriv_eq_sum_inv_of_ne_zero {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (z : ℂ)
    (hz : bkJostDet logPrime z ≠ 0) :
    logDeriv (bkJostDet logPrime) z =
      ∑ S : Vertex P, (z - (bkEnergy logPrime S : ℂ))⁻¹ := by
  rw [show bkJostDet logPrime =
      (fun w : ℂ => ∏ S : Vertex P, (w - (bkEnergy logPrime S : ℂ))) by
    funext w
    exact bkJostDet_eq_prod logPrime w]
  rw [logDeriv_prod]
  · simp only [logDeriv]
    congr 1
    funext S
    simp [sub_eq_add_neg]
  · intro S hS hzero
    apply hz
    rw [bkJostDet_eq_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ S) hzero
  · intro S hS
    simpa using
      (hasDerivAt_id z).sub_const (bkEnergy logPrime S : ℂ)

theorem bkJostDet_eq_zero_iff {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (z : ℂ) :
    bkJostDet logPrime z = 0 ↔
      ∃ S : Vertex P, z = (bkEnergy logPrime S : ℂ) := by
  rw [bkJostDet_eq_prod]
  simp only [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨S, -, hS⟩
    exact ⟨S, sub_eq_zero.mp hS⟩
  · rintro ⟨S, hS⟩
    exact ⟨S, Finset.mem_univ S, sub_eq_zero.mpr hS⟩

theorem bkJostDet_zero_im_eq_zero {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (z : ℂ)
    (hz : bkJostDet logPrime z = 0) :
    z.im = 0 := by
  rcases (bkJostDet_eq_zero_iff logPrime z).mp hz with ⟨S, rfl⟩
  simp

theorem bkJostDet_zero_is_real {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (z : ℂ)
    (hz : bkJostDet logPrime z = 0) :
    ∃ r : ℝ, z = r := by
  refine ⟨z.re, ?_⟩
  apply Complex.ext
  · rfl
  · exact bkJostDet_zero_im_eq_zero logPrime z hz

theorem bkEnergy_nonneg_of_nonneg {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ)
    (hlog : ∀ p, 0 ≤ logPrime p) (S : Vertex P) :
    0 ≤ bkEnergy logPrime S := by
  exact Finset.sum_nonneg (fun p hp => hlog p)

theorem bkJostDet_zero_nonneg {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ)
    (hlog : ∀ p, 0 ≤ logPrime p) (z : ℂ)
    (hz : bkJostDet logPrime z = 0) :
    0 ≤ z.re := by
  rcases (bkJostDet_eq_zero_iff logPrime z).mp hz with ⟨S, rfl⟩
  exact_mod_cast bkEnergy_nonneg_of_nonneg logPrime hlog S

theorem bkJostDet_zero_of_basisDelta_eigenvalue {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (S : Vertex P) :
    bkJostDet logPrime (bkEnergy logPrime S : ℂ) = 0 := by
  exact (bkJostDet_eq_zero_iff logPrime _).mpr ⟨S, rfl⟩

theorem bkJostDet_eq_zero_iff_eigenstate {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (z : ℂ) :
    bkJostDet logPrime z = 0 ↔
      ∃ f : CantorField P, f ≠ 0 ∧
        bkHamiltonian logPrime f = z • f := by
  rw [bkJostDet_eq_zero_iff]
  constructor
  · rintro ⟨S, rfl⟩
    refine ⟨basisDelta S, ?_, bkHamiltonian_basisDelta_eigenvector logPrime S⟩
    intro hzero
    have hvalue := congrFun hzero S
    simp [basisDelta] at hvalue
  · rintro ⟨f, hf, hEigen⟩
    classical
    by_contra hNoEnergy
    push_neg at hNoEnergy
    have hzero : f = 0 := by
      funext S
      have hpoint := congrFun hEigen S
      change (bkEnergy logPrime S : ℂ) * f S = z * f S at hpoint
      have hscalar : z - (bkEnergy logPrime S : ℂ) ≠ 0 := by
        intro hscalar
        apply hNoEnergy S
        exact sub_eq_zero.mp hscalar
      have hpoint' : (bkEnergy logPrime S : ℂ) * f S = z * f S := by
        simpa [smul_eq_mul] using hpoint
      have hmul :
          ((bkEnergy logPrime S : ℂ) - z) * f S = 0 := by
        calc
          ((bkEnergy logPrime S : ℂ) - z) * f S =
              (bkEnergy logPrime S : ℂ) * f S - z * f S := by ring
          _ = 0 := by rw [hpoint']; ring
      have hscalar' : (bkEnergy logPrime S : ℂ) - z ≠ 0 := by
        intro hscalar'
        apply hscalar
        calc
          z - (bkEnergy logPrime S : ℂ) =
              -((bkEnergy logPrime S : ℂ) - z) := by ring
          _ = 0 := by rw [hscalar']; simp
      exact (mul_eq_zero.mp hmul).resolve_left hscalar'
    exact hf hzero

theorem bkResolventKernel_exists_of_jost_ne_zero {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (z : ℂ)
    (hz : bkJostDet logPrime z ≠ 0) :
    ∃ K : MatrixResolventKernel (Vertex P),
      K.A = bkHamiltonianMatrix logPrime ∧ K.z = z := by
  let A := bkHamiltonianMatrix logPrime
  let R := resolventDiff z A
  have hdet : R.det ≠ 0 := by
    simpa [R, A, bkJostDet] using hz
  have hunitdet : IsUnit R.det := isUnit_iff_ne_zero.mpr hdet
  have hunit : IsUnit R := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact hunitdet
  let K : MatrixResolventKernel (Vertex P) :=
    { A := A
      z := z
      kernel := R⁻¹
      diff_mul_kernel := Matrix.mul_nonsing_inv R hunitdet
      kernel_mul_diff := Matrix.nonsing_inv_mul R hunitdet }
  exact ⟨K, rfl, rfl⟩

theorem bkResolventKernel_exists_iff_jost_ne_zero {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (z : ℂ) :
    (∃ K : MatrixResolventKernel (Vertex P),
      K.A = bkHamiltonianMatrix logPrime ∧ K.z = z) ↔
        bkJostDet logPrime z ≠ 0 := by
  constructor
  · rintro ⟨K, hA, hz⟩
    have hright :
        resolventDiff z (bkHamiltonianMatrix logPrime) * K.kernel = 1 := by
      simpa [hA, hz] using K.diff_mul_kernel
    have hunit : IsUnit
        (resolventDiff z (bkHamiltonianMatrix logPrime)).det :=
      Matrix.isUnit_det_of_right_inverse hright
    exact hunit.ne_zero
  · exact bkResolventKernel_exists_of_jost_ne_zero logPrime z

/-! The same logarithmic derivative is the finite trace of the resolvent.

The proof uses only the diagonal resolvent equation, so this is a genuine
finite matrix identity rather than a formal appeal to an infinite trace. -/
theorem bkJostDet_logDeriv_eq_trace_resolvent
    {P : PrimeCantorZetaDiracOperator.PrimeCutoff} (logPrime : PrimeMode P → ℝ) (z : ℂ)
    (K : MatrixResolventKernel (Vertex P))
    (hA : K.A = bkHamiltonianMatrix logPrime) (hz : K.z = z) :
    logDeriv (bkJostDet logPrime) z = Matrix.trace K.kernel := by
  have hJ : bkJostDet logPrime z ≠ 0 := by
    have hright := congrArg Matrix.det K.diff_mul_kernel
    have hdetR :
        (resolventDiff z (bkHamiltonianMatrix logPrime)).det ≠ 0 := by
      intro hzero
      have hzero' :
          (z • (1 : Matrix (Vertex P) (Vertex P) ℂ) -
            bkHamiltonianMatrix logPrime).det = 0 := by
        change (z • (1 : Matrix (Vertex P) (Vertex P) ℂ) -
          bkHamiltonianMatrix logPrime).det = 0 at hzero
        exact hzero
      have hright' := hright
      rw [hz, hA] at hright'
      change ((z • (1 : Matrix (Vertex P) (Vertex P) ℂ) -
        bkHamiltonianMatrix logPrime) * K.kernel).det = Matrix.det 1 at hright'
      rw [Matrix.det_mul, hzero', zero_mul] at hright'
      have hbad : (1 : ℂ) = 0 := by simpa using hright'.symm
      exact one_ne_zero hbad
    simpa [bkJostDet, resolventDiff] using hdetR
  rw [bkJostDet_logDeriv_eq_sum_inv_of_ne_zero logPrime z hJ]
  change (∑ S : Vertex P, (z - (bkEnergy logPrime S : ℂ))⁻¹) =
    ∑ S : Vertex P, K.kernel S S
  apply Finset.sum_congr rfl
  intro S hS
  have hdiag := congrFun (congrFun K.diff_mul_kernel S) S
  have hfactor : z - (bkEnergy logPrime S : ℂ) ≠ 0 := by
    intro hzero
    apply hJ
    rw [bkJostDet_eq_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ S) hzero
  have hsum :
      (∑ x : Vertex P,
        (z * (1 : Matrix (Vertex P) (Vertex P) ℂ) S x -
          Matrix.diagonal (fun T => (bkEnergy logPrime T : ℂ)) S x) *
        K.kernel x S) =
        (z - (bkEnergy logPrime S : ℂ)) * K.kernel S S := by
    change ((Finset.univ : Finset (Vertex P)).sum (fun x =>
        (z * (1 : Matrix (Vertex P) (Vertex P) ℂ) S x -
          Matrix.diagonal (fun T => (bkEnergy logPrime T : ℂ)) S x) *
          K.kernel x S)) =
      (z - (bkEnergy logPrime S : ℂ)) * K.kernel S S
    rw [Finset.sum_eq_single S]
    · simp
    · intro b hb hbs
      simp [Ne.symm hbs]
    · simp
  have hdiag' :
      (z - (bkEnergy logPrime S : ℂ)) * K.kernel S S = 1 := by
    have hdiag0 :
        (∑ x : Vertex P,
          (z * (1 : Matrix (Vertex P) (Vertex P) ℂ) S x -
            Matrix.diagonal (fun T => (bkEnergy logPrime T : ℂ)) S x) *
            K.kernel x S) = 1 := by
      simpa [hz, hA, resolventDiff, Matrix.mul_apply, bkHamiltonianMatrix,
        Matrix.smul_apply, smul_eq_mul] using hdiag
    rw [hsum] at hdiag0
    exact hdiag0
  calc
    (z - (bkEnergy logPrime S : ℂ))⁻¹ =
        (z - (bkEnergy logPrime S : ℂ))⁻¹ * 1 := by simp
    _ = (z - (bkEnergy logPrime S : ℂ))⁻¹ *
        ((z - (bkEnergy logPrime S : ℂ)) * K.kernel S S) := by
          rw [hdiag']
    _ = K.kernel S S := by field_simp [hfactor]

theorem finite_resolvent_identity
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (z w : ℂ)
    (Rz Rw : Matrix n n ℂ)
    (_hz_left : resolventDiff z A * Rz = 1)
    (hz_right : Rz * resolventDiff z A = 1)
    (hw_left : resolventDiff w A * Rw = 1)
    (_hw_right : Rw * resolventDiff w A = 1) :
    Rz - Rw = (w - z) • (Rz * Rw) := by
  have hdiff :
      resolventDiff w A - resolventDiff z A =
        (w - z) • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [resolventDiff]
    · simp [resolventDiff, hij]
  have hfirst : Rz * resolventDiff w A * Rw = Rz := by
    calc
      Rz * resolventDiff w A * Rw =
          Rz * (resolventDiff w A * Rw) := by rw [mul_assoc]
      _ = Rz * 1 := by rw [hw_left]
      _ = Rz := by simp
  have hsecond : Rz * resolventDiff z A * Rw = Rw := by
    calc
      Rz * resolventDiff z A * Rw =
          (Rz * resolventDiff z A) * Rw := rfl
      _ = 1 * Rw := by rw [hz_right]
      _ = Rw := by simp
  calc
    Rz - Rw = Rz * resolventDiff w A * Rw -
        Rz * resolventDiff z A * Rw := by rw [hfirst, hsecond]
    _ = Rz * (resolventDiff w A - resolventDiff z A) * Rw := by
      noncomm_ring
    _ = Rz * ((w - z) • (1 : Matrix n n ℂ)) * Rw := by rw [hdiff]
    _ = (w - z) • (Rz * Rw) := by
      simp

/-! ## 2. Critical-line Berry--Keating phases -/

/-- Single-prime Berry--Keating critical-line phase `exp(- i t log p)`. -/
def bkPrimePhase {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) (p : PrimeMode P) : ℂ :=
  Complex.exp (-(Complex.I * (t : ℂ) * (logPrime p : ℂ)))

/-- Square-free Berry--Keating critical-line phase `exp(- i t E(S))`. -/
def bkStatePhase {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) (S : Vertex P) : ℂ :=
  Complex.exp (-(Complex.I * (t : ℂ) * (bkEnergy logPrime S : ℂ)))

/-! The prime phase is the multiplicative one-mode factor of the square-free
state phase.  This is the finite phase-lift law used by the cutoff bridge. -/

theorem bkStatePhase_insert_of_not_mem {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ)
    (p : PrimeMode P) (S : Vertex P) (hp : p ∉ S) :
    bkStatePhase logPrime t (insert p S) =
      bkPrimePhase logPrime t p * bkStatePhase logPrime t S := by
  unfold bkStatePhase bkPrimePhase
  rw [show bkEnergy logPrime (insert p S) =
      logPrime p + bkEnergy logPrime S by simp [bkEnergy, hp]]
  rw [show -(Complex.I * (t : ℂ) *
      ((logPrime p + bkEnergy logPrime S : ℝ) : ℂ)) =
      (-(Complex.I * (t : ℂ) * (logPrime p : ℂ))) +
        (-(Complex.I * (t : ℂ) * (bkEnergy logPrime S : ℂ))) by
    push_cast
    ring]
  rw [Complex.exp_add]

theorem hasDerivAt_bkStatePhase {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) (S : Vertex P) :
    HasDerivAt (fun u : ℝ => bkStatePhase logPrime u S)
      (-(Complex.I * (bkEnergy logPrime S : ℂ)) *
        bkStatePhase logPrime t S) t := by
  let C : ℂ := -(Complex.I * (bkEnergy logPrime S : ℂ))
  have hlin : HasDerivAt (fun u : ℝ => C * (u : ℂ)) C t := by
    simpa using
      (ContinuousLinearMap.hasDerivAt Complex.ofRealCLM (x := t)).const_mul C
  have hexp : HasDerivAt
      (fun u : ℝ => Complex.exp (C * (u : ℂ)))
      (Complex.exp (C * (t : ℂ)) * C) t := by
    simpa using (Complex.hasDerivAt_exp (C * (t : ℂ))).comp t hlin
  simpa [bkStatePhase, C, mul_assoc, mul_left_comm, mul_comm] using hexp

/-! The same finite phase in the native real rotor carrier. -/

def bkStateRotor {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) (S : Vertex P) :
    InfoGeometry.Geometry.RealChiralPhase :=
  (Real.cos (t * bkEnergy logPrime S),
    -Real.sin (t * bkEnergy logPrime S))

theorem bkStateRotor_normSq {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) (S : Vertex P) :
    InfoGeometry.Geometry.RealChiralPhase.normSq
      (bkStateRotor logPrime t S) = 1 := by
  change Real.cos (t * bkEnergy logPrime S) ^ 2 +
      (-Real.sin (t * bkEnergy logPrime S)) ^ 2 = 1
  nlinarith [Real.sin_sq_add_cos_sq (t * bkEnergy logPrime S)]

theorem bkStateRotor_add {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (s t : ℝ) (S : Vertex P) :
    bkStateRotor logPrime (s + t) S =
      bkStateRotor logPrime s S * bkStateRotor logPrime t S := by
  let e := bkEnergy logPrime S
  apply Prod.ext
  · change Real.cos ((s + t) * e) =
      Real.cos (s * e) * Real.cos (t * e) -
        (-Real.sin (s * e)) * (-Real.sin (t * e))
    rw [show (s + t) * e = s * e + t * e by ring, Real.cos_add]
    ring
  · change -Real.sin ((s + t) * e) =
      Real.cos (s * e) * (-Real.sin (t * e)) +
        (-Real.sin (s * e)) * Real.cos (t * e)
    rw [show (s + t) * e = s * e + t * e by ring, Real.sin_add]
    ring

@[simp] theorem bkStateRotor_zero {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (S : Vertex P) :
    bkStateRotor logPrime 0 S = 1 := by
  ext <;> simp [bkStateRotor]

theorem bkStateRotor_mul_neg {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) (S : Vertex P) :
    bkStateRotor logPrime t S * bkStateRotor logPrime (-t) S = 1 := by
  rw [← bkStateRotor_add logPrime t (-t) S, add_neg_cancel,
    bkStateRotor_zero]

theorem bkStateRotor_complexification {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) (S : Vertex P) :
    InfoGeometry.Compatibility.chiralToComplex
        (InfoGeometry.Compatibility.realChiralPhaseEquiv
          (bkStateRotor logPrime t S)) =
      bkStatePhase logPrime t S := by
  rw [InfoGeometry.Compatibility.chiralToComplex_eq_scalar_add_bivector_I]
  simp only [InfoGeometry.Compatibility.realChiralPhaseEquiv_scalar,
    InfoGeometry.Compatibility.realChiralPhaseEquiv_bivector]
  unfold bkStateRotor bkStatePhase
  change (Real.cos (t * bkEnergy logPrime S) : ℂ) +
      ((-Real.sin (t * bkEnergy logPrime S) : ℝ) : ℂ) * Complex.I =
    Complex.exp (-(Complex.I * (t : ℂ) *
      (bkEnergy logPrime S : ℂ)))
  have harg :
      -(Complex.I * (t : ℂ) * (bkEnergy logPrime S : ℂ)) =
        ((-(t * bkEnergy logPrime S) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp

/-- The finite Berry--Keating rotor carries a constant Madelung current.

The second argument is its parameter derivative in real chiral coordinates.
This is an exact finite statement; it does not assert a continuum-domain
self-adjoint realization. -/
theorem bkStateRotor_phaseCurrent
    {P : PrimeCantorZetaDiracOperator.PrimeCutoff} (hbar mass : ℝ)
    (logPrime : PrimeMode P → ℝ) (t : ℝ) (S : Vertex P) :
    InfoGeometry.Geometry.RealChiralPhase.phaseCurrent hbar mass
        (bkStateRotor logPrime t S)
        (-bkEnergy logPrime S * Real.sin (t * bkEnergy logPrime S),
          -bkEnergy logPrime S * Real.cos (t * bkEnergy logPrime S)) =
      -(hbar / mass) * bkEnergy logPrime S := by
  unfold InfoGeometry.Geometry.RealChiralPhase.phaseCurrent
    InfoGeometry.Geometry.RealChiralPhase.phaseNumerator bkStateRotor
  let e := bkEnergy logPrime S
  let θ := t * e
  change (hbar / mass) *
      (Real.cos θ * (-e * Real.cos θ) -
        (-Real.sin θ) * (-e * Real.sin θ)) =
      -(hbar / mass) * e
  rw [show Real.cos θ * (-e * Real.cos θ) -
      (-Real.sin θ) * (-e * Real.sin θ) =
        -e * (Real.cos θ ^ 2 + Real.sin θ ^ 2) by ring]
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [htrig]
  ring

/-- Diagonal critical-line Berry--Keating evolution on the finite carrier. -/
def bkEvolution {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) :
    CantorField P → CantorField P :=
  fun f S => bkStatePhase logPrime t S * f S

theorem hasDerivAt_bkEvolution_apply {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ)
    (f : CantorField P) (S : Vertex P) :
    HasDerivAt (fun u : ℝ => bkEvolution logPrime u f S)
      (-(Complex.I * (bkEnergy logPrime S : ℂ)) *
        bkEvolution logPrime t f S) t := by
  simpa [bkEvolution, mul_assoc, mul_left_comm, mul_comm] using
    (hasDerivAt_bkStatePhase logPrime t S).mul_const (f S)

theorem hasDerivAt_bkEvolution_apply_eq_matrixHamiltonian
    {P : PrimeCantorZetaDiracOperator.PrimeCutoff} (logPrime : PrimeMode P → ℝ) (t : ℝ)
    (f : CantorField P) (S : Vertex P) :
    HasDerivAt (fun u : ℝ => bkEvolution logPrime u f S)
      (-Complex.I *
        (Matrix.mulVec (bkHamiltonianMatrix logPrime)
          (bkEvolution logPrime t f)) S) t := by
  have hH := congrFun
    (bkHamiltonianMatrix_mulVec_eq_bkHamiltonian logPrime
      (bkEvolution logPrime t f)) S
  rw [hH]
  simpa [bkHamiltonian, mul_assoc, mul_left_comm, mul_comm] using
    hasDerivAt_bkEvolution_apply logPrime t f S

/-- The critical-line holonomy vector induced by the finite BK dilation phases. -/
def bkCriticalHolonomy {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) : PrimeMode P → ℂ :=
  fun p => bkPrimePhase logPrime t p

theorem bkStatePhase_star_mul_self {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) (S : Vertex P) :
    star (bkStatePhase logPrime t S) * bkStatePhase logPrime t S = 1 := by
  simp only [Complex.star_def]
  rw [← Complex.normSq_eq_conj_mul_self]
  have hn : ‖bkStatePhase logPrime t S‖ = 1 := by
    simp [bkStatePhase, Complex.norm_exp]
  have hnormSq : Complex.normSq (bkStatePhase logPrime t S) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hn]
    norm_num
  exact_mod_cast hnormSq

theorem bkEvolution_pairing_preserved {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ)
    (f g : CantorField P) :
    pairing (bkEvolution logPrime t f) (bkEvolution logPrime t g) =
      pairing f g := by
  unfold pairing bkEvolution
  apply Finset.sum_congr rfl
  intro S hS
  calc
    star (bkStatePhase logPrime t S * f S) *
        (bkStatePhase logPrime t S * g S) =
        star (f S) *
          (star (bkStatePhase logPrime t S) *
            bkStatePhase logPrime t S) * g S := by
              simp only [star_mul]
              ring
    _ = star (f S) * g S := by
      rw [bkStatePhase_star_mul_self]
      simp

theorem bkStatePhase_add {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (s t : ℝ) (S : Vertex P) :
    bkStatePhase logPrime (s + t) S =
      bkStatePhase logPrime s S * bkStatePhase logPrime t S := by
  unfold bkStatePhase
  rw [show -(Complex.I * ((s + t : ℝ) : ℂ) *
      (bkEnergy logPrime S : ℂ)) =
      (-(Complex.I * (s : ℂ) * (bkEnergy logPrime S : ℂ))) +
        (-(Complex.I * (t : ℂ) * (bkEnergy logPrime S : ℂ))) by
    push_cast
    ring]
  rw [Complex.exp_add]

@[simp]
theorem bkEvolution_zero {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (f : CantorField P) :
    bkEvolution logPrime 0 f = f := by
  funext S
  simp [bkEvolution, bkStatePhase]

theorem bkEvolution_add {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (s t : ℝ) (f : CantorField P) :
    bkEvolution logPrime (s + t) f =
      bkEvolution logPrime s (bkEvolution logPrime t f) := by
  funext S
  simp only [bkEvolution, bkStatePhase_add]
  ring

theorem bkEvolution_neg_left {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) (f : CantorField P) :
    bkEvolution logPrime (-t) (bkEvolution logPrime t f) = f := by
  rw [← bkEvolution_add, neg_add_cancel, bkEvolution_zero]

theorem bkEvolution_neg_right {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (t : ℝ) (f : CantorField P) :
    bkEvolution logPrime t (bkEvolution logPrime (-t) f) = f := by
  rw [← bkEvolution_add, add_neg_cancel, bkEvolution_zero]

/-! ## 3. Bundled finite Berry--Keating/Cantor--Dirac packet -/

/--
A finite Berry--Keating/Cantor--Dirac packet.

`amplitude` and `holonomy` are the data used by the existing Cantor--Dirac
operator.  `logPrime` records the finite logarithmic periods.  The field
`critical_holonomy` asserts that on the critical-line parameter supplied by the
owner, the holonomy restricts to the BK phase `exp(-i t log p)`.
-/
structure FiniteBerryKeatingCantorDirac (P : PrimeCantorZetaDiracOperator.PrimeCutoff) where
  amplitude : PrimeMode P → ℂ
  holonomy : ℂ → PrimeMode P → ℂ
  logPrime : PrimeMode P → ℝ
  criticalParam : ℝ → ℂ
  critical_holonomy :
    ∀ t : ℝ, ∀ p : PrimeMode P,
      holonomy (criticalParam t) p = bkCriticalHolonomy logPrime t p

namespace FiniteBerryKeatingCantorDirac

variable {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
variable (B : FiniteBerryKeatingCantorDirac P)

/-- Forget the BK structure and keep only the finite Cantor--Dirac packet. -/
def toCantorZetaDirac : FiniteCantorZetaDirac P :=
  { amplitude := B.amplitude, holonomy := B.holonomy }

/-- Finite BK Hamiltonian associated to the packet. -/
def H : CantorField P → CantorField P :=
  bkHamiltonian B.logPrime

/-- Critical-line finite BK evolution associated to the packet. -/
def U (t : ℝ) : CantorField P → CantorField P :=
  bkEvolution B.logPrime t

theorem U_zero : B.U 0 = id := by
  funext f
  funext S
  simp [U, bkEvolution, bkStatePhase]

/-! The finite Berry--Keating evolution is a genuine additive flow. -/
theorem U_add (s t : ℝ) : B.U (s + t) = B.U s ∘ B.U t := by
  funext f S
  simp [U, bkEvolution, bkStatePhase_add, Function.comp_apply, mul_assoc]

theorem U_neg_apply (t : ℝ) (f : CantorField P) (S : Vertex P) :
    B.U (-t) (B.U t f) S = f S := by
  change bkStatePhase B.logPrime (-t) S *
      (bkStatePhase B.logPrime t S * f S) = f S
  calc
    bkStatePhase B.logPrime (-t) S *
        (bkStatePhase B.logPrime t S * f S) =
        (bkStatePhase B.logPrime (-t) S *
          bkStatePhase B.logPrime t S) * f S := by ring
    _ = bkStatePhase B.logPrime (-t + t) S * f S := by
      rw [← bkStatePhase_add]
    _ = f S := by simp [bkStatePhase]

theorem U_neg_left (t : ℝ) : B.U (-t) ∘ B.U t = id := by
  funext f S
  simpa [Function.comp_apply] using B.U_neg_apply t f S

theorem U_neg_right (t : ℝ) : B.U t ∘ B.U (-t) = id := by
  funext f S
  simpa [Function.comp_apply] using B.U_neg_apply (-t) f S

/-- The zeta-Cantor creation supercharge at parameter `s`. -/
def Q (s : ℂ) : CantorField P → CantorField P :=
  B.toCantorZetaDirac.Q s

/-- The zeta-Cantor dual annihilation supercharge at parameter `s`. -/
def Qsharp (s : ℂ) : CantorField P → CantorField P :=
  B.toCantorZetaDirac.Qsharp s

/-- The finite zeta-Cantor Dirac operator at parameter `s`. -/
def D (s : ℂ) : CantorField P → CantorField P :=
  B.toCantorZetaDirac.op s

/-- The holonomy along the supplied critical parameter is the BK critical phase. -/
theorem holonomy_on_critical
    (t : ℝ) (p : PrimeMode P) :
    B.holonomy (B.criticalParam t) p = bkCriticalHolonomy B.logPrime t p :=
  B.critical_holonomy t p

end FiniteBerryKeatingCantorDirac

/- Direct finite Berry--Keating boundary statements. -/

theorem period_eq_logPrime
    {P : PrimeCantorZetaDiracOperator.PrimeCutoff}
    {B : FiniteBerryKeatingCantorDirac P}
    (period : PrimeMode P → ℝ)
    (hperiod : ∀ p : PrimeMode P, period p = B.logPrime p)
    (p : PrimeMode P) :
    period p = B.logPrime p :=
  hperiod p

/- Direct RH-safe spectral gate. -/

theorem zero_implies_critical
    (Xi : ℂ → ℂ)
    (CriticalLine SelfAdjointSector : ℂ → Prop)
    (zero_implies_selfAdjoint :
      ∀ s : ℂ, Xi s = 0 → SelfAdjointSector s)
    (selfAdjoint_iff_critical :
      ∀ s : ℂ, SelfAdjointSector s ↔ CriticalLine s)
    (s : ℂ)
    (hz : Xi s = 0) :
    CriticalLine s :=
  (selfAdjoint_iff_critical s).mp (zero_implies_selfAdjoint s hz)

end InfoGeometry.Arithmetic.PrimeCantorBerryKeatingOperator
