import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite quasiparticle--phonon secular equation

This is a two-channel algebraic truncation.  The two coordinates are labelled
`qp` and `ph`; no claim about a full QPNM, RPA, or nuclear spectroscopy is made.
-/

namespace InfoGeometry.Physics.SolovievFiniteSecularEigenproblem

abbrev Carrier := InfoGeometry.Algebra.FiniteSpin.Vec2R
abbrev Hamiltonian := InfoGeometry.Algebra.FiniteSpin.Mat2R

/-- Finite quasiparticle/phonon block Hamiltonian. -/
def blockHamiltonian (eQ eP v : ℝ) : Hamiltonian :=
  !![eQ, v; v, eP]

/-- The coordinate eigenvalue equation for the finite block. -/
def isEigenpair (H : Hamiltonian) (c : Carrier) (E : ℝ) : Prop :=
  H.mulVec c = E • c

/-- The secular polynomial of the finite two-channel block. -/
def secularPolynomial (eQ eP v E : ℝ) : ℝ :=
  (eQ - E) * (eP - E) - v ^ 2

/-- The matrix eigenvalue equation is exactly two coupled secular equations. -/
theorem block_eigenpair_iff
    (eQ eP v E : ℝ) (c : Carrier) :
    isEigenpair (blockHamiltonian eQ eP v) c E ↔
      (eQ * c 0 + v * c 1 = E * c 0 ∧
       v * c 0 + eP * c 1 = E * c 1) := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simpa [isEigenpair, blockHamiltonian, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, smul_eq_mul] using And.intro h0 h1
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i
    · simpa [isEigenpair, blockHamiltonian, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, smul_eq_mul] using h0
    · simpa [isEigenpair, blockHamiltonian, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, smul_eq_mul] using h1

/-- The determinant of the shifted block is its explicit secular polynomial. -/
theorem block_secular_determinant
    (eQ eP v E : ℝ) :
    (blockHamiltonian eQ eP v - E • (1 : Hamiltonian)).det =
      secularPolynomial eQ eP v E := by
  simp [blockHamiltonian, secularPolynomial, Matrix.det_fin_two]
  ring

/-- A nonzero eigenvector forces the explicit secular polynomial to vanish. -/
theorem nonzero_eigenpair_secular
    (eQ eP v E : ℝ) (c : Carrier) (hc : c ≠ 0)
    (heig : isEigenpair (blockHamiltonian eQ eP v) c E) :
    secularPolynomial eQ eP v E = 0 := by
  rcases (block_eigenpair_iff eQ eP v E c).mp heig with ⟨h0, h1⟩
  by_contra hdet
  have hc0 : c 0 = 0 := by
    by_contra h0c
    have hmul0 := congrArg (fun x => (eP - E) * x) h0
    have hmul1 := congrArg (fun x => v * x) h1
    have hprod : secularPolynomial eQ eP v E * c 0 = 0 := by
      dsimp [secularPolynomial]
      linear_combination hmul0 - hmul1
    exact h0c ((mul_eq_zero.mp hprod).resolve_left hdet)
  have hc1 : c 1 = 0 := by
    by_contra h1c
    have hmul0 := congrArg (fun x => v * x) h0
    have hmul1 := congrArg (fun x => (eQ - E) * x) h1
    have hprod : secularPolynomial eQ eP v E * c 1 = 0 := by
      dsimp [secularPolynomial]
      linear_combination hmul1 - hmul0
    exact h1c ((mul_eq_zero.mp hprod).resolve_left hdet)
  apply hc
  funext i
  fin_cases i
  · exact hc0
  · exact hc1

/-- A secular root with nonzero coupling has an explicit eigenvector. -/
theorem secular_root_has_eigenpair_of_coupling_ne_zero
    (eQ eP v E : ℝ) (hv : v ≠ 0)
    (hroot : secularPolynomial eQ eP v E = 0) :
    ∃ c : Carrier, c ≠ 0 ∧ isEigenpair (blockHamiltonian eQ eP v) c E := by
  refine ⟨![v, E - eQ], ?_, ?_⟩
  · intro hc
    have h0 := congrFun hc 0
    simpa using hv h0
  · apply (block_eigenpair_iff eQ eP v E ![v, E - eQ]).mpr
    constructor
    · simp
      ring
    · have hroot' : (eQ - E) * (eP - E) = v ^ 2 := by
        dsimp [secularPolynomial] at hroot
        linarith
      simp
      nlinarith

/-! The uncoupled case is still an exact finite spectral statement. -/

/-- Every secular root yields a nonzero eigenpair for the two-channel block. -/
theorem secular_root_has_nonzero_eigenpair
    (eQ eP v E : ℝ) (hroot : secularPolynomial eQ eP v E = 0) :
    ∃ c : Carrier, c ≠ 0 ∧ isEigenpair (blockHamiltonian eQ eP v) c E := by
  by_cases hv : v = 0
  · subst v
    have hprod : (eQ - E) * (eP - E) = 0 := by
      dsimp [secularPolynomial] at hroot
      simpa using hroot
    by_cases hQ : eQ - E = 0
    · refine ⟨![1, 0], ?_, ?_⟩
      · intro h
        have := congrFun h 0
        simp at this
      · apply (block_eigenpair_iff eQ eP 0 E ![1, 0]).mpr
        have h_eQ : eQ = E := sub_eq_zero.mp hQ
        subst h_eQ
        simp
    · have hP : eP - E = 0 := (mul_eq_zero.mp hprod).resolve_left hQ
      refine ⟨![0, 1], ?_, ?_⟩
      · intro h
        have := congrFun h 1
        simp at this
      · apply (block_eigenpair_iff eQ eP 0 E ![0, 1]).mpr
        have h_eP : eP = E := sub_eq_zero.mp hP
        subst h_eP
        simp
  · exact secular_root_has_eigenpair_of_coupling_ne_zero eQ eP v E hv hroot

end InfoGeometry.Physics.SolovievFiniteSecularEigenproblem
