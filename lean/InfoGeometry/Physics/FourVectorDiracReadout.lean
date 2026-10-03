import InfoGeometry.Clifford.DiracPauliGamma
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Geometry.PauliParavectorBridge
import InfoGeometry.Physics.LorentzBoostMinkowski
import InfoGeometry.Optics.JonesPoincareSphere

/-!
# Finite Dirac and Stokes four-vector readouts

This owner records only finite matrix identities.  It does not construct a
Poincare representation or a Pauli--Lubanski operator.  The Dirac identity is
the concrete Clifford linearisation of the Minkowski quadratic form, while
the Stokes statement reuses the existing Jones/Pauli null readout.
-/

noncomputable section

namespace InfoGeometry.Physics.FourVectorDiracReadout

open InfoGeometry.Clifford.DiracPauliGamma
open InfoGeometry.Geometry.PauliParavectorBridge
open InfoGeometry.Physics.LorentzBoostMinkowski
open InfoGeometry.Optics.JonesPoincareSphere

/-- The finite Dirac slash of a real `(+---)` four-vector. -/
def diracSlash (p : FourVector) : DiracMatrix :=
  (p.t : ℂ) • gamma 0 + (p.x : ℂ) • gamma 1 +
    (p.y : ℂ) • gamma 2 + (p.z : ℂ) • gamma 3

theorem diracSlash_sq (p : FourVector) :
    diracSlash p * diracSlash p =
      (minkowskiSq p : ℂ) • (1 : DiracMatrix) := by
  rcases p with ⟨t, x, y, z⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracSlash, gamma, gamma0, gamma1, gamma2, gamma3,
      minkowskiSq, minkowskiPair, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.smul_apply] <;>
    ring_nf <;>
    simp <;>
    ring

theorem diracSlash_square_readout (p : FourVector) :
    diracSlash p * diracSlash p =
      (minkowskiSq p : ℂ) • (1 : DiracMatrix) :=
  diracSlash_sq p

/--
The massive Clifford factorization follows from the slash-square identity:
the product of the two conjugate Dirac factors is the scalar mass-shell
polynomial times the identity.  This is an algebraic identity for every
four-vector and mass parameter; it does not assert that every vector is on
shell.
-/
theorem diracSlash_mass_factorization (p : FourVector) (m : ℝ) :
    (diracSlash p - (m : ℂ) • (1 : DiracMatrix)) *
        (diracSlash p + (m : ℂ) • (1 : DiracMatrix)) =
      ((minkowskiSq p : ℂ) - (m : ℂ) ^ 2) • (1 : DiracMatrix) := by
  have hfactor :
      (diracSlash p - (m : ℂ) • (1 : DiracMatrix)) *
          (diracSlash p + (m : ℂ) • (1 : DiracMatrix)) =
        diracSlash p * diracSlash p - (m : ℂ) ^ 2 • (1 : DiracMatrix) := by
    rw [sub_mul, mul_add]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
    module
  rw [hfactor, diracSlash_sq]
  ext i j
  simp only [Matrix.smul_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

/-- The Dirac factor product vanishes precisely on the algebraic mass shell.

This equivalence belongs to the finite Clifford/matrix carrier.  It is
independent of the exterior-square Plücker condition, whose quadratic form
tests decomposability of a bivector rather than the Minkowski norm of a
four-momentum. -/
theorem diracSlash_factorization_zero_iff_mass_shell
    (p : FourVector) (m : ℝ) :
    (diracSlash p - (m : ℂ) • (1 : DiracMatrix)) *
        (diracSlash p + (m : ℂ) • (1 : DiracMatrix)) = 0 ↔
      minkowskiSq p = m ^ 2 := by
  rw [diracSlash_mass_factorization]
  constructor
  · intro h
    have h00 := congrArg (fun M : DiracMatrix => M 0 0) h
    have hcomplex : ((minkowskiSq p : ℝ) : ℂ) - (m : ℂ) ^ 2 = 0 := by
      simpa using h00
    exact_mod_cast sub_eq_zero.mp hcomplex
  · intro h
    have hscalar : (minkowskiSq p : ℂ) - (m : ℂ) ^ 2 = 0 := by
      exact_mod_cast sub_eq_zero.mpr h
    rw [hscalar]
    ext i j
    simp

/--
A nonzero spinor in the kernel of the massive Dirac factor forces the
corresponding four-vector onto the algebraic mass shell.  The nonzero-spinor
hypothesis is essential: the zero vector solves every homogeneous equation.
-/
theorem dirac_equation_nonzero_spinor_implies_mass_shell
    (p : FourVector) (m : ℝ) (ψ : Fin 4 → ℂ)
    (hψ : ψ ≠ 0)
    (hDirac : Matrix.mulVec
      (diracSlash p - (m : ℂ) • (1 : DiracMatrix)) ψ = 0) :
    minkowskiSq p = m ^ 2 := by
  let A : DiracMatrix := diracSlash p - (m : ℂ) • (1 : DiracMatrix)
  let B : DiracMatrix := diracSlash p + (m : ℂ) • (1 : DiracMatrix)
  have hreverse : B * A =
      ((minkowskiSq p : ℂ) - (m : ℂ) ^ 2) • (1 : DiracMatrix) := by
    calc
      B * A = diracSlash p * diracSlash p -
          (m : ℂ) ^ 2 • (1 : DiracMatrix) := by
        dsimp [A, B]
        rw [mul_sub, add_mul]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
          Matrix.mul_one]
        simp only [smul_add, smul_smul]
        ext i j
        simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.add_apply,
          Matrix.sub_apply, Complex.real_smul, smul_eq_mul]
        push_cast
        ring
      _ = ((minkowskiSq p : ℂ) - (m : ℂ) ^ 2) •
          (1 : DiracMatrix) := by
        rw [diracSlash_sq]
        ext i j
        simp only [Matrix.smul_apply, Matrix.one_apply]
        by_cases h : i = j <;> simp [h]
  have hzero : Matrix.mulVec (B * A) ψ = 0 := by
    rw [← Matrix.mulVec_mulVec, hDirac, Matrix.mulVec_zero]
  have hscalar : ((minkowskiSq p : ℂ) - (m : ℂ) ^ 2) • ψ = 0 := by
    simpa only [hreverse, Matrix.smul_mulVec, Matrix.one_mulVec] using hzero
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, ψ i ≠ 0 := by
    by_contra hnone
    apply hψ
    funext i
    exact not_ne_iff.mp (not_exists.mp hnone i)
  have hcoordinate := congrFun hscalar i
  have hcoef : (minkowskiSq p : ℂ) - (m : ℂ) ^ 2 = 0 := by
    exact (mul_eq_zero.mp (by simpa using hcoordinate)).resolve_right hi
  have hmass : (minkowskiSq p : ℂ) = (m : ℂ) ^ 2 := sub_eq_zero.mp hcoef
  exact_mod_cast hmass

/-- The finite Stokes carrier is null in the Pauli/Hestenes quadratic form. -/
theorem stokes_pauli_determinant_zero (J : JonesSpinor) :
    Matrix.det (InfoGeometry.Geometry.PauliParavectorBridge.pauliMatrix
      (JonesSpinor.stokesMinkowski4 J)) = 0 := by
  exact JonesSpinor.stokesPauli_det_zero J

end InfoGeometry.Physics.FourVectorDiracReadout
