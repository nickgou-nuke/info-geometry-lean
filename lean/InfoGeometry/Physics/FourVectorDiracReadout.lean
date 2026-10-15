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

/-- In the finite Clifford carrier, nilpotence of the momentum slash is
equivalent to the massless Minkowski condition.  This is distinct from the
universal square-zero identity for generators in the exterior algebra. -/
theorem diracSlash_nilpotent_iff_lightlike (p : FourVector) :
    diracSlash p * diracSlash p = 0 ↔ minkowskiSq p = 0 := by
  rw [diracSlash_sq]
  constructor
  · intro h
    have h00 := congrArg (fun M : DiracMatrix => M 0 0) h
    have hscalar : (minkowskiSq p : ℂ) = 0 := by
      simpa using h00
    exact_mod_cast hscalar
  · intro h
    rw [h]
    simp

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

/-- The scalar-plus-slash Dirac factor vanishes only at zero momentum and
zero mass.  This concrete coordinate fact handles the degenerate case in
the mass-shell-to-kernel direction below. -/
theorem diracSlash_add_scalar_eq_zero_iff
    (p : FourVector) (m : ℝ) :
    diracSlash p + (m : ℂ) • (1 : DiracMatrix) = 0 ↔
      p = ⟨0, 0, 0, 0⟩ ∧ m = 0 := by
  rcases p with ⟨t, x, y, z⟩
  constructor
  · intro h
    have h00 : (t : ℂ) + (m : ℂ) = 0 := by
      simpa [diracSlash, gamma, gamma0, gamma1, gamma2, gamma3] using
        congrArg (fun M : DiracMatrix => M 0 0) h
    have h22 : -(t : ℂ) + (m : ℂ) = 0 := by
      simpa [diracSlash, gamma, gamma0, gamma1, gamma2, gamma3] using
        congrArg (fun M : DiracMatrix => M 2 2) h
    have h02 : (z : ℂ) = 0 := by
      simpa [diracSlash, gamma, gamma0, gamma1, gamma2, gamma3] using
        congrArg (fun M : DiracMatrix => M 0 2) h
    have h03 : (x : ℂ) + -((y : ℂ) * Complex.I) = 0 := by
      simpa [diracSlash, gamma, gamma0, gamma1, gamma2, gamma3] using
        congrArg (fun M : DiracMatrix => M 0 3) h
    have ht₀ : t = 0 := by
      have h₁ : t + m = 0 := by exact_mod_cast h00
      have h₂ : -t + m = 0 := by exact_mod_cast h22
      linarith
    have hm₀ : m = 0 := by
      have h₁ : t + m = 0 := by exact_mod_cast h00
      rw [ht₀] at h₁
      linarith
    have hx₀ : x = 0 := by
      have hre := congrArg Complex.re h03
      simpa using hre
    have hy₀ : y = 0 := by
      have him := congrArg Complex.im h03
      have hneg : -y = 0 := by simpa using him
      linarith
    have hz₀ : z = 0 := by exact_mod_cast h02
    constructor
    · simp only [FourVector.mk.injEq]
      exact ⟨ht₀, hx₀, hy₀, hz₀⟩
    · exact hm₀
  · rintro ⟨hp, hm⟩
    simp only [FourVector.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl, rfl, rfl⟩
    subst m
    simp [diracSlash, gamma, gamma0, gamma1, gamma2, gamma3]

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

/-- On the algebraic mass shell, the finite massive Dirac factor has a
nonzero spinor in its kernel.  The zero momentum/zero mass case is handled
separately; otherwise the companion factor supplies a nonzero kernel vector
through the conjugate-factor identity. -/
theorem mass_shell_implies_nonzero_dirac_kernel
    (p : FourVector) (m : ℝ) (hMass : minkowskiSq p = m ^ 2) :
    ∃ ψ : Fin 4 → ℂ, ψ ≠ 0 ∧
      Matrix.mulVec (diracSlash p - (m : ℂ) • (1 : DiracMatrix)) ψ = 0 := by
  let A : DiracMatrix := diracSlash p - (m : ℂ) • (1 : DiracMatrix)
  let B : DiracMatrix := diracSlash p + (m : ℂ) • (1 : DiracMatrix)
  have hAB : A * B = 0 := by
    rw [diracSlash_mass_factorization, hMass]
    simp
  by_cases hB : B = 0
  · have hp₀m₀ : p = ⟨0, 0, 0, 0⟩ ∧ m = 0 :=
      (diracSlash_add_scalar_eq_zero_iff p m).mp (by simpa [B] using hB)
    rcases hp₀m₀ with ⟨rfl, rfl⟩
    let ψ : Fin 4 → ℂ := fun i => if i = 0 then 1 else 0
    refine ⟨ψ, ?_, ?_⟩
    · intro hzero
      have hzero₀ := congrFun hzero 0
      simp [ψ] at hzero₀
    · have hA : diracSlash (⟨0, 0, 0, 0⟩ : FourVector) -
          (0 : ℂ) • (1 : DiracMatrix) = 0 := by
        ext i j
        simp [diracSlash, gamma, gamma0, gamma1, gamma2, gamma3]
      change Matrix.mulVec
        (diracSlash (⟨0, 0, 0, 0⟩ : FourVector) -
          (0 : ℂ) • (1 : DiracMatrix)) ψ = 0
      rw [hA]
      simp
  · have hentry : ∃ i j : Fin 4, B i j ≠ 0 := by
      by_contra h
      apply hB
      ext i j
      exact not_ne_iff.mp (not_exists.mp (not_exists.mp h i) j)
    obtain ⟨i, j, hij⟩ := hentry
    let e : Fin 4 → ℂ := Pi.single j 1
    let ψ : Fin 4 → ℂ := B.mulVec e
    have hcoord : ψ i = B i j := by
      dsimp [ψ, e]
      exact congrFun (Matrix.mulVec_single_one B j) i
    have hψ : ψ ≠ 0 := by
      intro hzero
      apply hij
      rw [← hcoord, hzero]
      rfl
    have hmul : Matrix.mulVec (A * B) e = 0 := by
      rw [hAB]
      simp
    have hkernel : Matrix.mulVec A (B.mulVec e) = 0 := by
      simpa only [Matrix.mulVec_mulVec] using hmul
    exact ⟨ψ, hψ, hkernel⟩

/-- The finite Stokes carrier is null in the Pauli/Hestenes quadratic form. -/
theorem stokes_pauli_determinant_zero (J : JonesSpinor) :
    Matrix.det (InfoGeometry.Geometry.PauliParavectorBridge.pauliMatrix
      (JonesSpinor.stokesMinkowski4 J)) = 0 := by
  exact JonesSpinor.stokesPauli_det_zero J

end InfoGeometry.Physics.FourVectorDiracReadout
