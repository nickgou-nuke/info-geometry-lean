import proofs.NonIsoConf3QuadricD4PointCount

/-!
# Algebraic E-polynomial substitution for the D=4 point-count fingerprint

This file does **not** prove the purity/comparison theorem. It formalizes the
algebraic substitution step:

`#U_4(F_p) = P(p)`  ⇒  candidate `E_c(U_4; u,v) = P(uv)`.
-/

noncomputable section

namespace NonIsoConf3QuadricD4EPolynomial

/-- Integer form of the D=4 finite-field count polynomial. -/
def countPolynomialZ (T : ℤ) : ℤ :=
  T ^ 2 * (T - 1) ^ 2 * (T + 1) * (T ^ 3 - 2 * T ^ 2 - T + 3)

/-- Expanded form of the same polynomial. -/
def countPolynomialExpandedZ (T : ℤ) : ℤ :=
  T ^ 8 - 3 * T ^ 7 + 7 * T ^ 5 - 4 * T ^ 4 - 4 * T ^ 3 + 3 * T ^ 2

/-- The factorized and expanded integer count polynomials agree. -/
theorem countPolynomialZ_expand (T : ℤ) :
    countPolynomialZ T = countPolynomialExpandedZ T := by
  unfold countPolynomialZ countPolynomialExpandedZ
  ring

/-- Candidate compactly supported E-polynomial after the substitution `T = u*v`. -/
def candidateEc (u v : ℤ) : ℤ := countPolynomialZ (u * v)

/-- Expanded candidate compactly supported E-polynomial. -/
def candidateEcExpanded (u v : ℤ) : ℤ := countPolynomialExpandedZ (u * v)

/-- The candidate E-polynomial is just the point-count polynomial evaluated at `uv`. -/
theorem candidateEc_expand (u v : ℤ) :
    candidateEc u v = candidateEcExpanded u v := by
  unfold candidateEc candidateEcExpanded
  exact countPolynomialZ_expand (u * v)

/-- Specialization at `u=v=1` vanishes for the open space candidate. -/
theorem candidateEc_one_one : candidateEc 1 1 = 0 := by
  norm_num [candidateEc, countPolynomialZ]

/-- Specialization at `u=1`, `v=p` recovers the integer count polynomial at `p`. -/
theorem candidateEc_one_p (p : ℤ) : candidateEc 1 p = countPolynomialZ p := by
  simp [candidateEc]

/-- The recorded Lean/Nat point-count polynomial agrees with the integer
polynomial on the checked positive samples. -/
theorem countPolynomialZ_p3 : countPolynomialZ 3 = 1296 := by
  norm_num [countPolynomialZ]

theorem countPolynomialZ_p5 : countPolynomialZ 5 = 175200 := by
  norm_num [countPolynomialZ]

theorem countPolynomialZ_p7 : countPolynomialZ 7 = 3400992 := by
  norm_num [countPolynomialZ]

theorem countPolynomialZ_p11 : countPolynomialZ 11 = 156961200 := by
  norm_num [countPolynomialZ]

/-- Unconditional synthesis: the finite polynomial algebra gives the candidate 
compact-support E-polynomial properties. -/
theorem e_polynomial_synthesis :
    (∀ u v : ℤ, candidateEc u v = countPolynomialZ (u * v)) ∧
    (∀ u v : ℤ, candidateEc u v = candidateEcExpanded u v) ∧
    candidateEc 1 1 = 0 := by
  exact ⟨by intro u v; rfl, candidateEc_expand, candidateEc_one_one⟩

end NonIsoConf3QuadricD4EPolynomial

end noncomputable section
