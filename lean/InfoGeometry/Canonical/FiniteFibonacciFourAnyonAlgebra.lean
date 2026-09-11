import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteFibonacciFourAnyonBlocks

/-!
# InfoGeometry.Canonical.FiniteFibonacciFourAnyonAlgebra

Finite algebraic checks from the four-Fibonacci-anyon block calculation.

The analytic derivation of the four-point conformal blocks uses hypergeometric
functions and analytic continuation.  This file formalizes only algebraic pieces
that are independent of that analytic layer:

* the `Z₃` parafermion conformal dimensions obtained from the general formulas;
* the finite mass-dimension arithmetic check in the `M = 0` four-anyon case;
* elementary cross-ratio changes of variables;
* the polynomial/rational identity between the three `r = 0` limiting
  Read--Rezayi splitting factors.

No hypergeometric functions.
No analytic continuation theorem.
No conformal-block construction.
No monodromy matrix claim.
-/

namespace InfoGeometry.Canonical.FiniteFibonacciFourAnyonAlgebra

/-- General `Zₖ` order-parameter conformal dimension, as a rational scalar. -/
def sigmaDimension (k l : ℚ) : ℚ :=
  l * (k - l) / (2 * k * (k + 2))

/-- General `Zₖ` parafermionic-current conformal dimension, as a rational scalar. -/
def psiDimension (k l : ℚ) : ℚ :=
  l * (k - l) / k

/-- General neutral-field conformal dimension, as a rational scalar. -/
def epsilonDimension (k j : ℚ) : ℚ :=
  j * (j + 1) / (k + 2)

/-- For `Z₃`, the field `σ₁` has conformal dimension `1 / 15`. -/
theorem sigmaDimension_three_one :
    sigmaDimension 3 1 = 1 / 15 := by
  norm_num [sigmaDimension]

/-- For `Z₃`, the current `ψ₁` has conformal dimension `2 / 3`. -/
theorem psiDimension_three_one :
    psiDimension 3 1 = 2 / 3 := by
  norm_num [psiDimension]

/-- For `Z₃`, the Fibonacci field `ε = ε(1)` has conformal dimension `2 / 5`. -/
theorem epsilonDimension_three_one :
    epsilonDimension 3 1 = 2 / 5 := by
  norm_num [epsilonDimension]

/-- Homogeneous-polynomial mass dimension from equation `(2.17)`. -/
def rrPolynomialMassDimension (r : ℚ) : ℚ :=
  -3 * (r + 1) * (r + 2)

/-- Expanded form of the polynomial mass dimension. -/
theorem rrPolynomialMassDimension_expand (r : ℚ) :
    rrPolynomialMassDimension r = -3 * r ^ 2 - 9 * r - 6 := by
  simp [rrPolynomialMassDimension]
  ring

/-- Prefactor mass dimension in the `M = 0` case of equation `(2.20)`. -/
def prefactorMassDimensionM0 (r : ℚ) : ℚ :=
  3 * r ^ 2 + 11 * r + 31 / 3

/-- The coefficient contribution from the four-anyon block formula. -/
def fourAnyonCoefficientMassShift : ℚ :=
  -7 / 5

/-- The parafermionic correlator dimension readout. -/
def parafermionCorrelatorDimension (r : ℚ) : ℚ :=
  4 / 15 + (2 / 3) * (3 * r + 4)

/-- The finite scale-dimension consistency check from equation `(2.22)`. -/
theorem fourAnyon_dimension_consistency (r : ℚ) :
    prefactorMassDimensionM0 r + rrPolynomialMassDimension r +
        fourAnyonCoefficientMassShift =
      parafermionCorrelatorDimension r := by
  simp [prefactorMassDimensionM0, rrPolynomialMassDimension,
    fourAnyonCoefficientMassShift, parafermionCorrelatorDimension]
  ring

/-- Cross-ratio change of variables `x = η / (η - 1)`. -/
noncomputable def xFromEta (η : ℝ) : ℝ :=
  η / (η - 1)

/-- If `x = η/(η-1)`, then `1 - x = 1/(1-η)`. -/
theorem one_sub_xFromEta {η : ℝ} (hη : η ≠ 1) :
    1 - xFromEta η = 1 / (1 - η) := by
  have h1 : 1 - η ≠ 0 := sub_ne_zero.mpr (Ne.symm hη)
  have h2 : η - 1 ≠ 0 := sub_ne_zero.mpr hη
  unfold xFromEta
  field_simp [h1, h2]
  ring

/-- If `x = η/(η-1)`, then `x/(x-1) = η`. -/
theorem xFromEta_div_sub_one {η : ℝ} (hη : η ≠ 1) :
    xFromEta η / (xFromEta η - 1) = η := by
  have h2 : η - 1 ≠ 0 := sub_ne_zero.mpr hη
  unfold xFromEta
  field_simp [h2]
  ring

/-- The `r = 0` limiting factor for the `12,34` splitting, suppressing common notation. -/
noncomputable def psi1234Limit (W η : ℝ) : ℝ :=
  (2 / 9) * W ^ 3 * (1 - η) * (2 - η) / η ^ 3

/-- The `r = 0` limiting factor for the `13,24` splitting. -/
noncomputable def psi1324Limit (W η : ℝ) : ℝ :=
  (2 / 9) * W ^ 3 * (1 - η) * (1 - 2 * η) / η ^ 2

/-- The `r = 0` limiting factor for the `14,23` splitting. -/
noncomputable def psi1423Limit (W η : ℝ) : ℝ :=
  -(2 / 9) * W ^ 3 * (1 + η) / η ^ 2

/-- The `η`-form of the finite linear relation among the three limiting splittings. -/
theorem psi_limit_linear_relation {W η : ℝ} (hη : η ≠ 0) :
    (1 - η) * psi1423Limit W η =
      -η * psi1234Limit W η + psi1324Limit W η := by
  unfold psi1234Limit psi1324Limit psi1423Limit
  field_simp [hη]
  ring

end InfoGeometry.Canonical.FiniteFibonacciFourAnyonAlgebra
