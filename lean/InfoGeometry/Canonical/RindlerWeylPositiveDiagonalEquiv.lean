import InfoGeometry.Canonical.RindlerWeylDecomposition
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Positive diagonal logarithmic coordinates

This owner bundles the verified logarithmic reconstruction into an actual
equivalence between the positive quadrant and the `(ξ, η)`-plane.  It does
not assert a Zorn, Weyl, Rindler-flow, or modular-action theorem.
-/

namespace InfoGeometry.Canonical.RindlerWeylDecomposition

noncomputable section

/-- The positive diagonal quadrant. -/
abbrev PositiveDiagonal :=
  {p : ℝ × ℝ // 0 < p.1 ∧ 0 < p.2}

/-- Logarithmic geometric-mean and ratio coordinates. -/
def toRindlerWeyl (p : PositiveDiagonal) : ℝ × ℝ :=
  (xi p.1.1 p.1.2, eta p.1.1 p.1.2)

/-- Exponential reconstruction from `(ξ, η)` coordinates. -/
def fromRindlerWeyl (p : ℝ × ℝ) : PositiveDiagonal :=
  ⟨(Real.exp (p.1 + p.2), Real.exp (p.1 - p.2)),
    Real.exp_pos _, Real.exp_pos _⟩

theorem fromRindlerWeyl_toRindlerWeyl (p : PositiveDiagonal) :
    fromRindlerWeyl (toRindlerWeyl p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · exact exp_xi_add_eta_eq_r (r := p.1.1) (s := p.1.2) p.2.1
  · exact exp_xi_sub_eta_eq_s (r := p.1.1) (s := p.1.2) p.2.2

theorem toRindlerWeyl_fromRindlerWeyl (p : ℝ × ℝ) :
    toRindlerWeyl (fromRindlerWeyl p) = p := by
  apply Prod.ext
  · simp [toRindlerWeyl, fromRindlerWeyl, xi, eta,
      Real.log_exp]
  · simp [toRindlerWeyl, fromRindlerWeyl, xi, eta,
      Real.log_exp]

/-- Global logarithmic coordinates on the positive diagonal quadrant. -/
noncomputable def positiveDiagonalEquiv : PositiveDiagonal ≃ ℝ × ℝ where
  toFun := toRindlerWeyl
  invFun := fromRindlerWeyl
  left_inv := fromRindlerWeyl_toRindlerWeyl
  right_inv := toRindlerWeyl_fromRindlerWeyl

@[simp] theorem positiveDiagonalEquiv_apply (p : PositiveDiagonal) :
    positiveDiagonalEquiv p = toRindlerWeyl p := rfl

@[simp] theorem positiveDiagonalEquiv_symm_apply (p : ℝ × ℝ) :
    positiveDiagonalEquiv.symm p = fromRindlerWeyl p := rfl

end
end InfoGeometry.Canonical.RindlerWeylDecomposition
