import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeUHFFactorizationBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliLinearGaugeUHFFactorizationBridge

set_option linter.unusedSimpArgs false

/-!
# Cuntz Gauge Word Factorization and Diagonal Readout Bridge

This module formalizes the gauge-grading and factorization properties
of the canonical gauge state across the linear word core:

1. **Gauge-Grading on Word Monomials:**
   The degree difference $|u| - |v|$ defines the grade of word monomials $S_u S_v^*$,
   and a finite type of formal relation labels is assigned bookkeeping degree 0.
   The labels are not relation elements in an algebra.

2. **Action of the Conditional Expectation:**
   $E_0 : \text{WordCore} \to \text{WordCore}$ acts as the identity on equal-length
   monomials ($|u| = |v|$) and annihilates cross-grading terms.

3. **Gauge State Factorization on WordCore:**
   $$\varphi_0 = \tau_0 \circ E_0$$

4. **Exact Positivity on Diagonal Projections:**
   For every binary multi-index $u \in \text{List Bool}$, the diagonal projection
   $E_{uu} = S_u S_u^*$ has strictly positive expectation:
   $$\operatorname{Re}(\varphi_0(E_{uu})) = 2^{-|u|} > 0$$

Note: This owner establishes the linear and diagonal matrix-unit properties on the
word core. Full algebraic quotient descent by the two-sided Cuntz ideal $I_{\mathrm{Cuntz}}$
and arbitrary quadratic positivity $\varphi_0(a^* a) \ge 0$ belong to the next quotient owner.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CuntzGaugeQuotientDescentBridge

open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeUHFFactorizationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliLinearGaugeUHFFactorizationBridge

/-- Word degrees (length difference $|u| - |v|$). -/
def wordGrading (p : List Bool × List Bool) : ℤ :=
  (p.1.length : ℤ) - (p.2.length : ℤ)

/-- Formal names for the five standard Cuntz relations.

This is only a finite label type.  It does not construct relation elements,
an ideal, or a quotient of `WordCore`. -/
inductive CuntzRelation : Type
  | isometries_0 : CuntzRelation      -- S_0^* S_0 = 1
  | isometries_1 : CuntzRelation      -- S_1^* S_1 = 1
  | orthogonality_01 : CuntzRelation  -- S_0^* S_1 = 0
  | orthogonality_10 : CuntzRelation  -- S_1^* S_0 = 0
  | completeness : CuntzRelation      -- S_0 S_0^* + S_1 S_1^* = 1

/-- Bookkeeping degree attached to a formal relation label.

This does not compute the degree of an actual Cuntz relation element. -/
def relationDegree : CuntzRelation → ℤ
  | CuntzRelation.isometries_0 => 0
  | CuntzRelation.isometries_1 => 0
  | CuntzRelation.orthogonality_01 => 0
  | CuntzRelation.orthogonality_10 => 0
  | CuntzRelation.completeness => 0

/-- Every formal relation label has bookkeeping degree zero by definition.

This is not yet a homogeneity theorem for concrete relation elements. -/
theorem cuntz_relations_gauge_invariant (rel : CuntzRelation) :
    relationDegree rel = 0 := by
  cases rel <;> rfl

/-- The linear word-core projection preserves an equal-length monomial:
    $E_0(S_u S_v^\dagger) = S_u S_v^\dagger$ when $|u| = |v|$.

No quotient descent is involved. -/
theorem E0_preserves_degree_zero (u v : List Bool) (h : u.length = v.length) :
    E0 (wordMonomial u v) = wordMonomial u v := by
  simp [E0_monomial, h]

/-- Factorization of the linear word-core functional:
    $\varphi_0 = \tau_0 \circ E_0$.

The maps act on the finitely supported word carrier, not on a Cuntz quotient. -/
theorem phi0_factorization_eq :
    phi0 = tau0.comp E0 :=
  phi0_eq_tau0_comp_E0

/-- Diagonal word-kernel readout on $E_{uu} = S_u S_u^*$:
    $\varphi_0(E_{uu}) = 2^{-|u|}$.

This is a scalar diagonal evaluation, not positivity of the functional on all
quadratic elements. -/
theorem phi0_diagonal_monomial (u : List Bool) :
    phi0 (wordMonomial u u) = (1 / 2 : ℂ) ^ u.length := by
  rw [phi0_monomial, canonicalGaugeState_proj]

/-- Strict positivity of the real part of the diagonal readout:
    $\operatorname{Re}(\varphi_0(E_{uu})) = 2^{-|u|} > 0$.

This does not assert a positive functional on arbitrary $a^*a$. -/
theorem phi0_diagonal_re_pos (u : List Bool) :
    (phi0 (wordMonomial u u)).re > 0 := by
  rw [phi0_diagonal_monomial]
  have hreal : (1 / 2 : ℂ) ^ u.length = (((1 / 2 : ℝ) ^ u.length : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hreal]
  simp only [Complex.ofReal_re]
  positivity

end InfoGeometry.OperatorAlgebra.CuntzGaugeQuotientDescentBridge
