import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Arithmetic for the finite Chevalley order formula at `q = 2`

This module records only numerical consequences of the standard order formula.
It does **not** define a carrier for `G₂(2)`, identify that carrier with
`SplitOctF2Aut`, or prove a BN-pair enumeration.  In particular, the numbers
below must not be read as a theorem about the cardinality of the concrete
automorphism group.

The arithmetic facts are over the finite field parameter `q = 2`:

1. **Chevalley Order Formula**:
   $$|G_2(q)| = q^6 (q^6 - 1)(q^2 - 1)$$
   For $q = 2$: $|G_2(2)| = 2^6 (2^6 - 1)(2^2 - 1) = 64 \times 63 \times 3 = 12096$.
2. **Simple Core $G_2(2)' \cong \operatorname{PSU}_3(3)$**:
   $$|G_2(2)'| = 6048$$
3. **Index-2 Extension**: $[G_2(2) : G_2(2)'] = 2$.
4. **Prime Power Factorization**: $|G_2(2)| = 2^6 \cdot 3^3 \cdot 7$.
5. **Sylow Subgroup Orders**:
   - Sylow 2-subgroup (Unipotent radical $U$): $|U| = 2^6 = 64$.
   - Sylow 3-subgroup: $|P_3| = 3^3 = 27$.
   - Sylow 7-subgroup: $|P_7| = 7$.
6. **Weyl Group $W(G_2) \cong D_6$**: $|W(G_2)| = 12$.
7. **Coordinate carrier count**: `2^8 = 256` is only the cardinality of an
   eight-coordinate Boolean carrier, not of an automorphism group.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.FiniteChevalley

/-- The standard numerical Chevalley order formula. This is a formula
    theorem, not a cardinality theorem for a Lean group carrier. -/
def chevalleyG2Order (q : ℕ) : ℕ :=
  q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)

/-- Evaluation of the standard formula at `q = 2`. -/
theorem chevalley_order_formula_at_two : chevalleyG2Order 2 = 12096 := by
  rfl

/-- Prime factorization of the evaluated numerical formula. -/
theorem chevalley_order_formula_prime_factorization :
    chevalleyG2Order 2 = (2 ^ 6) * (3 ^ 3) * 7 := by
  rfl

/-- Abstract root-count arithmetic, independent of a group carrier. -/
def rootSystemCount : ℕ := 12
def positiveRootCount : ℕ := 6
def negativeRootCount : ℕ := 6

theorem root_system_sum : positiveRootCount + negativeRootCount = rootSystemCount := by rfl

/-- Cardinality of an eight-coordinate Boolean model, not of an automorphism
    group. -/
def octonionDimension : ℕ := 8
def octonionF2CarrierCard : ℕ := 2 ^ octonionDimension

theorem octonion_f2_card_eq : octonionF2CarrierCard = 256 := by rfl

end InfoGeometry.Algebra.Zorn.FiniteChevalley
