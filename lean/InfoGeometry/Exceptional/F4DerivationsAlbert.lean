/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Dimension.Finrank
import InfoGeometry.Algebra.BaezF4H3Zorn
import InfoGeometry.Exceptional.AlbertAlgebraSplitJordan
import InfoGeometry.Algebra.H3ZornCarrierBasis
import InfoGeometry.Canonical.F4ActionMatrixRankCertificateBridge

open InfoGeometry.Algebra
open H3Zorn

attribute [local instance 100] LieRing.ofAssociativeRing

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

/-!
# Section 51: The 52-Dimensional Split Exceptional Lie Algebra 𝔣₄(4) and Jordan Derivations on 𝔍₃(𝕆_s)
Target: `InfoGeometry/Exceptional/F4DerivationsAlbert.lean`

Formalizes:
1. The actual 27-dimensional Albert carrier `H3Zorn ℝ`, via its coordinate basis.
2. An upper bound of 52 on the span of the explicitly indexed inner derivations.
   This owner does not prove that those generators are independent or that they
   span all Jordan derivations; exact F₄-carrier dimension remains conditional.
3. The Jordan Leibniz Derivation Lie Algebra:
   - 𝔣₄ = Der(𝔍₃(𝕆_s)) as a LieSubalgebra ℝ (Module.End ℝ (H3Zorn ℝ))
   - D(X * Y) = D X * Y + X * D Y
   - Annihilation of the Jordan unit: D(1) = 0
   - Preservation of the Leibniz rule under the Lie bracket [D, E]
4. Inner Derivations and Multiplication Commutators:
   - D_{A, B} = [L_A, L_B] = L_A L_B - L_B L_A ∈ 𝔣₄
   - Vanishing trace: Tr(D_{A,B}(X)) = 0
   - Antisymmetry: D_{B, A} = - D_{A, B}
   - Self-annihilation: D_{A, A} = 0
5. An explicitly indexed family of 52 candidate generators (not asserted to be a basis).
-/

namespace InfoGeometry.Exceptional.F4DerivationsAlbert

/-! ### 1. Carrier Dimension and Generator-Span Bound

The numeric partition 27 = 3 + 3·8 is recorded by the carrier basis owner,
and the F₄ dimension claim is not inferred from a Nat constant.  Exact
dimension of the derivation carrier still requires the soldering and generation
hypotheses documented in `F4ActionSolderingBridge`.
-/

/-- The installed Albert carrier has dimension 27, via its explicit coordinate basis. -/
theorem albert_dimension_eq : Module.finrank ℝ (H3Zorn ℝ) = 27 := by
  exact InfoGeometry.Algebra.finrank_h3zorn

/-- The span of the 52 named inner derivations has dimension at most 52.
This bound does not assert that the generators are independent or span all
Jordan derivations. -/
theorem f4_basis_span_finrank_le_52 :
    Module.finrank ℝ InfoGeometry.Algebra.f4BasisSpan ≤ 52 :=
  InfoGeometry.Canonical.F4ActionMatrix.f4BasisSpan_finrank_le_52

/-! ### 2. The Jordan Leibniz Derivation Lie Algebra -/

/-- Every element D of 𝔣₄ satisfies the Leibniz product rule for the Jordan product. -/
theorem f4_derivation_leibniz (D : H3ZornF4Derivations) (X Y : H3Zorn ℝ) :
    (D : Module.End ℝ (H3Zorn ℝ)) (X * Y) =
      (D : Module.End ℝ (H3Zorn ℝ)) X * Y + X * (D : Module.End ℝ (H3Zorn ℝ)) Y :=
  D.2 X Y

/-- The Lie bracket of two Jordan derivations satisfies the Leibniz product rule. -/
theorem f4_derivation_commutator (D E : H3ZornF4Derivations) (X Y : H3Zorn ℝ) :
    (⁅D, E⁆ : Module.End ℝ (H3Zorn ℝ)) (X * Y) =
      (⁅D, E⁆ : Module.End ℝ (H3Zorn ℝ)) X * Y + X * (⁅D, E⁆ : Module.End ℝ (H3Zorn ℝ)) Y :=
  H3ZornJordanDerivation_commutator D.2 E.2 X Y

/-- Every Jordan derivation annihilates the identity element: D(1) = 0. -/
theorem f4_derivation_unit_annihilation (D : H3ZornF4Derivations) :
    (D : Module.End ℝ (H3Zorn ℝ)) 1 = 0 :=
  h3Zorn_derivation_apply_one_eq_zero ⟨D.1, D.2⟩

/-! ### 3. Inner Derivations and Multiplication Commutators -/

/-- The inner derivation D_{A, B} = [L_A, L_B] as an element of the 𝔣₄ derivation Lie algebra. -/
noncomputable def innerDerivation (A B : H3Zorn ℝ) : H3ZornF4Derivations :=
  ⟨(h3ZornJordanInnerDerivation A B : Module.End ℝ (H3Zorn ℝ)),
   h3ZornJordanInnerDerivation_mem_F4 A B⟩

/-- Coordinate action of the inner derivation: D_{A, B}(X) = A * (B * X) - B * (A * X). -/
theorem innerDerivation_apply (A B X : H3Zorn ℝ) :
    (innerDerivation A B : Module.End ℝ (H3Zorn ℝ)) X =
      A * (B * X) - B * (A * X) :=
  h3ZornJordanInnerDerivation_apply A B X

/-- Inner derivations are strictly trace-free: Tr(D_{A, B}(X)) = 0 for all X. -/
theorem innerDerivation_trace_free (A B X : H3Zorn ℝ) :
    linearTrace ((innerDerivation A B : Module.End ℝ (H3Zorn ℝ)) X) = 0 :=
  h3ZornJordanInnerDerivation_linearTrace_zero A B X

/-- Self-inner derivations vanish identically: D_{A, A} = 0. -/
theorem innerDerivation_self_zero (A : H3Zorn ℝ) :
    (innerDerivation A A : Module.End ℝ (H3Zorn ℝ)) = 0 := by
  refine LinearMap.ext (fun X => ?_)
  rw [innerDerivation_apply, sub_self]
  rfl

/-- Inner derivations are antisymmetric in their arguments: D_{B, A} = - D_{A, B}. -/
theorem innerDerivation_antisymm (A B : H3Zorn ℝ) :
    (innerDerivation B A : Module.End ℝ (H3Zorn ℝ)) =
      -(innerDerivation A B : Module.End ℝ (H3Zorn ℝ)) := by
  refine LinearMap.ext (fun X => ?_)
  simp only [innerDerivation_apply, LinearMap.neg_apply]
  abel

/-! ### 4. Explicitly Indexed Inner-Derivation Family

The family `f4Basis : Fin 52 → ...` is defined by the carrier owner. Its index
type has 52 elements, but that fact alone is not a basis theorem; the meaningful
carrier-level consequence available unconditionally is `f4_basis_span_finrank_le_52`.
-/

end InfoGeometry.Exceptional.F4DerivationsAlbert
