/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Canonical.KZResidueBracket
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Projective.Conf3ConcreteDLog
import InfoGeometry.Canonical.ArnoldCohenBCFWBridge

noncomputable section

namespace InfoGeometry.Canonical.KZLogarithmicConnection

open scoped BigOperators
open InfoGeometry.Projective.Conf3ConcreteDLog
open InfoGeometry.Canonical.ArnoldCohenBCFWBridge

/-!
# Three-point logarithmic coefficient and commutator identities

This module proves algebraic consequences of the three-point Arnold relation.
The scalar points are pairwise distinct, and the form carrier has the explicitly
assumed alternating bilinear operation `ExteriorFormAlgebra.wedge`.

`kz_connection_flatness` retains its historical name but proves only the
form-level Arnold cancellation; its exchange datum does not occur in the
conclusion. `kz_curvature_vanishes_of_cybe` proves that the three right-weighted
commutator contributions sum to zero when their cyclic commutators agree.
The historical name `CYBEExchangeData` denotes those explicit equalities; it
neither constructs Casimir residues nor supplies a Yang--Baxter representation.

No exterior derivative, complete connection curvature, flat bundle, parallel
transport, or monodromy is constructed here. The independent native Lie and
exterior factors are treated in `ArnoldKohnoParaKahlerConnection` and
`IndexedArnoldKohnoExterior`.
-/

section CYBE

variable {K : Type*} [Ring K]

/-! ## 1. Equal cyclic commutator data -/

/-- Three associative-algebra residues with equal cyclic commutators. The
name is retained for compatibility; the equalities are explicit hypotheses. -/
structure CYBEExchangeData (A : Type*) [Ring A] [Module K A] where
  t01 : A
  t12 : A
  t20 : A
  -- Assumed equal cyclic commutators.
  cybe_01_12 : bracket t01 t12 = bracket t12 t20
  cybe_12_20 : bracket t12 t20 = bracket t20 t01

namespace CYBEExchangeData

variable {A : Type*} [Ring A] [Module K A] (C : CYBEExchangeData (K := K) A)

theorem bracket_01_12_eq_12_20 :
    bracket C.t01 C.t12 = bracket C.t12 C.t20 :=
  C.cybe_01_12

theorem bracket_12_20_eq_20_01 :
    bracket C.t12 C.t20 = bracket C.t20 C.t01 :=
  C.cybe_12_20

theorem bracket_01_12_eq_20_01 :
    bracket C.t01 C.t12 = bracket C.t20 C.t01 :=
  C.cybe_01_12.trans C.cybe_12_20

/-- The sum of the three equal cyclic commutators.
    $[t_{01}, t_{12}] + [t_{12}, t_{20}] + [t_{20}, t_{01}] = 3 [t_{01}, t_{12}]$. -/
theorem cybe_sum_eq_three :
    bracket C.t01 C.t12 + bracket C.t12 C.t20 + bracket C.t20 C.t01 =
      bracket C.t01 C.t12 + bracket C.t01 C.t12 + bracket C.t01 C.t12 := by
  have h1 := (bracket_01_12_eq_12_20 C).symm
  have h2 := (bracket_01_12_eq_20_01 C).symm
  rw [h1, h2]

end CYBEExchangeData

end CYBE

variable {K : Type*} [Field K]

/-! ## 2. Arnold coefficient cancellation (not yet curvature)

The theorem below records the form-level Arnold cancellation only.  It does
not by itself establish curvature vanishing, since the exchange elements do
not occur in its conclusion.  The curvature-level statement is provided by
`kz_curvature_vanishes_of_cybe` below. -/

/-- Form-level Arnold cancellation. The exchange datum is unused; this
statement does not contain the operator-valued curvature contribution. -/
theorem kz_connection_flatness
    {M : Type*} [AddCommGroup M] [Module K M]
    (alg : ExteriorFormAlgebra (R := K) M)
    (dz : Fin 3 → M) (z : Fin 3 → K)
    (h01 : z 0 ≠ z 1) (h12 : z 1 ≠ z 2) (h20 : z 2 ≠ z 0)
    {A : Type*} [Ring A] [Algebra K A]
    (_C : CYBEExchangeData (K := K) A) :
    let w01 := conf3ConcreteForm dz z 0 1
    let w12 := conf3ConcreteForm dz z 1 2
    let w20 := conf3ConcreteForm dz z 2 0
    -- The scalar pre-factor multiplying each Casimir commutator vanishes by Arnold-Cohen
    alg.wedge w01 w12 + alg.wedge w12 w20 + alg.wedge w20 w01 = 0 := by
  intro w01 w12 w20
  exact conf3_concrete_arnold_relation alg dz z h01 h12 h20

/-- Cancellation of the three commutator-weighted terms in a common
coefficient algebra. The exchange elements multiply the alternating-form
values on the right, and the cyclic commutator hypotheses are used. -/
theorem kz_curvature_vanishes_of_cybe
    {A : Type*} [Ring A] [Algebra K A]
    (alg : ExteriorFormAlgebra (R := K) A)
    (dz : Fin 3 → A) (z : Fin 3 → K)
    (h01 : z 0 ≠ z 1) (h12 : z 1 ≠ z 2) (h20 : z 2 ≠ z 0)
    (C : CYBEExchangeData (K := K) A) :
    let w01 := conf3ConcreteForm dz z 0 1
    let w12 := conf3ConcreteForm dz z 1 2
    let w20 := conf3ConcreteForm dz z 2 0
    alg.wedge w01 w12 * bracket C.t01 C.t12 +
      alg.wedge w12 w20 * bracket C.t12 C.t20 +
      alg.wedge w20 w01 * bracket C.t20 C.t01 = 0 := by
  intro w01 w12 w20
  have hArnold : alg.wedge w01 w12 + alg.wedge w12 w20 +
      alg.wedge w20 w01 = 0 := by
    exact conf3_concrete_arnold_relation alg dz z h01 h12 h20
  have h12_20 : bracket C.t12 C.t20 = bracket C.t01 C.t12 :=
    C.cybe_01_12.symm
  have h20_01 : bracket C.t20 C.t01 = bracket C.t01 C.t12 :=
    C.cybe_01_12.trans C.cybe_12_20 |>.symm
  rw [h12_20, h20_01, ← add_mul, ← add_mul, hArnold, zero_mul]

/-! ## 3. 4-Point Moduli Space Cross-Ratio Logarithmic Form -/

/-- Rational 4-point cross-ratio difference identity:
    $\frac{1}{z_0 - z_2} + \frac{1}{z_1 - z_3} - \frac{1}{z_0 - z_3} - \frac{1}{z_1 - z_2} = \frac{-(z_0 - z_1)(z_2 - z_3)(z_0 + z_1 - z_2 - z_3)}{(z_0 - z_2)(z_1 - z_3)(z_0 - z_3)(z_1 - z_2)}$. -/
theorem four_point_cross_ratio_dlog_identity
    (z₀ z₁ z₂ z₃ : K)
    (h02 : z₀ ≠ z₂) (h13 : z₁ ≠ z₃) (h03 : z₀ ≠ z₃) (h12 : z₁ ≠ z₂) :
    (1 / (z₀ - z₂)) + (1 / (z₁ - z₃)) - (1 / (z₀ - z₃)) - (1 / (z₁ - z₂)) =
      - (((z₀ - z₁) * (z₂ - z₃) * (z₀ + z₁ - z₂ - z₃)) /
         ((z₀ - z₂) * (z₁ - z₃) * (z₀ - z₃) * (z₁ - z₂))) := by
  have d02 : z₀ - z₂ ≠ 0 := sub_ne_zero.mpr h02
  have d13 : z₁ - z₃ ≠ 0 := sub_ne_zero.mpr h13
  have d03 : z₀ - z₃ ≠ 0 := sub_ne_zero.mpr h03
  have d12 : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr h12
  field_simp [d02, d13, d03, d12]
  ring

/-! ## 4. Combined algebraic identities -/

/-- Conjunction of the form-level Arnold identity, the assumed cyclic
commutator equalities, and a four-point rational identity. Its historical
name does not assert an analytic flatness or moduli-space construction. -/
theorem grand_kz_moduli_synthesis
    {M : Type*} [AddCommGroup M] [Module K M]
    (alg : ExteriorFormAlgebra (R := K) M)
    (dz : Fin 3 → M) (z : Fin 3 → K)
    (h01 : z 0 ≠ z 1) (h12 : z 1 ≠ z 2) (h20 : z 2 ≠ z 0)
    {A : Type*} [Ring A] [Algebra K A]
    (C : CYBEExchangeData (K := K) A)
    (w₀ w₁ w₂ w₃ : K)
    (hw02 : w₀ ≠ w₂) (hw13 : w₁ ≠ w₃) (hw03 : w₀ ≠ w₃) (hw12 : w₁ ≠ w₂) :
    -- (1) Form-level Arnold cancellation
    (alg.wedge (conf3ConcreteForm dz z 0 1) (conf3ConcreteForm dz z 1 2) +
     alg.wedge (conf3ConcreteForm dz z 1 2) (conf3ConcreteForm dz z 2 0) +
     alg.wedge (conf3ConcreteForm dz z 2 0) (conf3ConcreteForm dz z 0 1) = 0) ∧
    -- (2) Assumed cyclic commutator agreement
    (bracket C.t01 C.t12 = bracket C.t12 C.t20 ∧
     bracket C.t12 C.t20 = bracket C.t20 C.t01) ∧
    -- (3) Four-point rational identity
    ((1 / (w₀ - w₂)) + (1 / (w₁ - w₃)) - (1 / (w₀ - w₃)) - (1 / (w₁ - w₂)) =
      - (((w₀ - w₁) * (w₂ - w₃) * (w₀ + w₁ - w₂ - w₃)) /
         ((w₀ - w₂) * (w₁ - w₃) * (w₀ - w₃) * (w₁ - w₂)))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact conf3_concrete_arnold_relation alg dz z h01 h12 h20
  · exact ⟨C.cybe_01_12, C.cybe_12_20⟩
  · exact four_point_cross_ratio_dlog_identity w₀ w₁ w₂ w₃ hw02 hw13 hw03 hw12

end InfoGeometry.Canonical.KZLogarithmicConnection
