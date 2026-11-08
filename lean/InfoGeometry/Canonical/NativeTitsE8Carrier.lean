import Mathlib.LinearAlgebra.TensorProduct.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.QuadraticJordanH3Zorn
import InfoGeometry.Algebra.H3ZornCarrierBasis
import InfoGeometry.Algebra.H3ZornF4Basis
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Algebra.BaezF4H3Zorn

/-!
# Native carrier layer for the split Tits `E8` construction

This file replaces the dimension-only magic-square bookkeeping by actual
repository carriers as far as the current theorem graph permits.

For the split-octonion / split-Albert Tits decomposition

`Der(O_s) ⊕ (O_s' ⊗ H3(O_s)') ⊕ Der(H3(O_s))`

we construct the two traceless submodules natively and prove their real
finranks `7` and `26`.  Hence the mixed tensor carrier has real finrank `182`.
The existing split-octonion derivation owner contributes the proved finrank
`14`.

The repository does not yet prove
`Module.finrank ℝ H3ZornF4Derivations = 52`; that exact statement is retained
as the single explicit hypothesis in the final `248`-dimensional carrier
readout.  No `E8` Lie bracket or Jacobi theorem is inferred from dimension
bookkeeping alone.
-/

noncomputable section

namespace InfoGeometry.Canonical.NativeTitsE8Carrier

open scoped TensorProduct
open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Algebra.ZornVectorMatrix

abbrev VZ := ZornVectorMatrix ℝ

/-- The native split-octonion trace as a linear functional. -/
def zornTraceLinear : VZ →ₗ[ℝ] ℝ where
  toFun := ZornVectorMatrix.trace
  map_add' X Y := by
    simp [ZornVectorMatrix.trace, ZornVectorMatrix.add]
    ring
  map_smul' r X := by
    simp [ZornVectorMatrix.trace, ZornVectorMatrix.smul]
    ring

/-- Native traceless split-octonions `O_s' = ker Tr`. -/
def splitOctonionTraceZero : Submodule ℝ VZ :=
  LinearMap.ker zornTraceLinear

/-- Literal coordinate linear equivalence used only to read the ambient
split-octonion dimension from the existing vector-Zorn carrier. -/
def zornVectorCoordinateLinearEquiv :
    VZ ≃ₗ[ℝ] (ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ) × ℝ) where
  toFun X := (X.a, X.v, X.w, X.b)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv X := by cases X; rfl
  right_inv p := by rcases p with ⟨a, v, w, b⟩; rfl
  map_add' X Y := by rfl
  map_smul' r X := by rfl

/-- The native vector-Zorn split-octonion carrier has real dimension eight. -/
theorem finrank_zornVectorMatrix : Module.finrank ℝ VZ = 8 := by
  rw [zornVectorCoordinateLinearEquiv.finrank_eq]
  simp

/-- The split-octonion trace functional is nonzero. -/
theorem zornTraceLinear_ne_zero : zornTraceLinear ≠ 0 := by
  intro h
  have hE := congrArg
    (fun f : VZ →ₗ[ℝ] ℝ => f (ZornVectorMatrix.E11 : VZ)) h
  norm_num [zornTraceLinear, ZornVectorMatrix.trace,
    ZornVectorMatrix.E11] at hE

/-- The actual traceless split-octonion submodule has real finrank seven. -/
theorem finrank_splitOctonionTraceZero :
    Module.finrank ℝ splitOctonionTraceZero = 7 := by
  change Module.finrank ℝ (LinearMap.ker zornTraceLinear) = 7
  letI : FiniteDimensional ℝ VZ :=
    InfoGeometry.Algebra.zornCoordinateBasis.finiteDimensional_of_finite
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero
    zornTraceLinear_ne_zero
  rw [finrank_zornVectorMatrix] at h
  omega

/-- The native H3 diagonal trace as a linear functional. -/
def h3TraceLinear : H3Zorn ℝ →ₗ[ℝ] ℝ where
  toFun := H3Zorn.linearTrace
  map_add' X Y := H3Zorn.linearTrace_add X Y
  map_smul' r X := by
    simpa [smul_eq_mul] using H3Zorn.linearTrace_smul r X

/-- Native traceless Albert carrier `H3(O_s)' = ker Tr`. -/
def h3TraceZero : Submodule ℝ (H3Zorn ℝ) :=
  LinearMap.ker h3TraceLinear

/-- The new kernel definition is extensionally the repository's existing
`H3Zorn.traceZero` submodule. -/
theorem h3TraceZero_eq_native :
    h3TraceZero = H3Zorn.traceZero (R := ℝ) := by
  ext X
  rfl

/-- The H3 trace functional is nonzero. -/
theorem h3TraceLinear_ne_zero : h3TraceLinear ≠ 0 := by
  intro h
  have hE := congrArg
    (fun f : H3Zorn ℝ →ₗ[ℝ] ℝ => f (H3Zorn.E1 : H3Zorn ℝ)) h
  norm_num [h3TraceLinear, H3Zorn.linearTrace, H3Zorn.E1] at hE

/-- The actual traceless split-Albert submodule has real finrank twenty-six. -/
theorem finrank_h3TraceZero :
    Module.finrank ℝ h3TraceZero = 26 := by
  letI : FiniteDimensional ℝ (H3Zorn ℝ) :=
    h3ZornBasis.finiteDimensional_of_finite
  change Module.finrank ℝ (LinearMap.ker h3TraceLinear) = 26
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero
    h3TraceLinear_ne_zero
  rw [InfoGeometry.Algebra.finrank_h3zorn] at h
  omega

/-- The mixed Tits carrier `O_s' tensor H3(O_s)'`. -/
abbrev MixedCarrier :=
  splitOctonionTraceZero ⊗[ℝ] h3TraceZero

/-- The mixed carrier has the genuine tensor-product finrank `7 * 26 = 182`. -/
theorem finrank_mixedCarrier : Module.finrank ℝ MixedCarrier = 182 := by
  letI : Module.Free ℝ splitOctonionTraceZero :=
    Module.Free.of_divisionRing ℝ splitOctonionTraceZero
  letI : Module.Free ℝ h3TraceZero :=
    Module.Free.of_divisionRing ℝ h3TraceZero
  letI : Module.Finite ℝ splitOctonionTraceZero :=
    Module.finite_of_finrank_pos (by
      rw [finrank_splitOctonionTraceZero]
      norm_num)
  letI : Module.Finite ℝ h3TraceZero :=
    Module.finite_of_finrank_pos (by
      rw [finrank_h3TraceZero]
      norm_num)
  rw [Module.finrank_tensorProduct,
    finrank_splitOctonionTraceZero, finrank_h3TraceZero]

/-- Existing native split-octonion derivation carrier. -/
abbrev G2DerivationCarrier :=
  InfoGeometry.Lie.CanonicalZornDerivationDimension.VDer

/-- The split-octonion derivation carrier has the already-proved finrank 14. -/
theorem finrank_g2DerivationCarrier :
    Module.finrank ℝ G2DerivationCarrier = 14 :=
  InfoGeometry.Lie.CanonicalZornDerivationDimension.finrank_vectorDerivations

/-- Existing native Jordan-derivation Lie subalgebra on the split Albert
carrier.  Its exact real finrank `52` is intentionally not assumed here. -/
abbrev F4DerivationCarrier := H3ZornF4Derivations

/-- The theorem-safe native Tits carrier before any Lie-bracket identification. -/
abbrev NativeTitsCarrier :=
  G2DerivationCarrier × MixedCarrier × F4DerivationCarrier

/-- The first two genuine native summands contribute `14 + 182 = 196`
dimensions independently of the unresolved F4 classification theorem. -/
theorem finrank_g2_plus_mixed :
    Module.finrank ℝ (G2DerivationCarrier × MixedCarrier) = 196 := by
  letI : Module.Free ℝ G2DerivationCarrier :=
    Module.Free.of_divisionRing ℝ G2DerivationCarrier
  letI : Module.Finite ℝ G2DerivationCarrier :=
    Module.finite_of_finrank_pos (by
      rw [finrank_g2DerivationCarrier]
      norm_num)
  letI : Module.Free ℝ MixedCarrier :=
    Module.Free.of_divisionRing ℝ MixedCarrier
  letI : Module.Finite ℝ MixedCarrier :=
    Module.finite_of_finrank_pos (by
      rw [finrank_mixedCarrier]
      norm_num)
  rw [Module.finrank_prod, finrank_g2DerivationCarrier, finrank_mixedCarrier]

/-- Exact remaining theorem boundary for the maximal split Tits cell:
if the native Albert derivation carrier has the expected finrank `52`, then
the actual direct-sum carrier has finrank `248`.

This is deliberately conditional: equal dimension does not by itself equip the
carrier with the `E8(8)` Lie bracket or prove a real-form isomorphism. -/
theorem finrank_nativeTitsCarrier_of_f4
    (hF4 : Module.finrank ℝ F4DerivationCarrier = 52) :
    Module.finrank ℝ NativeTitsCarrier = 248 := by
  letI : Module.Free ℝ MixedCarrier :=
    Module.Free.of_divisionRing ℝ MixedCarrier
  letI : Module.Finite ℝ MixedCarrier :=
    Module.finite_of_finrank_pos (by
      rw [finrank_mixedCarrier]
      norm_num)
  letI : Module.Free ℝ F4DerivationCarrier :=
    Module.Free.of_divisionRing ℝ F4DerivationCarrier
  letI : Module.Finite ℝ F4DerivationCarrier :=
    Module.finite_of_finrank_pos (by
      rw [hF4]
      norm_num)
  letI : Module.Free ℝ G2DerivationCarrier :=
    Module.Free.of_divisionRing ℝ G2DerivationCarrier
  letI : Module.Finite ℝ G2DerivationCarrier :=
    Module.finite_of_finrank_pos (by
      rw [finrank_g2DerivationCarrier]
      norm_num)
  rw [Module.finrank_prod, Module.finrank_prod,
    finrank_g2DerivationCarrier, finrank_mixedCarrier, hF4]

/-- Compact native-carrier packet exposing both proved traceless dimensions and
the exact remaining F4 finrank obligation. -/
theorem native_tits_carrier_packet :
    Module.finrank ℝ splitOctonionTraceZero = 7 ∧
    Module.finrank ℝ h3TraceZero = 26 ∧
    Module.finrank ℝ MixedCarrier = 182 ∧
    Module.finrank ℝ G2DerivationCarrier = 14 := by
  exact ⟨finrank_splitOctonionTraceZero, finrank_h3TraceZero,
    finrank_mixedCarrier, finrank_g2DerivationCarrier⟩

end InfoGeometry.Canonical.NativeTitsE8Carrier

end noncomputable section
