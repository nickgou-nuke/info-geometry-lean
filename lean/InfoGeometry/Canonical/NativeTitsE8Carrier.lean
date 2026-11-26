/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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
import InfoGeometry.Algebra.H3ZornF4DimensionClosure
import InfoGeometry.Canonical.SplitFreudenthalTitsE8Carrier

/-!
# Native carrier layer for the split Tits `E8` construction

This file replaces the dimension-only magic-square bookkeeping by actual
repository carriers:

For the split-octonion / split-Albert Tits decomposition

`Der(O_s) ⊕ (O_s' ⊗ H3(O_s)') ⊕ Der(H3(O_s))`

we construct the two traceless submodules natively and prove their real
finranks `7` and `26`, so the mixed tensor carrier has real finrank `182`.
The split-octonion derivation owner contributes finrank `14`, and
`H3ZornF4DimensionClosure` unconditionally supplies `finrank ℝ H3ZornF4Derivations = 52`,
yielding the unconditional `248`-dimensional carrier theorem
`finrank_nativeTitsCarrier` as well as a linear equivalence
`nativeToSplitTitsE8Equiv` to `SplitFreudenthalTitsE8Carrier.SplitTitsE8Carrier`.
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
  let _inst : FiniteDimensional ℝ VZ :=
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
    simp [smul_eq_mul, H3Zorn.linearTrace_smul]

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
  let _inst : FiniteDimensional ℝ (H3Zorn ℝ) :=
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
  let _free1 : Module.Free ℝ splitOctonionTraceZero :=
    Module.Free.of_divisionRing ℝ splitOctonionTraceZero
  let _free2 : Module.Free ℝ h3TraceZero :=
    Module.Free.of_divisionRing ℝ h3TraceZero
  let _fin1 : Module.Finite ℝ splitOctonionTraceZero :=
    Module.finite_of_finrank_pos (by
      rw [finrank_splitOctonionTraceZero]
      norm_num)
  let _fin2 : Module.Finite ℝ h3TraceZero :=
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
carrier, whose real finrank `52` is established unconditionally in
`H3ZornF4DimensionClosure`. -/
abbrev F4DerivationCarrier := H3ZornF4Derivations

/-- The native split-Albert derivation carrier has real finrank 52. -/
theorem finrank_f4DerivationCarrier :
    Module.finrank ℝ F4DerivationCarrier = 52 :=
  InfoGeometry.Algebra.finrank_H3ZornF4Derivations

/-- The theorem-safe native Tits carrier before any Lie-bracket identification. -/
abbrev NativeTitsCarrier :=
  G2DerivationCarrier × MixedCarrier × F4DerivationCarrier

/-- The first two genuine native summands contribute `14 + 182 = 196`
dimensions. -/
theorem finrank_g2_plus_mixed :
    Module.finrank ℝ (G2DerivationCarrier × MixedCarrier) = 196 := by
  let _free1 : Module.Free ℝ G2DerivationCarrier :=
    Module.Free.of_divisionRing ℝ G2DerivationCarrier
  let _fin1 : Module.Finite ℝ G2DerivationCarrier :=
    Module.finite_of_finrank_pos (by
      rw [finrank_g2DerivationCarrier]
      norm_num)
  let _free2 : Module.Free ℝ MixedCarrier :=
    Module.Free.of_divisionRing ℝ MixedCarrier
  let _fin2 : Module.Finite ℝ MixedCarrier :=
    Module.finite_of_finrank_pos (by
      rw [finrank_mixedCarrier]
      norm_num)
  rw [Module.finrank_prod, finrank_g2DerivationCarrier, finrank_mixedCarrier]

/-- Conditional form retained for compatibility: given `finrank ℝ F4DerivationCarrier = 52`,
the direct-sum carrier has finrank `248`. -/
theorem finrank_nativeTitsCarrier_of_f4
    (hF4 : Module.finrank ℝ F4DerivationCarrier = 52) :
    Module.finrank ℝ NativeTitsCarrier = 248 := by
  let _free1 : Module.Free ℝ MixedCarrier :=
    Module.Free.of_divisionRing ℝ MixedCarrier
  let _fin1 : Module.Finite ℝ MixedCarrier :=
    Module.finite_of_finrank_pos (by
      rw [finrank_mixedCarrier]
      norm_num)
  let _free2 : Module.Free ℝ F4DerivationCarrier :=
    Module.Free.of_divisionRing ℝ F4DerivationCarrier
  let _fin2 : Module.Finite ℝ F4DerivationCarrier :=
    Module.finite_of_finrank_pos (by
      rw [hF4]
      norm_num)
  let _free3 : Module.Free ℝ G2DerivationCarrier :=
    Module.Free.of_divisionRing ℝ G2DerivationCarrier
  let _fin3 : Module.Finite ℝ G2DerivationCarrier :=
    Module.finite_of_finrank_pos (by
      rw [finrank_g2DerivationCarrier]
      norm_num)
  rw [Module.finrank_prod, Module.finrank_prod,
    finrank_g2DerivationCarrier, finrank_mixedCarrier, hF4]

/-- Unconditional 248-dimensional finrank of the native Tits `E8` carrier. -/
theorem finrank_nativeTitsCarrier :
    Module.finrank ℝ NativeTitsCarrier = 248 :=
  finrank_nativeTitsCarrier_of_f4 finrank_f4DerivationCarrier

/-- Currying linear equivalence between `Fin 7 × Fin 26 → ℝ` and
`Matrix (Fin 7) (Fin 26) ℝ`. -/
def mixedCurryMatrixEquiv :
    (Fin 7 × Fin 26 → ℝ) ≃ₗ[ℝ]
      SplitFreudenthalTitsE8Carrier.MixedCoordinateCarrier where
  toFun f i j := f (i, j)
  invFun M p := M p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Linear equivalence unifying the native 182D tensor carrier with the
`7 × 26` coordinate matrix carrier of `SplitFreudenthalTitsE8Carrier`. -/
def mixedCarrierToCoordinateEquiv :
    MixedCarrier ≃ₗ[ℝ] SplitFreudenthalTitsE8Carrier.MixedCoordinateCarrier :=
  letI : Module.Finite ℝ splitOctonionTraceZero :=
    Module.finite_of_finrank_pos (by
      rw [finrank_splitOctonionTraceZero]
      norm_num)
  letI : Module.Finite ℝ h3TraceZero :=
    Module.finite_of_finrank_pos (by
      rw [finrank_h3TraceZero]
      norm_num)
  let b7 : Module.Basis (Fin 7) ℝ splitOctonionTraceZero :=
    Module.finBasisOfFinrankEq ℝ splitOctonionTraceZero finrank_splitOctonionTraceZero
  let b26 : Module.Basis (Fin 26) ℝ h3TraceZero :=
    Module.finBasisOfFinrankEq ℝ h3TraceZero finrank_h3TraceZero
  (b7.tensorProduct b26).equivFun.trans mixedCurryMatrixEquiv

/-- Explicit 52-element basis of `F4DerivationCarrier` constructed from `f4Basis`
and `H3ZornF4DimensionClosure`. -/
def f4DerivationBasis : Module.Basis (Fin 52) ℝ F4DerivationCarrier :=
  letI : LieRing (Module.End ℝ (H3Zorn ℝ)) := LieRing.ofAssociativeRing
  letI : LieAlgebra ℝ (Module.End ℝ (H3Zorn ℝ)) := LieAlgebra.ofAssociativeAlgebra
  let v : Fin 52 → F4DerivationCarrier := fun i =>
    ⟨(f4Basis i).1, (f4Basis i).2⟩
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    intro D _
    have hD_span : (D : Module.End ℝ (H3Zorn ℝ)) ∈ f4BasisSpan := by
      rw [f4BasisSpan_eq_H3ZornF4Derivations]
      exact D.2
    have hmap :
        Submodule.map H3ZornF4Derivations.toSubmodule.subtype
            (Submodule.span ℝ (Set.range v)) = f4BasisSpan := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    have hmem_map :
        H3ZornF4Derivations.toSubmodule.subtype D ∈
          Submodule.map H3ZornF4Derivations.toSubmodule.subtype
            (Submodule.span ℝ (Set.range v)) := by
      rw [hmap]
      exact hD_span
    rcases Submodule.mem_map.mp hmem_map with ⟨D', hD', hEq⟩
    have hDD' : D' = D := H3ZornF4Derivations.toSubmodule.injective_subtype hEq
    subst hDD'
    exact hD'
  letI : Module.Finite ℝ F4DerivationCarrier :=
    Module.finite_of_finrank_pos (by
      rw [finrank_f4DerivationCarrier]
      norm_num)
  basisOfTopLeSpanOfCardEqFinrank v htop
    (by rw [Fintype.card_fin, finrank_f4DerivationCarrier])

/-- Linear equivalence unifying the native 52D `F4DerivationCarrier` with the
certified 52D `F4CertifiedCarrier` via `f4Basis` and `f4ActionMatrixReal`. -/
def f4DerivationToCertifiedEquiv :
    F4DerivationCarrier ≃ₗ[ℝ] SplitFreudenthalTitsE8Carrier.F4CertifiedCarrier :=
  let bCert : Module.Basis (Fin 52) ℝ SplitFreudenthalTitsE8Carrier.F4CertifiedCarrier :=
    Module.Basis.span
      InfoGeometry.Canonical.F4ActionMatrixRationalCertificate.f4ActionMatrixReal_linearIndependent
  f4DerivationBasis.equiv bCert (Equiv.refl (Fin 52))

/-- Clean linear equivalence unifying the native 248D `NativeTitsCarrier` with
`SplitFreudenthalTitsE8Carrier.SplitTitsE8Carrier`. -/
def nativeToSplitTitsE8Equiv :
    NativeTitsCarrier ≃ₗ[ℝ] SplitFreudenthalTitsE8Carrier.SplitTitsE8Carrier :=
  InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv.prodCongr
    (mixedCarrierToCoordinateEquiv.prodCongr f4DerivationToCertifiedEquiv)

/-- Compact native-carrier packet exposing all proved finranks including `F4` and
the full `248`-dimensional native carrier. -/
theorem native_tits_carrier_packet :
    Module.finrank ℝ splitOctonionTraceZero = 7 ∧
    Module.finrank ℝ h3TraceZero = 26 ∧
    Module.finrank ℝ MixedCarrier = 182 ∧
    Module.finrank ℝ G2DerivationCarrier = 14 ∧
    Module.finrank ℝ F4DerivationCarrier = 52 ∧
    Module.finrank ℝ NativeTitsCarrier = 248 := by
  exact ⟨finrank_splitOctonionTraceZero, finrank_h3TraceZero,
    finrank_mixedCarrier, finrank_g2DerivationCarrier,
    finrank_f4DerivationCarrier, finrank_nativeTitsCarrier⟩

end InfoGeometry.Canonical.NativeTitsE8Carrier

end noncomputable section
