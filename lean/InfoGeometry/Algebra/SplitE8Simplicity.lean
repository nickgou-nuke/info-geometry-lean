/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SplitE8RootSystem
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Weights.IsSimple
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# Simplicity, `IsKilling`, and `E₈` `RootSystem` for `SplitE8Lie` (`𝔈₈(8)`)

Proves natively (without `sorry` or custom axioms) that the 248-dimensional split real
exceptional Lie algebra `SplitE8Lie` (`𝔈₈(8)`) constructed via the Freudenthal–Tits Magic
Square has nonvanishing opposite-root brackets `⁅e8RootVec r, e8RootVec (e8RootNeg r)⁆ ≠ 0`
across all `240` roots, has no nonzero abelian ideals (`NoAbelianIdeal`), has trivial radical
(`LieAlgebra.HasTrivialRadical`), trivial center, non-degenerate Killing form
(`LieAlgebra.IsKilling`), and 1-dimensional root spaces.

Constructs the Mathlib root system `splitE8RootSystem := LieAlgebra.IsKilling.rootSystem
splitE8Cartan`, establishes `IsRootSystem`, `IsCrystallographic`, `IsReduced`, the exact
`240`-root bijection `Fin 240 ≃ splitE8Cartan.root`, an explicit `RootPairing.Base` whose
Cartan matrix equals `CartanMatrix.E 8`, `IsIrreducible`, and hence `LieAlgebra.IsSimple`
and `LieAlgebra.IsSemisimple` for `SplitE8Lie`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open scoped BigOperators TensorProduct
open H3Zorn
open InfoGeometry.Algebra.MagicSquareTitsBracket
open InfoGeometry.Canonical.NativeTitsE8Carrier
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit
open InfoGeometry.Exceptional.CFSGPort.Chevalley
open InfoGeometry.Lie.CanonicalZornDerivationDimension

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private abbrev VZ := InfoGeometry.Canonical.NativeTitsE8Carrier.VZ
private abbrev VDer := InfoGeometry.Canonical.NativeTitsE8Carrier.G2DerivationCarrier

/-! ## 1. Universal Opposite-Root Bracket Nonvanishing (`240` Roots) -/

section OppositeRootNonvanishing

private theorem forall_fin240_of_blocks (P : Fin 240 → Bool)
    (h0 : (List.finRange 24).all (fun k => P ⟨0 + k.val, by omega⟩) = true)
    (h1 : (List.finRange 24).all (fun k => P ⟨24 + k.val, by omega⟩) = true)
    (h2 : (List.finRange 24).all (fun k => P ⟨48 + k.val, by omega⟩) = true)
    (h3 : (List.finRange 24).all (fun k => P ⟨72 + k.val, by omega⟩) = true)
    (h4 : (List.finRange 24).all (fun k => P ⟨96 + k.val, by omega⟩) = true)
    (h5 : (List.finRange 24).all (fun k => P ⟨120 + k.val, by omega⟩) = true)
    (h6 : (List.finRange 24).all (fun k => P ⟨144 + k.val, by omega⟩) = true)
    (h7 : (List.finRange 24).all (fun k => P ⟨168 + k.val, by omega⟩) = true)
    (h8 : (List.finRange 24).all (fun k => P ⟨192 + k.val, by omega⟩) = true)
    (h9 : (List.finRange 24).all (fun k => P ⟨216 + k.val, by omega⟩) = true)
    (r : Fin 240) : P r = true := by
  have hb : ∀ (off : ℕ) (hoff : off + 24 ≤ 240),
      (List.finRange 24).all (fun k => P ⟨off + k.val, by omega⟩) = true →
      ∀ k : Fin 24, P ⟨off + k.val, by omega⟩ = true := by
    intro off hoff hchk k
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
    exact hchk k
  by_cases c0 : r.val < 24
  · have heq : (⟨0 + (⟨r.val, c0⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
      Fin.ext (by dsimp; omega)
    simpa [heq] using hb 0 (by decide) h0 ⟨r.val, c0⟩
  · by_cases c1 : r.val < 48
    · have hk : r.val - 24 < 24 := by omega
      have heq : (⟨24 + (⟨r.val - 24, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
        Fin.ext (by dsimp; omega)
      simpa [heq] using hb 24 (by decide) h1 ⟨r.val - 24, hk⟩
    · by_cases c2 : r.val < 72
      · have hk : r.val - 48 < 24 := by omega
        have heq : (⟨48 + (⟨r.val - 48, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
          Fin.ext (by dsimp; omega)
        simpa [heq] using hb 48 (by decide) h2 ⟨r.val - 48, hk⟩
      · by_cases c3 : r.val < 96
        · have hk : r.val - 72 < 24 := by omega
          have heq : (⟨72 + (⟨r.val - 72, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
            Fin.ext (by dsimp; omega)
          simpa [heq] using hb 72 (by decide) h3 ⟨r.val - 72, hk⟩
        · by_cases c4 : r.val < 120
          · have hk : r.val - 96 < 24 := by omega
            have heq : (⟨96 + (⟨r.val - 96, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
              Fin.ext (by dsimp; omega)
            simpa [heq] using hb 96 (by decide) h4 ⟨r.val - 96, hk⟩
          · by_cases c5 : r.val < 144
            · have hk : r.val - 120 < 24 := by omega
              have heq : (⟨120 + (⟨r.val - 120, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                Fin.ext (by dsimp; omega)
              simpa [heq] using hb 120 (by decide) h5 ⟨r.val - 120, hk⟩
            · by_cases c6 : r.val < 168
              · have hk : r.val - 144 < 24 := by omega
                have heq : (⟨144 + (⟨r.val - 144, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                  Fin.ext (by dsimp; omega)
                simpa [heq] using hb 144 (by decide) h6 ⟨r.val - 144, hk⟩
              · by_cases c7 : r.val < 192
                · have hk : r.val - 168 < 24 := by omega
                  have heq : (⟨168 + (⟨r.val - 168, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                    Fin.ext (by dsimp; omega)
                  simpa [heq] using hb 168 (by decide) h7 ⟨r.val - 168, hk⟩
                · by_cases c8 : r.val < 216
                  · have hk : r.val - 192 < 24 := by omega
                    have heq : (⟨192 + (⟨r.val - 192, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                      Fin.ext (by dsimp; omega)
                    simpa [heq] using hb 192 (by decide) h8 ⟨r.val - 192, hk⟩
                  · have hk : r.val - 216 < 24 := by omega
                    have heq : (⟨216 + (⟨r.val - 216, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                      Fin.ext (by dsimp; omega)
                    simpa [heq] using hb 216 (by decide) h9 ⟨r.val - 216, hk⟩

private theorem sparseToMat_ne_zero_of_not_sparseZeroCheck {s : SparseMat27}
    (h : sparseZeroCheck s = false) : (sparseToMat s).map (Int.cast : ℤ → ℝ) ≠ 0 := by
  intro h0
  have hzm : sparseToMat s = 0 := by
    ext a b
    have hab := congrFun (congrFun h0 a) b
    simpa [Matrix.map_apply] using hab
  have hzc : sparseZeroCheck s = true := by
    simp only [sparseZeroCheck, List.all_eq_true, beq_iff_eq]
    intro p _
    exact congrFun (congrFun hzm p.1) p.2.1
  rw [h] at hzc
  cases hzc

private theorem h3zornToMatrix_four_f4Inner (x y : h3TraceZero)
    (sx sy : SparseMat27)
    (hx : h3zornToMatrix ((2 : ℝ) • jordanLmul (R := ℝ) x.1) = (sparseToMat sx).map Int.cast)
    (hy : h3zornToMatrix ((2 : ℝ) • jordanLmul (R := ℝ) y.1) = (sparseToMat sy).map Int.cast) :
    h3zornToMatrix ((4 : ℝ) • (f4Inner x y : Module.End ℝ (H3Zorn ℝ))) =
      (sparseToMat (sparseComm sx sy)).map Int.cast := by
  have h4 : (4 : ℝ) • (f4Inner x y : Module.End ℝ (H3Zorn ℝ)) =
      ((2 : ℝ) • jordanLmul (R := ℝ) x.1) * ((2 : ℝ) • jordanLmul (R := ℝ) y.1) -
        ((2 : ℝ) • jordanLmul (R := ℝ) y.1) * ((2 : ℝ) • jordanLmul (R := ℝ) x.1) := by
    apply LinearMap.ext
    intro z
    change (4 : ℝ) • (x.1 * (y.1 * z) - y.1 * (x.1 * z)) =
      (2 : ℝ) • (x.1 * ((2 : ℝ) • (y.1 * z))) - (2 : ℝ) • (y.1 * ((2 : ℝ) • (x.1 * z)))
    rw [mul_smul_comm, mul_smul_comm, smul_smul, smul_smul]
    norm_num
    module
  rw [h4, map_sub, map_mul, map_mul, hx, hy, sparseToMat_comm]
  ext a b
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, Int.cast_sub, Int.cast_sum,
    Int.cast_mul]

private theorem projG2_mk (g : G2DerivationCarrier) (m : MixedCarrier) (f : F4DerivationCarrier) :
    projG2 ⟨g, m, f⟩ = g := rfl

private theorem projF4_mk (g : G2DerivationCarrier) (m : MixedCarrier) (f : F4DerivationCarrier) :
    projF4 ⟨g, m, f⟩ = f := rfl

private theorem vz_sub_a (X Y : VZ) : (X - Y).a = X.a - Y.a := rfl
private theorem vz_sub_v (X Y : VZ) (i : Fin 3) : (X - Y).v i = X.v i - Y.v i := rfl
private theorem vz_sub_w (X Y : VZ) (i : Fin 3) : (X - Y).w i = X.w i - Y.w i := rfl
private theorem vz_sub_b (X Y : VZ) : (X - Y).b = X.b - Y.b := rfl

private theorem g2_param_bracket_neg_ne_zero :
    ⁅g2Param 1, g2Param 5⁆ ≠ 0 ∧ ⁅g2Param 2, g2Param 11⁆ ≠ 0 ∧ ⁅g2Param 7, g2Param 12⁆ ≠ 0 := by
  have hbr : ∀ (D₁ D₂ : VDer) (X : VZ), (⁅D₁, D₂⁆).toFun X = D₁ (D₂ X) - D₂ (D₁ X) :=
    fun _ _ _ => rfl
  have hz0 : ∀ (X : VZ) (k : Fin 3), ((0 : VDer).toFun X).v k = 0 := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have hv := congrArg (fun D : VDer => (D.toFun (zornU 0).1).v 0) h0
    rw [hz0] at hv
    simp only [hbr, vz_sub_v, g2Param, parameterDerivation, parameterAction, zornU,
      ZornVectorMatrix.U, ZornVec3.basis] at hv
    norm_num at hv
  · intro h0
    have hv := congrArg (fun D : VDer => (D.toFun (zornU 0).1).v 0) h0
    rw [hz0] at hv
    simp only [hbr, vz_sub_v, g2Param, parameterDerivation, parameterAction, zornU,
      ZornVectorMatrix.U, ZornVec3.basis] at hv
    norm_num at hv
  · intro h0
    have hv := congrArg (fun D : VDer => (D.toFun (zornU 1).1).v 1) h0
    rw [hz0] at hv
    simp only [hbr, vz_sub_v, g2Param, parameterDerivation, parameterAction, zornU,
      ZornVectorMatrix.U, ZornVec3.basis] at hv
    norm_num at hv

private theorem sector1_bracket_neg_ne_zero (r : Fin 6) :
    ⁅e8RootVec ⟨r.val, by omega⟩, e8RootVec (e8RootNeg ⟨r.val, by omega⟩)⁆ ≠ 0 := by
  have ⟨h15, h211, h712⟩ := g2_param_bracket_neg_ne_zero
  have hv0 : e8RootVec 0 = embedG2 (g2Param 1) := by dsimp [e8RootVec]; simp [g2LongIdx]
  have hv1 : e8RootVec 1 = embedG2 (g2Param 2) := by dsimp [e8RootVec]; simp [g2LongIdx]
  have hv2 : e8RootVec 2 = embedG2 (g2Param 5) := by dsimp [e8RootVec]; simp [g2LongIdx]
  have hv3 : e8RootVec 3 = embedG2 (g2Param 7) := by dsimp [e8RootVec]; simp [g2LongIdx]
  have hv4 : e8RootVec 4 = embedG2 (g2Param 11) := by dsimp [e8RootVec]; simp [g2LongIdx]
  have hv5 : e8RootVec 5 = embedG2 (g2Param 12) := by dsimp [e8RootVec]; simp [g2LongIdx]
  have hn0 : e8RootNeg 0 = 2 := by decide
  have hn1 : e8RootNeg 1 = 4 := by decide
  have hn2 : e8RootNeg 2 = 0 := by decide
  have hn3 : e8RootNeg 3 = 5 := by decide
  have hn4 : e8RootNeg 4 = 1 := by decide
  have hn5 : e8RootNeg 5 = 3 := by decide
  fin_cases r
  · intro h0
    change ⁅e8RootVec 0, e8RootVec (e8RootNeg 0)⁆ = 0 at h0
    rw [hn0, hv0, hv2, bracket_g2_g2] at h0
    exact h15 (congrArg projG2 h0)
  · intro h0
    change ⁅e8RootVec 1, e8RootVec (e8RootNeg 1)⁆ = 0 at h0
    rw [hn1, hv1, hv4, bracket_g2_g2] at h0
    exact h211 (congrArg projG2 h0)
  · intro h0
    change ⁅e8RootVec 2, e8RootVec (e8RootNeg 2)⁆ = 0 at h0
    rw [hn2, hv2, hv0, bracket_g2_g2, ← lie_skew, map_neg, neg_eq_zero] at h0
    exact h15 (congrArg projG2 h0)
  · intro h0
    change ⁅e8RootVec 3, e8RootVec (e8RootNeg 3)⁆ = 0 at h0
    rw [hn3, hv3, hv5, bracket_g2_g2] at h0
    exact h712 (congrArg projG2 h0)
  · intro h0
    change ⁅e8RootVec 4, e8RootVec (e8RootNeg 4)⁆ = 0 at h0
    rw [hn4, hv4, hv1, bracket_g2_g2, ← lie_skew, map_neg, neg_eq_zero] at h0
    exact h211 (congrArg projG2 h0)
  · intro h0
    change ⁅e8RootVec 5, e8RootVec (e8RootNeg 5)⁆ = 0 at h0
    rw [hn5, hv5, hv3, bracket_g2_g2, ← lie_skew, map_neg, neg_eq_zero] at h0
    exact h712 (congrArg projG2 h0)

private theorem traceBilin_h3DiagZero₁_self :
    traceBilin h3DiagZero₁.1 h3DiagZero₁.1 = 2 := by
  simp [traceBilin, h3DiagZero₁_coe, H3Zorn.sub_readback, h3_diag₁, h3_diag₂,
    ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.trace,
    ZornVectorMatrix.sub, ZornVectorMatrix.neg, ZornVectorMatrix.zero, ZornVec3.dot]
  norm_num

private theorem traceBilin_h3DiagZero₁_two :
    traceBilin h3DiagZero₁.1 h3DiagZero₂.1 = -1 := by
  simp [traceBilin, h3DiagZero₁_coe, h3DiagZero₂_coe, H3Zorn.sub_readback,
    h3_diag₁, h3_diag₂, h3_diag₃, ZornVectorMatrix.conj, ZornVectorMatrix.mul,
    ZornVectorMatrix.trace, ZornVectorMatrix.sub, ZornVectorMatrix.neg,
    ZornVectorMatrix.zero, ZornVec3.dot]

private theorem traceBilin_h3DiagZero₂_self :
    traceBilin h3DiagZero₂.1 h3DiagZero₂.1 = 2 := by
  simp [traceBilin, h3DiagZero₂_coe, H3Zorn.sub_readback, h3_diag₂, h3_diag₃,
    ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.trace,
    ZornVectorMatrix.sub, ZornVectorMatrix.neg, ZornVectorMatrix.zero, ZornVec3.dot]
  norm_num

private theorem projG2_sector2_bracket (i s : Fin 3) :
    projG2 ⁅sector2UVec i s, sector2VVec i s⁆ =
      ⁅g2Inner zornE0 (zornU i), g2Inner zornE0 (zornV i)⁆ -
        (8 : ℝ) • g2Inner (zornU i) (zornV i) := by
  have ht11 := traceBilin_h3DiagZero₁_self
  have ht12 := traceBilin_h3DiagZero₁_two
  have ht21 : traceBilin h3DiagZero₂.1 h3DiagZero₁.1 = -1 := by
    rw [traceBilin_symm, ht12]
  have ht22 := traceBilin_h3DiagZero₂_self
  have hpg : ∀ D : G2DerivationCarrier, projG2 (embedG2 D) = D := fun _ => rfl
  have hpf : ∀ D : F4DerivationCarrier, projG2 (embedF4 D) = 0 := fun _ => rfl
  have hpt : ∀ a x, projG2 (embedTensor a x) = 0 := fun _ _ => rfl
  fin_cases s <;>
    · dsimp only [sector2UVec, sector2VVec]
      simp only [add_lie, sub_lie, lie_add, lie_sub, lie_smul, smul_lie,
        bracket_g2_g2, bracket_g2_tensor, bracket_tensor_g2, bracket_tensor_tensor,
        map_add, map_sub, map_smul, map_neg, hpg, hpf, hpt, ht11, ht12, ht21, ht22,
        add_zero, zero_add, zero_sub]
      module

private theorem g2Inner_zornU_zornV_eval (i : Fin 3) :
    ((g2Inner (zornU i) (zornV i)).toFun (zornU i).1).v i = 2 := by
  have hst : ∀ (x y : splitOctonionTraceZero) (z : VZ),
      (g2Inner x y).toFun z = stanDerMap (R := ℝ) x.1 y.1 z := fun _ _ _ => rfl
  fin_cases i <;>
    · simp [hst, stanDerMap, L_map, R_map, zornU, zornV, ZornVectorMatrix.U,
        ZornVectorMatrix.V, ZornVectorMatrix.mul, ZornVectorMatrix.add,
        vz_sub_a, vz_sub_v, vz_sub_w, vz_sub_b, ZornVec3.dot, ZornVec3.cross,
        ZornVec3.basis]
      norm_num

private theorem g2Inner_zornU_zornV_ne_zero (i : Fin 3) :
    g2Inner (zornU i) (zornV i) ≠ 0 := by
  intro h0
  have hz0 : ∀ (X : VZ) (k : Fin 3), ((0 : VDer).toFun X).v k = 0 := fun _ _ => rfl
  have hv := congrArg (fun D : VDer => (D.toFun (zornU i).1).v i) h0
  rw [g2Inner_zornU_zornV_eval i, hz0] at hv
  norm_num at hv

private theorem sector2_bracket_neg_ne_zero (i s : Fin 3) :
    ⁅sector2UVec i s, sector2VVec i s⁆ ≠ 0 := by
  intro h0
  have hpg := congrArg projG2 h0
  rw [projG2_sector2_bracket i s, map_zero] at hpg
  have hv := congrArg (fun D : VDer => (D.toFun (zornU i).1).v i) hpg
  have hz0 : ∀ (X : VZ) (k : Fin 3), ((0 : VDer).toFun X).v k = 0 := fun _ _ => rfl
  have hbr : ∀ (D₁ D₂ : VDer) (X : VZ), (⁅D₁, D₂⁆).toFun X = D₁ (D₂ X) - D₂ (D₁ X) :=
    fun _ _ _ => rfl
  have hst : ∀ (x y : splitOctonionTraceZero) (z : VZ),
      (g2Inner x y).toFun z = stanDerMap (R := ℝ) x.1 y.1 z := fun _ _ _ => rfl
  have hsub : ∀ (D₁ D₂ : VDer) (X : VZ), (D₁ - D₂).toFun X = D₁ X - D₂ X := fun _ _ _ => rfl
  have hsmv : ∀ (c : ℝ) (D : VDer) (X : VZ) (k : Fin 3),
      ((c • D).toFun X).v k = c * (D.toFun X).v k := fun _ _ _ _ => rfl
  rw [hsub, vz_sub_v, hsmv, g2Inner_zornU_zornV_eval i, hz0] at hv
  fin_cases i <;>
    · simp [hbr, vz_sub_v, hst, stanDerMap, L_map, R_map, zornE0, zornU, zornV,
        ZornVectorMatrix.diagonal, ZornVectorMatrix.U, ZornVectorMatrix.V,
        ZornVectorMatrix.mul, ZornVectorMatrix.add,
        vz_sub_a, vz_sub_w, vz_sub_b, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis] at hv
      norm_num at hv

private def sector3NegCheck (k : Fin 24) : Bool :=
  let r : Fin 240 := ⟨24 + k.val, by omega⟩
  let rn := e8RootNeg r
  if _ : 24 ≤ rn.val ∧ rn.val < 48 then
    !sparseZeroCheck (sparseComm (f4RootSparse ⟨k.val, by omega⟩)
      (f4RootSparse ⟨rn.val - 24, by omega⟩))
  else false

private theorem sector3_neg_check (k : Fin 24) : sector3NegCheck k = true := by
  have hchk : (List.finRange 24).all sector3NegCheck = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  exact hchk k

private theorem sector3_bracket_neg_ne_zero (k : Fin 24) :
    ⁅e8RootVec ⟨24 + k.val, by omega⟩, e8RootVec (e8RootNeg ⟨24 + k.val, by omega⟩)⁆ ≠ 0 := by
  have hchk := sector3_neg_check k
  dsimp only [sector3NegCheck] at hchk
  split_ifs at hchk with hrange
  obtain ⟨hn24, hn48⟩ := hrange
  simp only [Bool.not_eq_true'] at hchk
  have hr1 : e8RootVec ⟨24 + k.val, by omega⟩ = embedF4 (f4RootVec ⟨k.val, by omega⟩) := by
    dsimp only [e8RootVec]
    split_ifs <;> try omega
    exact congrArg (fun j : Fin 48 => embedF4 (f4RootVec j)) (Fin.ext (by dsimp; omega))
  have hr2 : e8RootVec (e8RootNeg ⟨24 + k.val, by omega⟩) =
      embedF4 (f4RootVec ⟨(e8RootNeg ⟨24 + k.val, by omega⟩).val - 24, by omega⟩) := by
    dsimp only [e8RootVec]
    split_ifs <;> try omega
    rfl
  have hpf_id : ∀ D : F4DerivationCarrier, projF4 (embedF4 D) = D := fun _ => rfl
  intro h0
  have hpf := congrArg projF4 h0
  rw [hr1, hr2, bracket_f4_f4, hpf_id, map_zero] at hpf
  have hm := congrArg (fun X : F4DerivationCarrier =>
    h3zornToMatrix (X.1 : Module.End ℝ (H3Zorn ℝ))) hpf
  change h3zornToMatrix (⁅f4RootVec ⟨k.val, by omega⟩,
    f4RootVec ⟨(e8RootNeg ⟨24 + k.val, by omega⟩).val - 24, by omega⟩⁆ :
      Module.End ℝ (H3Zorn ℝ)) = _ at hm
  rw [h3zornToMatrix_f4_lie, h3zornToMatrix_f4RootVec, h3zornToMatrix_f4RootVec,
    ZeroMemClass.coe_zero, map_zero] at hm
  have hcomm : (sparseToMat (f4RootSparse ⟨k.val, by omega⟩)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (f4RootSparse ⟨(e8RootNeg ⟨24 + k.val, by omega⟩).val - 24, by omega⟩)).map
          Int.cast -
      (sparseToMat (f4RootSparse ⟨(e8RootNeg ⟨24 + k.val, by omega⟩).val - 24, by omega⟩)).map
          Int.cast *
        (sparseToMat (f4RootSparse ⟨k.val, by omega⟩)).map Int.cast =
      (sparseToMat (sparseComm (f4RootSparse ⟨k.val, by omega⟩)
        (f4RootSparse ⟨(e8RootNeg ⟨24 + k.val, by omega⟩).val - 24, by omega⟩))).map
          Int.cast := by
    rw [sparseToMat_comm]
    ext a b
    simp [Matrix.mul_apply]
  rw [hcomm] at hm
  exact sparseToMat_ne_zero_of_not_sparseZeroCheck hchk hm

private def sector4NegCheck (m : Fin 48) : Bool :=
  let r : Fin 240 := ⟨48 + m.val, by omega⟩
  let rn := e8RootNeg r
  if _ : 48 ≤ rn.val ∧ rn.val < 96 then
    let k₁ : Fin 24 := ⟨m.val / 2, by omega⟩
    let sgn₁ : ℤ := if m.val % 2 = 0 then 1 else -1
    let k₂ : Fin 24 := ⟨(rn.val - 48) / 2, by omega⟩
    let sgn₂ : ℤ := if (rn.val - 48) % 2 = 0 then 1 else -1
    !sparseZeroCheck (sparseAdd
      (sparseComm (f4RootSparse ⟨24 + k₁.val, by omega⟩) (f4RootSparse ⟨24 + k₂.val, by omega⟩))
      (sparseSmul (sgn₁ * sgn₂)
        (sparseComm (twoLData ⟨3 + k₁.val, by omega⟩) (twoLData ⟨3 + k₂.val, by omega⟩))))
  else false

private theorem sector4_neg_block0 :
    (List.finRange 24).all (fun m => sector4NegCheck ⟨m.val, by omega⟩) = true := by
  decide

private theorem sector4_neg_block1 :
    (List.finRange 24).all (fun m => sector4NegCheck ⟨24 + m.val, by omega⟩) = true := by
  decide

private theorem sector4_neg_check (m : Fin 48) : sector4NegCheck m = true := by
  by_cases h24 : m.val < 24
  · have h0 := sector4_neg_block0
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at h0
    simpa [show (⟨(⟨m.val, h24⟩ : Fin 24).val, by omega⟩ : Fin 48) = m from Fin.ext rfl] using
      h0 ⟨m.val, h24⟩
  · have hm : m.val - 24 < 24 := by omega
    have h1 := sector4_neg_block1
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at h1
    simpa [show (⟨24 + (⟨m.val - 24, hm⟩ : Fin 24).val, by omega⟩ : Fin 48) = m from
      Fin.ext (by dsimp; omega)] using h1 ⟨m.val - 24, hm⟩

private theorem projF4_sector4_bracket (k₁ k₂ : Fin 24) (sgn₁ sgn₂ : ℤ) :
    projF4 ⁅sector4Vec k₁ sgn₁, sector4Vec k₂ sgn₂⁆ =
      ⁅f4RootVec ⟨24 + k₁.val, by omega⟩, f4RootVec ⟨24 + k₂.val, by omega⟩⁆ +
        ((sgn₁ * sgn₂ : ℤ) : ℝ) • ((4 : ℝ) • f4Inner (h3TraceZeroOff k₁) (h3TraceZeroOff k₂)) := by
  have hpf : ∀ D : F4DerivationCarrier, projF4 (embedF4 D) = D := fun _ => rfl
  have hpg : ∀ D : G2DerivationCarrier, projF4 (embedG2 D) = 0 := fun _ => rfl
  have hpt : ∀ a x, projF4 (embedTensor a x) = 0 := fun _ _ => rfl
  dsimp only [sector4Vec]
  simp only [add_lie, lie_add, lie_smul, smul_lie, bracket_f4_f4, bracket_f4_tensor,
    bracket_tensor_f4, bracket_tensor_tensor, map_add, map_smul, map_neg, hpf, hpg, hpt,
    zornBilin_zornE0_self, smul_zero, add_zero, zero_add, neg_zero, smul_smul]
  congr 2
  push_cast
  ring

private theorem sector4_bracket_neg_ne_zero (m : Fin 48) :
    ⁅e8RootVec ⟨48 + m.val, by omega⟩, e8RootVec (e8RootNeg ⟨48 + m.val, by omega⟩)⁆ ≠ 0 := by
  let r : Fin 240 := ⟨48 + m.val, by omega⟩
  have hchk := sector4_neg_check m
  dsimp only [sector4NegCheck] at hchk
  have hrange : 48 ≤ (e8RootNeg r).val ∧ (e8RootNeg r).val < 96 := by
    by_contra hno
    rw [dite_eq_right_of_eq_false (eq_false hno)] at hchk
    exact Bool.false_ne_true hchk
  rw [dite_eq_left_of_eq_true (eq_true hrange), Bool.not_eq_true'] at hchk
  obtain ⟨hn48, hn96⟩ := hrange
  set rn := e8RootNeg r
  let k₁ : Fin 24 := ⟨m.val / 2, by omega⟩
  let sgn₁ : ℤ := if m.val % 2 = 0 then 1 else -1
  let k₂ : Fin 24 := ⟨(rn.val - 48) / 2, by omega⟩
  let sgn₂ : ℤ := if (rn.val - 48) % 2 = 0 then 1 else -1
  have hr_val : r.val = 48 + m.val := rfl
  have hr1 : e8RootVec r = sector4Vec k₁ sgn₁ := by
    have hlt6 : ¬ r.val < 6 := by omega
    have hlt15 : ¬ r.val < 15 := by omega
    have hlt24 : ¬ r.val < 24 := by omega
    have hlt48 : ¬ r.val < 48 := by omega
    have hlt96 : r.val < 96 := by omega
    simp only [e8RootVec, hlt6, hlt15, hlt24, hlt48, hlt96, ↓reduceDIte]
    simp only [hr_val, Nat.add_sub_cancel_left]
    rfl
  have hr2 : e8RootVec rn = sector4Vec k₂ sgn₂ := by
    have hlt6 : ¬ rn.val < 6 := by omega
    have hlt15 : ¬ rn.val < 15 := by omega
    have hlt24 : ¬ rn.val < 24 := by omega
    have hlt48 : ¬ rn.val < 48 := by omega
    have hlt96 : rn.val < 96 := hn96
    simp only [e8RootVec, hlt6, hlt15, hlt24, hlt48, hlt96, ↓reduceDIte]
    rfl
  intro h0
  have hpf := congrArg projF4 h0
  change projF4 ⁅e8RootVec r, e8RootVec rn⁆ = 0 at hpf
  rw [hr1, hr2, projF4_sector4_bracket] at hpf
  have hm := congrArg (fun X : F4DerivationCarrier =>
    h3zornToMatrix (X.1 : Module.End ℝ (H3Zorn ℝ))) hpf
  rw [ZeroMemClass.coe_zero, map_zero, Submodule.coe_add, map_add, SetLike.val_smul,
    map_smul, SetLike.val_smul] at hm
  have hlie : h3zornToMatrix ((⁅f4RootVec ⟨24 + k₁.val, by omega⟩,
      f4RootVec ⟨24 + k₂.val, by omega⟩⁆ : F4DerivationCarrier).1 : Module.End ℝ (H3Zorn ℝ)) =
      h3zornToMatrix (f4RootVec ⟨24 + k₁.val, by omega⟩ : Module.End ℝ (H3Zorn ℝ)) *
        h3zornToMatrix (f4RootVec ⟨24 + k₂.val, by omega⟩ : Module.End ℝ (H3Zorn ℝ)) -
      h3zornToMatrix (f4RootVec ⟨24 + k₂.val, by omega⟩ : Module.End ℝ (H3Zorn ℝ)) *
        h3zornToMatrix (f4RootVec ⟨24 + k₁.val, by omega⟩ : Module.End ℝ (H3Zorn ℝ)) :=
    h3zornToMatrix_f4_lie _ _
  rw [hlie, h3zornToMatrix_f4RootVec, h3zornToMatrix_f4RootVec,
    h3zornToMatrix_four_f4Inner (h3TraceZeroOff k₁) (h3TraceZeroOff k₂)
      (twoLData ⟨3 + k₁.val, by omega⟩) (twoLData ⟨3 + k₂.val, by omega⟩)
      (by simpa [h3TraceZeroOff_coe] using
        h3zornToMatrix_two_jordanLmul_basis ⟨3 + k₁.val, by omega⟩)
      (by simpa [h3TraceZeroOff_coe] using
        h3zornToMatrix_two_jordanLmul_basis ⟨3 + k₂.val, by omega⟩)]
    at hm
  have hmat :
      ((sparseToMat (f4RootSparse ⟨24 + k₁.val, by omega⟩)).map (Int.cast : ℤ → ℝ) *
          (sparseToMat (f4RootSparse ⟨24 + k₂.val, by omega⟩)).map Int.cast -
        (sparseToMat (f4RootSparse ⟨24 + k₂.val, by omega⟩)).map Int.cast *
          (sparseToMat (f4RootSparse ⟨24 + k₁.val, by omega⟩)).map Int.cast) +
        ((sgn₁ * sgn₂ : ℤ) : ℝ) •
          (sparseToMat (sparseComm (twoLData ⟨3 + k₁.val, by omega⟩)
            (twoLData ⟨3 + k₂.val, by omega⟩))).map (Int.cast : ℤ → ℝ) =
      (sparseToMat (sparseAdd
        (sparseComm (f4RootSparse ⟨24 + k₁.val, by omega⟩) (f4RootSparse ⟨24 + k₂.val, by omega⟩))
        (sparseSmul (sgn₁ * sgn₂) (sparseComm (twoLData ⟨3 + k₁.val, by omega⟩)
          (twoLData ⟨3 + k₂.val, by omega⟩))))).map Int.cast := by
    rw [sparseToMat_add, sparseToMat_smul, sparseToMat_comm, sparseToMat_comm]
    ext a b
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.map_apply, smul_eq_mul, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_sum]
  rw [hmat] at hm
  exact sparseToMat_ne_zero_of_not_sparseZeroCheck hchk hm

private def e8ZornDualIdx (m : Fin 8) : Fin 8 :=
  match m.val with
  | 0 => 7 | 1 => 4 | 2 => 5 | 3 => 6 | 4 => 1 | 5 => 2 | 6 => 3 | _ => 0

private theorem zornBilinInt_e8ZornDualIdx_ne_zero (m : Fin 8) :
    zornBilinInt m (e8ZornDualIdx m) ≠ 0 := by
  fin_cases m <;> decide

private theorem traceBilin_h3TraceZeroOff_zornDual_ne_zero (b : Fin 3) (m : Fin 8) :
    traceBilin (h3TraceZeroOff ⟨8 * b.val + m.val, by omega⟩).1
      (h3TraceZeroOff ⟨8 * b.val + (e8ZornDualIdx m).val, by omega⟩).1 ≠ 0 := by
  have hz0 : (ZornVectorMatrix.mul (0 : VZ) (ZornVectorMatrix.conj (0 : VZ))).trace = 0 := by
    simp [ZornVectorMatrix.mul, ZornVectorMatrix.conj, ZornVectorMatrix.trace,
      ZornVectorMatrix.zero, ZornVec3.dot]
  have hne := zornBilinInt_e8ZornDualIdx_ne_zero m
  fin_cases b
  · have h1 : (h3TraceZeroOff ⟨8 * 0 + m.val, by omega⟩ : H3Zorn ℝ) =
        InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12 (zorn_basis m) := by
      simpa [h3TraceZeroOff_coe] using h3ZornBasis_12 m
    have h2 : (h3TraceZeroOff ⟨8 * 0 + (e8ZornDualIdx m).val, by omega⟩ : H3Zorn ℝ) =
        InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12
          (zorn_basis (e8ZornDualIdx m)) := by
      simpa [h3TraceZeroOff_coe] using h3ZornBasis_12 (e8ZornDualIdx m)
    change traceBilin (h3TraceZeroOff ⟨8 * 0 + m.val, by omega⟩ : H3Zorn ℝ)
      (h3TraceZeroOff ⟨8 * 0 + (e8ZornDualIdx m).val, by omega⟩ : H3Zorn ℝ) ≠ 0
    rw [h1, h2]
    dsimp only [traceBilin, InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12]
    rw [hz0]
    simp only [zero_mul, add_zero, zero_add]
    change zornBilin (zorn_basis m) (zorn_basis (e8ZornDualIdx m)) ≠ 0
    rw [zornBilin_zorn_basis]
    exact Int.cast_ne_zero.mpr hne
  · have hm1 : 11 + m.val = 3 + (8 * 1 + m.val) := by omega
    have hm2 : 11 + (e8ZornDualIdx m).val = 3 + (8 * 1 + (e8ZornDualIdx m).val) := by omega
    have h1 : (h3TraceZeroOff ⟨8 * 1 + m.val, by omega⟩ : H3Zorn ℝ) =
        embedJ23 (zorn_basis m) := by
      simpa [h3TraceZeroOff_coe, hm1] using h3ZornBasis_23 m
    have h2 : (h3TraceZeroOff ⟨8 * 1 + (e8ZornDualIdx m).val, by omega⟩ : H3Zorn ℝ) =
        embedJ23 (zorn_basis (e8ZornDualIdx m)) := by
      simpa [h3TraceZeroOff_coe, hm2] using h3ZornBasis_23 (e8ZornDualIdx m)
    change traceBilin (h3TraceZeroOff ⟨8 * 1 + m.val, by omega⟩ : H3Zorn ℝ)
      (h3TraceZeroOff ⟨8 * 1 + (e8ZornDualIdx m).val, by omega⟩ : H3Zorn ℝ) ≠ 0
    rw [h1, h2]
    dsimp only [traceBilin, embedJ23]
    rw [hz0]
    simp only [zero_mul, zero_add, add_zero]
    change zornBilin (zorn_basis m) (zorn_basis (e8ZornDualIdx m)) ≠ 0
    rw [zornBilin_zorn_basis]
    exact Int.cast_ne_zero.mpr hne
  · have hm1 : 19 + m.val = 3 + (8 * 2 + m.val) := by omega
    have hm2 : 19 + (e8ZornDualIdx m).val = 3 + (8 * 2 + (e8ZornDualIdx m).val) := by omega
    have h1 : (h3TraceZeroOff ⟨8 * 2 + m.val, by omega⟩ : H3Zorn ℝ) =
        embedJ31 (zorn_basis m) := by
      simpa [h3TraceZeroOff_coe, hm1] using h3ZornBasis_31 m
    have h2 : (h3TraceZeroOff ⟨8 * 2 + (e8ZornDualIdx m).val, by omega⟩ : H3Zorn ℝ) =
        embedJ31 (zorn_basis (e8ZornDualIdx m)) := by
      simpa [h3TraceZeroOff_coe, hm2] using h3ZornBasis_31 (e8ZornDualIdx m)
    change traceBilin (h3TraceZeroOff ⟨8 * 2 + m.val, by omega⟩ : H3Zorn ℝ)
      (h3TraceZeroOff ⟨8 * 2 + (e8ZornDualIdx m).val, by omega⟩ : H3Zorn ℝ) ≠ 0
    rw [h1, h2]
    dsimp only [traceBilin, embedJ31]
    rw [hz0]
    simp only [zero_mul, zero_add]
    change zornBilin (zorn_basis m) (zorn_basis (e8ZornDualIdx m)) ≠ 0
    rw [zornBilin_zorn_basis]
    exact Int.cast_ne_zero.mpr hne

private def sector5NegCheck (n : Fin 72) : Bool :=
  let r : Fin 240 := ⟨96 + n.val, by omega⟩
  let rn := e8RootNeg r
  if _ : 168 ≤ rn.val then
    ((rn.val - 168) / 24 == n.val / 24) &&
      ((rn.val - 168) % 24 / 8 == (n.val % 24) / 8) &&
      ((rn.val - 168) % 24 % 8 == (e8ZornDualIdx ⟨(n.val % 24) % 8, by omega⟩).val)
  else false

private theorem sector5_neg_block0 :
    (List.finRange 24).all (fun m => sector5NegCheck ⟨m.val, by omega⟩) = true := by
  decide

private theorem sector5_neg_block1 :
    (List.finRange 24).all (fun m => sector5NegCheck ⟨24 + m.val, by omega⟩) = true := by
  decide

private theorem sector5_neg_block2 :
    (List.finRange 24).all (fun m => sector5NegCheck ⟨48 + m.val, by omega⟩) = true := by
  decide

private theorem sector5_neg_check (n : Fin 72) : sector5NegCheck n = true := by
  by_cases h24 : n.val < 24
  · have h0 := sector5_neg_block0
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at h0
    simpa [show (⟨(⟨n.val, h24⟩ : Fin 24).val, by omega⟩ : Fin 72) = n from Fin.ext rfl] using
      h0 ⟨n.val, h24⟩
  · by_cases h48 : n.val < 48
    · have hm : n.val - 24 < 24 := by omega
      have h1 := sector5_neg_block1
      simp only [List.all_eq_true, List.mem_finRange, true_implies] at h1
      simpa [show (⟨24 + (⟨n.val - 24, hm⟩ : Fin 24).val, by omega⟩ : Fin 72) = n from
        Fin.ext (by dsimp; omega)] using h1 ⟨n.val - 24, hm⟩
    · have hm : n.val - 48 < 24 := by omega
      have h2 := sector5_neg_block2
      simp only [List.all_eq_true, List.mem_finRange, true_implies] at h2
      simpa [show (⟨48 + (⟨n.val - 48, hm⟩ : Fin 24).val, by omega⟩ : Fin 72) = n from
        Fin.ext (by dsimp; omega)] using h2 ⟨n.val - 48, hm⟩

private theorem sector5_bracket_neg_ne_zero (n : Fin 72) :
    ⁅e8RootVec ⟨96 + n.val, by omega⟩, e8RootVec (e8RootNeg ⟨96 + n.val, by omega⟩)⁆ ≠ 0 := by
  let r : Fin 240 := ⟨96 + n.val, by omega⟩
  have hchk := sector5_neg_check n
  dsimp only [sector5NegCheck] at hchk
  split_ifs at hchk with hn168
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  rcases hchk with ⟨⟨hi, hb⟩, hm⟩
  set rn := e8RootNeg r
  let i : Fin 3 := ⟨n.val / 24, by omega⟩
  let b : Fin 3 := ⟨(n.val % 24) / 8, by omega⟩
  let m : Fin 8 := ⟨(n.val % 24) % 8, by omega⟩
  have hr_val : r.val = 96 + n.val := rfl
  have hi1 : (⟨(r.val - 96) / 24, by omega⟩ : Fin 3) = i :=
    Fin.ext (by dsimp [i]; rw [hr_val]; omega)
  have hk1 : (⟨(r.val - 96) % 24, by omega⟩ : Fin 24) = ⟨8 * b.val + m.val, by omega⟩ := by
    apply Fin.ext
    dsimp [b, m]
    rw [hr_val]
    omega
  have hi2 : (⟨(rn.val - 168) / 24, by omega⟩ : Fin 3) = i := Fin.ext hi
  have hk2 : (⟨(rn.val - 168) % 24, by omega⟩ : Fin 24) =
      ⟨8 * b.val + (e8ZornDualIdx m).val, by omega⟩ := by
    apply Fin.ext
    dsimp [b, m]
    omega
  have hr1 : e8RootVec r =
      embedTensor (zornU i) (h3TraceZeroOff ⟨8 * b.val + m.val, by omega⟩) := by
    have hlt6 : ¬ r.val < 6 := by omega
    have hlt15 : ¬ r.val < 15 := by omega
    have hlt24 : ¬ r.val < 24 := by omega
    have hlt48 : ¬ r.val < 48 := by omega
    have hlt96 : ¬ r.val < 96 := by omega
    have hlt168 : r.val < 168 := by omega
    simp only [e8RootVec, hlt6, hlt15, hlt24, hlt48, hlt96, hlt168, ↓reduceDIte, hi1, hk1]
  have hr2 : e8RootVec rn =
      embedTensor (zornV i) (h3TraceZeroOff ⟨8 * b.val + (e8ZornDualIdx m).val, by omega⟩) := by
    have hlt6 : ¬ rn.val < 6 := by omega
    have hlt15 : ¬ rn.val < 15 := by omega
    have hlt24 : ¬ rn.val < 24 := by omega
    have hlt48 : ¬ rn.val < 48 := by omega
    have hlt96 : ¬ rn.val < 96 := by omega
    have hlt168 : ¬ rn.val < 168 := by omega
    simp only [e8RootVec, hlt6, hlt15, hlt24, hlt48, hlt96, hlt168, ↓reduceDIte, hi2, hk2]
  have hpg_id : ∀ D : G2DerivationCarrier, projG2 (embedG2 D) = D := fun _ => rfl
  have hpf_id : ∀ D : F4DerivationCarrier, projG2 (embedF4 D) = 0 := fun _ => rfl
  have hpt_id : ∀ a x, projG2 (embedTensor a x) = 0 := fun _ _ => rfl
  intro h0
  have hpg := congrArg projG2 h0
  change projG2 ⁅e8RootVec r, e8RootVec rn⁆ = 0 at hpg
  rw [hr1, hr2, bracket_tensor_tensor, map_add, map_add, hpg_id, hpt_id, hpf_id,
    add_zero, add_zero] at hpg
  have hsc := (smul_eq_zero.mp hpg).resolve_right (g2Inner_zornU_zornV_ne_zero i)
  have htb : traceBilin (h3TraceZeroOff ⟨8 * b.val + m.val, by omega⟩).1
      (h3TraceZeroOff ⟨8 * b.val + (e8ZornDualIdx m).val, by omega⟩).1 = 0 :=
    (mul_eq_zero.mp hsc).resolve_left (by norm_num)
  exact traceBilin_h3TraceZeroOff_zornDual_ne_zero b m htb

private theorem sector5_neg_ge168_lt (n : Fin 72) :
    96 ≤ (e8RootNeg ⟨168 + n.val, by omega⟩).val ∧
      (e8RootNeg ⟨168 + n.val, by omega⟩).val < 168 := by
  have hb0 : (List.finRange 24).all (fun m =>
      decide (96 ≤ (e8RootNeg ⟨168 + m.val, by omega⟩).val) &&
      decide ((e8RootNeg ⟨168 + m.val, by omega⟩).val < 168)) = true := by
    decide
  have hb1 : (List.finRange 24).all (fun m =>
      decide (96 ≤ (e8RootNeg ⟨192 + m.val, by omega⟩).val) &&
      decide ((e8RootNeg ⟨192 + m.val, by omega⟩).val < 168)) = true := by
    decide
  have hb2 : (List.finRange 24).all (fun m =>
      decide (96 ≤ (e8RootNeg ⟨216 + m.val, by omega⟩).val) &&
      decide ((e8RootNeg ⟨216 + m.val, by omega⟩).val < 168)) = true := by
    decide
  by_cases h24 : n.val < 24
  · have heq : (⟨168 + (⟨n.val, h24⟩ : Fin 24).val, by omega⟩ : Fin 240) =
        ⟨168 + n.val, by omega⟩ := Fin.ext rfl
    simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
      decide_eq_true_eq] at hb0
    simpa [heq] using hb0 ⟨n.val, h24⟩
  · by_cases h48 : n.val < 48
    · have hm : n.val - 24 < 24 := by omega
      have heq : (⟨192 + (⟨n.val - 24, hm⟩ : Fin 24).val, by omega⟩ : Fin 240) =
          ⟨168 + n.val, by omega⟩ := Fin.ext (by dsimp; omega)
      simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
        decide_eq_true_eq] at hb1
      simpa [heq] using hb1 ⟨n.val - 24, hm⟩
    · have hm : n.val - 48 < 24 := by omega
      have heq : (⟨216 + (⟨n.val - 48, hm⟩ : Fin 24).val, by omega⟩ : Fin 240) =
          ⟨168 + n.val, by omega⟩ := Fin.ext (by dsimp; omega)
      simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
        decide_eq_true_eq] at hb2
      simpa [heq] using hb2 ⟨n.val - 48, hm⟩

private theorem sector5_bracket_neg_ge168_ne_zero (n : Fin 72) :
    ⁅e8RootVec ⟨168 + n.val, by omega⟩, e8RootVec (e8RootNeg ⟨168 + n.val, by omega⟩)⁆ ≠ 0 := by
  let r : Fin 240 := ⟨168 + n.val, by omega⟩
  have hr_def : (⟨168 + n.val, by omega⟩ : Fin 240) = r := rfl
  obtain ⟨hn96, hn168⟩ := sector5_neg_ge168_lt n
  rw [hr_def] at hn96 hn168
  let m : Fin 72 := ⟨(e8RootNeg r).val - 96, by omega⟩
  have hm_eq : e8RootNeg r = ⟨96 + m.val, by omega⟩ := Fin.ext (by dsimp [m]; omega)
  have hm_neg : e8RootNeg ⟨96 + m.val, by omega⟩ = r := by
    rw [← hm_eq, e8RootNeg_involutive]
  intro h0
  have h0' : ⁅e8RootVec ⟨96 + m.val, by omega⟩, e8RootVec r⁆ = 0 := by
    change ⁅e8RootVec r, e8RootVec (e8RootNeg r)⁆ = 0 at h0
    rw [hm_eq, ← lie_skew, neg_eq_zero] at h0
    exact h0
  have hne := sector5_bracket_neg_ne_zero m
  rw [hm_neg] at hne
  exact hne h0'

private theorem sector5_bracket_neg_ge168_ne_zero_of (r : Fin 240) (n : Fin 72)
    (hr : r = ⟨168 + n.val, by omega⟩) :
    ⁅e8RootVec r, e8RootVec (e8RootNeg r)⁆ ≠ 0 := by
  subst hr
  exact sector5_bracket_neg_ge168_ne_zero n

private theorem sector2_neg_u (k : Fin 9) :
    e8RootNeg ⟨6 + k.val, by omega⟩ = ⟨15 + k.val, by omega⟩ := by
  fin_cases k <;> decide

private theorem sector2_neg_v (k : Fin 9) :
    e8RootNeg ⟨15 + k.val, by omega⟩ = ⟨6 + k.val, by omega⟩ := by
  fin_cases k <;> decide

/-- **Universal Opposite-Root Nonvanishing**: for every root `r : Fin 240` of `SplitE8Lie`,
the bracket `⁅e8RootVec r, e8RootVec (e8RootNeg r)⁆` is nonzero. -/
theorem e8RootVec_bracket_neg_ne_zero (r : Fin 240) :
    ⁅e8RootVec r, e8RootVec (e8RootNeg r)⁆ ≠ 0 := by
  by_cases h6 : r.val < 6
  · have hr_eq : (⟨(⟨r.val, h6⟩ : Fin 6).val, by omega⟩ : Fin 240) = r := Fin.ext rfl
    have h := sector1_bracket_neg_ne_zero ⟨r.val, h6⟩
    rwa [hr_eq] at h
  · by_cases h15 : r.val < 15
    · let k : Fin 9 := ⟨r.val - 6, by omega⟩
      have hr_eq : r = ⟨6 + k.val, by omega⟩ := Fin.ext (by dsimp [k]; omega)
      have hn : e8RootNeg r = ⟨15 + k.val, by omega⟩ := by
        have h := sector2_neg_u k
        rwa [← hr_eq] at h
      have hr1 : e8RootVec r =
          sector2UVec ⟨k.val / 3, by omega⟩ ⟨k.val % 3, by omega⟩ := by
        simp only [e8RootVec, h6, h15, ↓reduceDIte]
        rfl
      have hr2 : e8RootVec (e8RootNeg r) =
          sector2VVec ⟨k.val / 3, by omega⟩ ⟨k.val % 3, by omega⟩ := by
        rw [hn]
        have hlt6 : ¬ (15 + k.val < 6) := by omega
        have hlt15 : ¬ (15 + k.val < 15) := by omega
        have hlt24 : 15 + k.val < 24 := by omega
        simp only [e8RootVec, hlt6, hlt15, hlt24, ↓reduceDIte]
        congr 1 <;> exact Fin.ext (by dsimp; omega)
      rw [hr1, hr2]
      exact sector2_bracket_neg_ne_zero _ _
    · by_cases h24 : r.val < 24
      · let k : Fin 9 := ⟨r.val - 15, by omega⟩
        have hr_eq : r = ⟨15 + k.val, by omega⟩ := Fin.ext (by dsimp [k]; omega)
        have hn : e8RootNeg r = ⟨6 + k.val, by omega⟩ := by
          have h := sector2_neg_v k
          rwa [← hr_eq] at h
        have hr1 : e8RootVec r =
            sector2VVec ⟨k.val / 3, by omega⟩ ⟨k.val % 3, by omega⟩ := by
          simp only [e8RootVec, h6, h15, h24, ↓reduceDIte]
          rfl
        have hr2 : e8RootVec (e8RootNeg r) =
            sector2UVec ⟨k.val / 3, by omega⟩ ⟨k.val % 3, by omega⟩ := by
          rw [hn]
          have hlt6 : ¬ (6 + k.val < 6) := by omega
          have hlt15 : 6 + k.val < 15 := by omega
          simp only [e8RootVec, hlt6, hlt15, ↓reduceDIte]
          congr 1 <;> exact Fin.ext (by dsimp; omega)
        rw [hr1, hr2, ← lie_skew]
        exact neg_ne_zero.mpr (sector2_bracket_neg_ne_zero _ _)
      · by_cases h48 : r.val < 48
        · have hk : r.val - 24 < 24 := by omega
          have hr_eq : (⟨24 + (⟨r.val - 24, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
            Fin.ext (by dsimp; omega)
          have h := sector3_bracket_neg_ne_zero ⟨r.val - 24, hk⟩
          rwa [hr_eq] at h
        · by_cases h96 : r.val < 96
          · have hm : r.val - 48 < 48 := by omega
            have hr_eq : (⟨48 + (⟨r.val - 48, hm⟩ : Fin 48).val, by omega⟩ : Fin 240) = r :=
              Fin.ext (by dsimp; omega)
            have h := sector4_bracket_neg_ne_zero ⟨r.val - 48, hm⟩
            rwa [hr_eq] at h
          · by_cases h168 : r.val < 168
            · have hn : r.val - 96 < 72 := by omega
              have hr_eq : (⟨96 + (⟨r.val - 96, hn⟩ : Fin 72).val, by omega⟩ : Fin 240) = r :=
                Fin.ext (by dsimp; omega)
              have h := sector5_bracket_neg_ne_zero ⟨r.val - 96, hn⟩
              rwa [hr_eq] at h
            · have hn : r.val - 168 < 72 := by omega
              exact sector5_bracket_neg_ge168_ne_zero_of r ⟨r.val - 168, hn⟩
                (Fin.ext (by dsimp; omega))

end OppositeRootNonvanishing

/-! ## 2. `NoAbelianIdeal`, `HasTrivialRadical`, `IsKilling`, and Root Space 1-Dimensionality -/

section KillingAndNoAbelianIdeal

private theorem e8_cartan_transpose_mulVec_ne_zero {a : Fin 8 → ℝ}
    (ha : (∑ i : Fin 8, a i • e8SimpleH i) ≠ 0) :
    ∃ j : Fin 8, ∑ i : Fin 8, a i * (Tag.cartan .E8 i j : ℝ) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 := hcon 0; have h1 := hcon 1; have h2 := hcon 2; have h3 := hcon 3
  have h4 := hcon 4; have h5 := hcon 5; have h6 := hcon 6; have h7 := hcon 7
  have hcZ : ∀ i j : Fin 8, Tag.cartan .E8 i j =
      match i.val, j.val with
      | 0, 0 => 2 | 0, 2 => -1
      | 1, 1 => 2 | 1, 3 => -1
      | 2, 0 => -1 | 2, 2 => 2 | 2, 3 => -1
      | 3, 1 => -1 | 3, 2 => -1 | 3, 3 => 2 | 3, 4 => -1
      | 4, 3 => -1 | 4, 4 => 2 | 4, 5 => -1
      | 5, 4 => -1 | 5, 5 => 2 | 5, 6 => -1
      | 6, 5 => -1 | 6, 6 => 2 | 6, 7 => -1
      | 7, 6 => -1 | 7, 7 => 2
      | _, _ => 0 := by
    intro i j; fin_cases i <;> fin_cases j <;> decide
  simp only [Fin.sum_univ_eight, hcZ] at h0 h1 h2 h3 h4 h5 h6 h7
  norm_num [Fin.val] at h0 h1 h2 h3 h4 h5 h6 h7
  have ha0 : a 0 = 0 := by linarith
  have ha1 : a 1 = 0 := by linarith
  have ha2 : a 2 = 0 := by linarith
  have ha3 : a 3 = 0 := by linarith
  have ha4 : a 4 = 0 := by linarith
  have ha5 : a 5 = 0 := by linarith
  have ha6 : a 6 = 0 := by linarith
  have ha7 : a 7 = 0 := by linarith
  exact ha (Finset.sum_eq_zero fun i _ => by
    fin_cases i <;> simp [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7])

private theorem cartan_mem_abelian_ideal_eq_zero (I : LieIdeal ℝ SplitE8Lie) [IsLieAbelian I]
    (h : SplitE8Lie) (hh : h ∈ splitE8Cartan) (hI : h ∈ I) : h = 0 := by
  by_contra hne
  have hsp : h ∈ Submodule.span ℝ (Set.range e8SimpleH) := by
    change h ∈ splitE8Cartan.toSubmodule at hh
    rwa [← splitE8Cartan_eq_span_e8SimpleH]
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hsp
  obtain ⟨j, hj⟩ := e8_cartan_transpose_mulVec_ne_zero hne
  have hbr : ⁅∑ i : Fin 8, a i • e8SimpleH i, e8SimpleE j⁆ ∈ I := by
    rw [← lie_skew]
    exact I.neg_mem (I.lie_mem hI)
  have heq : ⁅∑ i : Fin 8, a i • e8SimpleH i, e8SimpleE j⁆ =
      (∑ i : Fin 8, a i * (Tag.cartan .E8 i j : ℝ)) • e8SimpleE j := by
    rw [sum_lie]
    simp only [smul_lie, e8Simple_bracket_HE, smul_smul, Finset.sum_smul]
  rw [heq] at hbr
  have hej : e8SimpleE j ∈ I := by
    have hs := I.smul_mem (∑ i : Fin 8, a i * (Tag.cartan .E8 i j : ℝ))⁻¹ hbr
    rw [smul_smul, inv_mul_cancel₀ hj, one_smul] at hs
    exact hs
  have hab : ⁅(⟨∑ i : Fin 8, a i • e8SimpleH i, hI⟩ : I), (⟨e8SimpleE j, hej⟩ : I)⁆ = 0 :=
    (inferInstance : IsLieAbelian I).trivial _ _
  have hab' : ⁅∑ i : Fin 8, a i • e8SimpleH i, e8SimpleE j⁆ = 0 :=
    congrArg Subtype.val hab
  rw [heq] at hab'
  have hzero := (smul_eq_zero.mp hab').resolve_left hj
  rw [e8SimpleE_eq_rootVec] at hzero
  exact e8RootVec_ne_zero (e8ESimpleIdx j) hzero

/-- `SplitE8Lie` has no nonzero abelian ideals. -/
theorem splitE8Lie_no_abelian_ideal (I : LieIdeal ℝ SplitE8Lie) [IsLieAbelian I] : I = ⊥ := by
  rw [eq_bot_iff]
  intro x hxI
  rw [LieSubmodule.mem_bot]
  have hrep := e8ChevalleyBasis.sum_repr x
  rw [Fintype.sum_sum_type] at hrep
  simp only [e8ChevalleyBasis_inl, e8ChevalleyBasis_inr] at hrep
  let hpart : SplitE8Lie := ∑ i : Fin 8, e8ChevalleyBasis.repr x (Sum.inl i) • e8SimpleH i
  have hhpart : hpart ∈ splitE8Cartan :=
    Submodule.sum_mem _ fun i _ => splitE8Cartan.smul_mem _ (e8SimpleH_mem_splitE8Cartan i)
  have hkill := e8_cartan_weight_kill_mem I.toSubmodule (fun a y hy => I.lie_mem hy)
    Finset.univ hpart hhpart (fun r => e8ChevalleyBasis.repr x (Sum.inr r))
    (by rw [hrep]; exact hxI)
  have hh0 : hpart = 0 := cartan_mem_abelian_ideal_eq_zero I hpart hhpart hkill.1
  have hr0 : ∀ r : Fin 240, e8ChevalleyBasis.repr x (Sum.inr r) = 0 := by
    intro r
    by_contra hcr
    have hrI : e8RootVec r ∈ I := by
      have hs := I.smul_mem (e8ChevalleyBasis.repr x (Sum.inr r))⁻¹
        (hkill.2 r (Finset.mem_univ r))
      rw [smul_smul, inv_mul_cancel₀ hcr, one_smul] at hs
      exact hs
    have hbrI : ⁅e8RootVec r, e8RootVec (e8RootNeg r)⁆ ∈ I := by
      rw [← lie_skew]
      exact I.neg_mem (I.lie_mem hrI)
    have hbrC : ⁅e8RootVec r, e8RootVec (e8RootNeg r)⁆ ∈ splitE8Cartan :=
      e8RootVec_opposite_bracket_mem_cartan (by rw [e8RootCoord_neg, add_neg_cancel])
    exact e8RootVec_bracket_neg_ne_zero r (cartan_mem_abelian_ideal_eq_zero I _ hbrC hbrI)
  have hsum0 : (∑ r : Fin 240, e8ChevalleyBasis.repr x (Sum.inr r) • e8RootVec r) = 0 :=
    Finset.sum_eq_zero fun r _ => by rw [hr0 r, zero_smul]
  have hh0' : (∑ i : Fin 8, e8ChevalleyBasis.repr x (Sum.inl i) • e8SimpleH i) = 0 := hh0
  rw [← hrep, hh0', hsum0, add_zero]

instance splitE8Lie_hasTrivialRadical : LieAlgebra.HasTrivialRadical ℝ SplitE8Lie :=
  (LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals ℝ SplitE8Lie).mpr
    splitE8Lie_no_abelian_ideal

instance splitE8Lie_isKilling : LieAlgebra.IsKilling ℝ SplitE8Lie := by
  have : IsNoetherian ℝ SplitE8Lie := (IsNoetherian.iff_fg).2 inferInstance
  exact inferInstance

theorem splitE8Lie_killingForm_nondegenerate : (killingForm ℝ SplitE8Lie).Nondegenerate :=
  LieAlgebra.IsKilling.killingForm_nondegenerate ℝ SplitE8Lie

theorem center_splitE8Lie_eq_bot : LieAlgebra.center ℝ SplitE8Lie = ⊥ :=
  le_antisymm (LieAlgebra.center_le_radical ℝ SplitE8Lie |>.trans (by simp)) bot_le

theorem finrank_splitE8Cartan_rootSpace_eq_one (α : splitE8Cartan.root) :
    Module.finrank ℝ (LieAlgebra.rootSpace splitE8Cartan α) = 1 :=
  LieAlgebra.IsKilling.finrank_rootSpace_eq_one α.1 (LieSubalgebra.isNonZero_coe_root α)

end KillingAndNoAbelianIdeal

/-! ## 3. Mathlib `E₈` `RootPairing`, `240` Roots, `Base`, and `CartanMatrix.E 8` -/

section E8RootSystem

/-- The Mathlib `RootPairing` of split `𝔈₈(8)` (`SplitE8Lie`) relative to `splitE8Cartan`. -/
noncomputable def splitE8RootSystem :
    RootPairing splitE8Cartan.root ℝ (Module.Dual ℝ splitE8Cartan) splitE8Cartan :=
  LieAlgebra.IsKilling.rootSystem splitE8Cartan

instance splitE8RootSystem_isRootSystem : splitE8RootSystem.IsRootSystem :=
  show (LieAlgebra.IsKilling.rootSystem splitE8Cartan).IsRootSystem from inferInstance

instance splitE8RootSystem_isCrystallographic : splitE8RootSystem.IsCrystallographic :=
  show (LieAlgebra.IsKilling.rootSystem splitE8Cartan).IsCrystallographic from inferInstance

instance splitE8RootSystem_isReduced : splitE8RootSystem.IsReduced :=
  show (LieAlgebra.IsKilling.rootSystem splitE8Cartan).IsReduced from inferInstance

/-- Package the `r`-th root weight `e8RootWeight r` as a Mathlib `LieModule.Weight`. -/
def e8MathlibWeight (r : Fin 240) :
    LieModule.Weight ℝ splitE8Cartan SplitE8Lie where
  toFun := e8RootWeight r
  genWeightSpace_ne_bot' := e8RootSpace_ne_bot r

/-- Package the `r`-th root weight as a nonzero root in `splitE8Cartan.root`. -/
def e8MathlibRoot (r : Fin 240) : splitE8Cartan.root :=
  ⟨e8MathlibWeight r, by
    simp only [LieSubalgebra.root, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h0
    apply e8RootWeight_ne_zero r
    ext H
    exact congrFun h0 H⟩

theorem e8MathlibRoot_injective : Function.Injective e8MathlibRoot := by
  intro r₁ r₂ h
  apply e8RootWeight_injective
  ext H
  exact congrFun (congrArg (fun x : splitE8Cartan.root => (x.1 : splitE8Cartan → ℝ)) h) H

theorem e8MathlibRoot_surjective : Function.Surjective e8MathlibRoot := by
  intro α
  let S : Set (splitE8Cartan → ℝ) :=
    insert 0 (Set.range (fun r : Fin 240 => (e8RootWeight r : splitE8Cartan → ℝ)))
  have hs : (⨆ ψ ∈ S, LieAlgebra.rootSpace splitE8Cartan ψ) = ⊤ := by
    rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.top_toSubmodule]
    simp only [LieSubmodule.iSup_toSubmodule]
    apply (Submodule.eq_top_iff_forall_basis_mem e8ChevalleyBasis).mpr
    rintro (i | r)
    · apply Submodule.mem_iSup_of_mem (0 : splitE8Cartan → ℝ)
      apply Submodule.mem_iSup_of_mem (Set.mem_insert 0 _)
      rw [e8ChevalleyBasis_inl]
      exact LieAlgebra.toLieSubmodule_le_rootSpace_zero ℝ SplitE8Lie splitE8Cartan
        (e8SimpleH_mem_splitE8Cartan i)
    · apply Submodule.mem_iSup_of_mem (e8RootWeight r : splitE8Cartan → ℝ)
      apply Submodule.mem_iSup_of_mem (Set.mem_insert_of_mem 0 (Set.mem_range_self r))
      rw [e8ChevalleyBasis_inr]
      exact e8RootVec_mem_rootSpace r
  have hmem : (α.1 : splitE8Cartan → ℝ) ∈ S :=
    (LieModule.iSupIndep_genWeightSpace ℝ splitE8Cartan SplitE8Lie).mem_of_biSup_eq_top
      hs α.1.genWeightSpace_ne_bot
  rcases hmem with h0 | ⟨r, hr⟩
  · exfalso
    exact (LieSubalgebra.isNonZero_coe_root α) h0
  · refine ⟨r, ?_⟩
    apply Subtype.ext
    ext H
    exact congrFun hr H

/-- Explicit bijection `Fin 240 ≃ splitE8Cartan.root`. -/
noncomputable def e8MathlibRootEquiv : Fin 240 ≃ splitE8Cartan.root :=
  Equiv.ofBijective e8MathlibRoot ⟨e8MathlibRoot_injective, e8MathlibRoot_surjective⟩

/-- Canonical bijection between `CFSGPort` `E₈` roots and Mathlib `splitE8Cartan.root`. -/
noncomputable def e8RootSystemEquiv :
    {v : Fin 8 → ℤ // IsRoot .E8 v} ≃ splitE8Cartan.root :=
  e8RootEquiv.symm.trans e8MathlibRootEquiv

theorem card_splitE8Cartan_root : Fintype.card splitE8Cartan.root = 240 := by
  rw [← Fintype.card_fin 240]
  exact (Fintype.card_congr e8MathlibRootEquiv).symm

theorem splitE8Cartan_root_card : splitE8Cartan.root.card = 240 := by
  rw [← Fintype.card_coe splitE8Cartan.root]
  exact card_splitE8Cartan_root

theorem e8RootWeight_simpleH (r : Fin 240) (i : Fin 8) :
    e8RootWeight r ⟨e8SimpleH i, e8SimpleH_mem_splitE8Cartan i⟩ = (e8RootEigenvalue i r : ℝ) := by
  apply smul_left_injective ℝ (e8RootVec_ne_zero r)
  dsimp only
  rw [← e8RootVec_bracket_cartan ⟨e8SimpleH i, e8SimpleH_mem_splitE8Cartan i⟩ r,
    ← e8RootVec_bracket_H i r]

/-- The simple-coroot basis `e8SimpleH` of `splitE8Cartan`. -/
noncomputable def e8SimpleHBasis : Module.Basis (Fin 8) ℝ splitE8Cartan :=
  let v : Fin 8 → splitE8Cartan := fun i => ⟨e8SimpleH i, e8SimpleH_mem_splitE8Cartan i⟩
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : ∑ i : Fin 8, c i • e8SimpleH i = 0 := by
      simpa [v] using congrArg (Subtype.val : splitE8Cartan → SplitE8Lie) hc
    exact Fintype.linearIndependent_iff.mp e8SimpleH_linearIndependent c hc'
  basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Fintype.card_fin, finrank_splitE8Cartan])

@[simp] theorem e8SimpleHBasis_apply (i : Fin 8) :
    (e8SimpleHBasis i : SplitE8Lie) = e8SimpleH i := by
  simp [e8SimpleHBasis]

private theorem e8RootCoord_fSimple (i : Fin 8) :
    e8RootCoord (e8FSimpleIdx i) = -e8RootCoord (e8ESimpleIdx i) := by
  have hchk : (List.finRange 8).all (fun i =>
      List.ofFn (e8RootCoord (e8FSimpleIdx i)) ==
        List.ofFn (-e8RootCoord (e8ESimpleIdx i))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
  exact List.ofFn_injective (hchk i)

private theorem e8RootCoord_sign_uniform (r : Fin 240) :
    (∀ i : Fin 8, 0 ≤ e8RootCoord r i) ∨ (∀ i : Fin 8, e8RootCoord r i ≤ 0) := by
  have hchk := forall_fin240_of_blocks
    (fun r => (List.finRange 8).all (fun i => decide (0 ≤ e8RootCoord r i)) ||
      (List.finRange 8).all (fun i => decide (e8RootCoord r i ≤ 0)))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) r
  simp only [Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq] at hchk
  exact hchk

private theorem e8RootWeight_eq_sum_simple (r : Fin 240) :
    e8RootWeight r =
      ∑ j : Fin 8, (e8RootCoord r j : ℝ) • e8RootWeight (e8ESimpleIdx j) := by
  apply e8SimpleHBasis.ext
  intro i
  rw [LinearMap.sum_apply]
  have he8 : (e8SimpleHBasis i : splitE8Cartan) = ⟨e8SimpleH i, e8SimpleH_mem_splitE8Cartan i⟩ :=
    Subtype.ext (e8SimpleHBasis_apply i)
  rw [he8, e8RootWeight_simpleH]
  simp_rw [LinearMap.smul_apply, smul_eq_mul, e8RootWeight_simpleH, e8RootEigenvalue_simpleE]
  rw [e8RootEigenvalue]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The 8 Bourbaki simple roots in `splitE8Cartan.root`. -/
def e8SimpleMathlibRoot (i : Fin 8) : splitE8Cartan.root :=
  e8MathlibRoot (e8ESimpleIdx i)

private theorem e8ESimpleIdx_injective : Function.Injective e8ESimpleIdx := by
  intro i j h
  have heq := congrArg (e8RootCoord ·) h
  have hi : e8RootCoord (e8ESimpleIdx i) i = 1 := by
    fin_cases i <;> decide
  have hj : ∀ a b : Fin 8, a ≠ b → e8RootCoord (e8ESimpleIdx a) b = 0 := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> first | contradiction | decide
  by_contra hne
  have h1 := congrFun heq i
  rw [hi, hj j i (Ne.symm hne)] at h1
  omega

private theorem e8SimpleMathlibRoot_injective : Function.Injective e8SimpleMathlibRoot :=
  e8MathlibRoot_injective.comp e8ESimpleIdx_injective

private theorem e8SimpleMathlibRoot_linearIndepOn :
    LinearIndepOn ℝ splitE8RootSystem.root (Set.range e8SimpleMathlibRoot) := by
  classical
  rw [linearIndepOn_iff'']
  intro s c hs_sub hsupp hsum i hi
  have hc0 : ∀ x : splitE8Cartan.root, x ∈ Set.range e8SimpleMathlibRoot → c x = 0 := by
    let a : Fin 8 → ℝ := fun j =>
      if e8SimpleMathlibRoot j ∈ s then c (e8SimpleMathlibRoot j) else 0
    have hsum8 : ∑ j : Fin 8, a j • e8RootWeight (e8ESimpleIdx j) = 0 := by
      have hconv : ∑ x ∈ s, c x • splitE8RootSystem.root x =
          ∑ x ∈ Finset.image e8SimpleMathlibRoot Finset.univ,
            (if x ∈ s then c x else 0) • splitE8RootSystem.root x := by
        simp_rw [ite_smul, zero_smul]
        rw [← Finset.sum_filter]
        refine Finset.sum_congr (by
          ext x
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨fun hx => ⟨hs_sub hx, hx⟩, fun h => h.2⟩) fun x _ => rfl
      rw [hconv, Finset.sum_image (fun x _ y _ hxy => e8SimpleMathlibRoot_injective hxy)] at hsum
      exact hsum
    have hzero : ∀ j : Fin 8, a j = 0 := by
      have hev : ∀ k : Fin 8, ∑ j : Fin 8, a j * (Tag.cartan .E8 j k : ℝ) = 0 := by
        intro k
        have hk := congrArg (fun f : Module.Dual ℝ splitE8Cartan =>
          f ⟨e8SimpleH k, e8SimpleH_mem_splitE8Cartan k⟩) hsum8
        rw [LinearMap.sum_apply, LinearMap.zero_apply] at hk
        simp only [LinearMap.smul_apply, smul_eq_mul, e8RootWeight_simpleH,
          e8RootEigenvalue_simpleE] at hk
        have hsymm : ∀ j : Fin 8, Tag.cartan .E8 k j = Tag.cartan .E8 j k := by
          intro j; fin_cases k <;> fin_cases j <;> decide
        simpa [hsymm] using hk
      have hne0 : (∑ j : Fin 8, a j • e8SimpleH j) = 0 := by
        by_contra hcon
        obtain ⟨k, hk⟩ := e8_cartan_transpose_mulVec_ne_zero hcon
        exact hk (hev k)
      exact Fintype.linearIndependent_iff.mp e8SimpleH_linearIndependent a hne0
    intro x hx
    rcases hx with ⟨j, rfl⟩
    by_cases hjs : e8SimpleMathlibRoot j ∈ s
    · have hj0 := hzero j
      simpa [a, hjs] using hj0
    · exact hsupp (e8SimpleMathlibRoot j) hjs
  exact hc0 i (hs_sub hi)

private theorem e8SimpleMathlibRoot_mem_or_neg_mem (α : splitE8Cartan.root) :
    splitE8RootSystem.root α ∈
        AddSubmonoid.closure (splitE8RootSystem.root '' Set.range e8SimpleMathlibRoot) ∨
      -splitE8RootSystem.root α ∈
        AddSubmonoid.closure (splitE8RootSystem.root '' Set.range e8SimpleMathlibRoot) := by
  obtain ⟨r, hr⟩ := e8MathlibRoot_surjective α
  have hwt : splitE8RootSystem.root α = e8RootWeight r := by
    rw [← hr]
    rfl
  rw [hwt, e8RootWeight_eq_sum_simple r]
  have hmem_gen : ∀ j : Fin 8, e8RootWeight (e8ESimpleIdx j) ∈
      AddSubmonoid.closure (splitE8RootSystem.root '' Set.range e8SimpleMathlibRoot) := by
    intro j
    apply AddSubmonoid.subset_closure
    exact ⟨e8SimpleMathlibRoot j, ⟨j, rfl⟩, rfl⟩
  rcases e8RootCoord_sign_uniform r with hpos | hneg
  · left
    have hns : (∑ j : Fin 8, (e8RootCoord r j : ℝ) • e8RootWeight (e8ESimpleIdx j)) =
        ∑ j : Fin 8, (e8RootCoord r j).toNat • e8RootWeight (e8ESimpleIdx j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Nat.cast_smul_eq_nsmul ℝ]
      congr 1
      exact_mod_cast (Int.toNat_of_nonneg (hpos j)).symm
    rw [hns]
    exact AddSubmonoid.sum_mem _ fun j _ => AddSubmonoid.nsmul_mem _ (hmem_gen j) _
  · right
    have hns : -(∑ j : Fin 8, (e8RootCoord r j : ℝ) • e8RootWeight (e8ESimpleIdx j)) =
        ∑ j : Fin 8, (-e8RootCoord r j).toNat • e8RootWeight (e8ESimpleIdx j) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h0 : 0 ≤ -e8RootCoord r j := neg_nonneg.mpr (hneg j)
      rw [← Nat.cast_smul_eq_nsmul ℝ, ← Int.cast_natCast, Int.toNat_of_nonneg h0,
        Int.cast_neg, neg_smul]
    rw [hns]
    exact AddSubmonoid.sum_mem _ fun j _ => AddSubmonoid.nsmul_mem _ (hmem_gen j) _

/-- Explicit `RootPairing.Base` for `splitE8RootSystem` supported on the 8 Bourbaki simple roots. -/
noncomputable def splitE8RootSystemBase : splitE8RootSystem.Base :=
  RootPairing.Base.mk' splitE8RootSystem (Set.range e8SimpleMathlibRoot)
    e8SimpleMathlibRoot_linearIndepOn e8SimpleMathlibRoot_mem_or_neg_mem

/-- Bijection between `Fin 8` and `splitE8RootSystemBase.support`. -/
noncomputable def splitE8BaseSupportEquiv : Fin 8 ≃ splitE8RootSystemBase.support :=
  Equiv.ofBijective
    (fun i => ⟨e8SimpleMathlibRoot i, by
      change e8SimpleMathlibRoot i ∈ (Set.toFinite (Set.range e8SimpleMathlibRoot)).toFinset
      rw [Set.Finite.mem_toFinset]
      exact ⟨i, rfl⟩⟩)
    ⟨fun _ _ h => e8SimpleMathlibRoot_injective (congrArg Subtype.val h),
     fun ⟨α, hα⟩ => by
       change α ∈ (Set.toFinite (Set.range e8SimpleMathlibRoot)).toFinset at hα
       rw [Set.Finite.mem_toFinset] at hα
       rcases hα with ⟨i, rfl⟩
       exact ⟨i, rfl⟩⟩

private theorem e8SimpleE_mem_rootSpace (i : Fin 8) :
    e8SimpleE i ∈ LieAlgebra.rootSpace splitE8Cartan (e8SimpleMathlibRoot i).1 := by
  rw [e8SimpleE_eq_rootVec]
  exact e8RootVec_mem_rootSpace (e8ESimpleIdx i)

private theorem e8SimpleF_mem_neg_rootSpace (i : Fin 8) :
    e8SimpleF i ∈ LieAlgebra.rootSpace splitE8Cartan (-(e8SimpleMathlibRoot i).1) := by
  rw [LieAlgebra.rootSpace, LieModule.mem_genWeightSpace]
  intro H
  refine ⟨1, ?_⟩
  rw [pow_one]
  change ⁅(H : SplitE8Lie), e8SimpleF i⁆ - (-(e8SimpleMathlibRoot i).1) H • e8SimpleF i = 0
  rw [e8SimpleF_eq_rootVec, lie_smul, e8RootVec_bracket_cartan H (e8FSimpleIdx i), smul_smul]
  have hwt : e8RootWeight (e8FSimpleIdx i) H = -((e8SimpleMathlibRoot i).1 H) := by
    have hrep := e8SimpleHBasis.sum_repr H
    conv_lhs => rw [← hrep]
    conv_rhs => rw [← hrep]
    simp only [map_sum, map_smul, smul_eq_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : e8RootWeight (e8FSimpleIdx i) (e8SimpleHBasis j) =
        -((e8SimpleMathlibRoot i).1 (e8SimpleHBasis j)) := by
      have he8 : (e8SimpleHBasis j : splitE8Cartan) =
          ⟨e8SimpleH j, e8SimpleH_mem_splitE8Cartan j⟩ :=
        Subtype.ext (e8SimpleHBasis_apply j)
      rw [he8]
      change e8RootWeight (e8FSimpleIdx i) ⟨e8SimpleH j, e8SimpleH_mem_splitE8Cartan j⟩ =
        -e8RootWeight (e8ESimpleIdx i) ⟨e8SimpleH j, e8SimpleH_mem_splitE8Cartan j⟩
      rw [e8RootWeight_simpleH, e8RootWeight_simpleH]
      simp only [e8RootEigenvalue, e8RootCoord_fSimple, Pi.neg_apply, mul_neg,
        Finset.sum_neg_distrib, Int.cast_neg]
    rw [hj]
    ring
  have hneg_app : (-(e8SimpleMathlibRoot i).1) H = -((e8SimpleMathlibRoot i).1 H) := rfl
  rw [hwt, hneg_app, smul_smul, mul_comm, sub_self]

theorem e8Simple_coroot_eq (i : Fin 8) :
    (LieAlgebra.IsKilling.coroot (e8SimpleMathlibRoot i).1 : SplitE8Lie) = e8SimpleH i :=
  ((e8Simple_isSl2Triple i).h_eq_coroot
    (LieSubalgebra.isNonZero_coe_root (e8SimpleMathlibRoot i))
    (e8SimpleE_mem_rootSpace i) (e8SimpleF_mem_neg_rootSpace i)).symm

theorem e8Simple_coroot_subtype_eq (i : Fin 8) :
    LieAlgebra.IsKilling.coroot (e8SimpleMathlibRoot i).1 =
      ⟨e8SimpleH i, e8SimpleH_mem_splitE8Cartan i⟩ :=
  Subtype.ext (e8Simple_coroot_eq i)

theorem splitE8RootSystem_pairing_simple (i j : Fin 8) :
    splitE8RootSystem.pairing (e8SimpleMathlibRoot i) (e8SimpleMathlibRoot j) =
      (CartanMatrix.E 8 i j : ℝ) := by
  change (LieAlgebra.IsKilling.rootSystem splitE8Cartan).pairing
    (e8SimpleMathlibRoot i) (e8SimpleMathlibRoot j) = (CartanMatrix.E 8 i j : ℝ)
  rw [LieAlgebra.IsKilling.rootSystem_pairing_apply, e8Simple_coroot_subtype_eq j]
  change e8RootWeight (e8ESimpleIdx i) ⟨e8SimpleH j, e8SimpleH_mem_splitE8Cartan j⟩ =
    (CartanMatrix.E 8 i j : ℝ)
  rw [e8RootWeight_simpleH, e8RootEigenvalue_simpleE, splitE8_cartan_eq_mathlib]
  have hsymm : CartanMatrix.E 8 j i = CartanMatrix.E 8 i j := by
    have ht := congrFun (congrFun (CartanMatrix.E_transpose 8) i) j
    simpa [Matrix.transpose_apply] using ht
  rw [hsymm]

theorem splitE8RootSystemBase_cartanMatrix_eq :
    splitE8RootSystemBase.cartanMatrix.reindex
      splitE8BaseSupportEquiv.symm splitE8BaseSupportEquiv.symm = CartanMatrix.E 8 := by
  ext i j
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  change splitE8RootSystem.pairing (splitE8BaseSupportEquiv i : splitE8Cartan.root)
    (splitE8BaseSupportEquiv j : splitE8Cartan.root) = algebraMap ℤ ℝ (CartanMatrix.E 8 i j)
  change splitE8RootSystem.pairing (e8SimpleMathlibRoot i) (e8SimpleMathlibRoot j) =
    (CartanMatrix.E 8 i j : ℝ)
  exact splitE8RootSystem_pairing_simple i j

end E8RootSystem

/-! ## 4. `IsIrreducible`, `IsSimple`, and `IsSemisimple` -/

section Simplicity

instance splitE8RootSystem_isIrreducible : splitE8RootSystem.IsIrreducible := by
  have : Nontrivial (Module.Dual ℝ splitE8Cartan) :=
    ⟨e8RootWeight 0, 0, e8RootWeight_ne_zero 0⟩
  refine RootPairing.IsIrreducible.mk' splitE8RootSystem fun q hq hne => ?_
  obtain ⟨f, hfq, hf0⟩ := (Submodule.ne_bot_iff q).mp hne
  have hex_i : ∃ i : Fin 8, f ⟨e8SimpleH i, e8SimpleH_mem_splitE8Cartan i⟩ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hf0
    apply e8SimpleHBasis.ext
    intro i
    have he8 : (e8SimpleHBasis i : splitE8Cartan) =
        ⟨e8SimpleH i, e8SimpleH_mem_splitE8Cartan i⟩ :=
      Subtype.ext (e8SimpleHBasis_apply i)
    rw [he8, LinearMap.zero_apply]
    exact hall i
  have hmem_of_refl : ∀ i : Fin 8,
      f ⟨e8SimpleH i, e8SimpleH_mem_splitE8Cartan i⟩ ≠ 0 →
      splitE8RootSystem.root (e8SimpleMathlibRoot i) ∈ q := by
    intro i hi
    have hinv := (Module.End.mem_invtSubmodule _).mp
      (hq (e8SimpleMathlibRoot i)) hfq
    change (splitE8RootSystem.reflection (e8SimpleMathlibRoot i)) f ∈ q at hinv
    rw [RootPairing.reflection_apply] at hinv
    have hsub : (splitE8RootSystem.coroot' (e8SimpleMathlibRoot i) f) •
        splitE8RootSystem.root (e8SimpleMathlibRoot i) ∈ q := by
      have h := q.sub_mem hfq hinv
      simpa using h
    have hcor : splitE8RootSystem.coroot' (e8SimpleMathlibRoot i) f =
        f ⟨e8SimpleH i, e8SimpleH_mem_splitE8Cartan i⟩ := by
      change (LieAlgebra.IsKilling.rootSystem splitE8Cartan).toLinearMap f
        ((LieAlgebra.IsKilling.rootSystem splitE8Cartan).coroot (e8SimpleMathlibRoot i)) = _
      rw [LieAlgebra.IsKilling.rootSystem_toLinearMap_apply,
        LieAlgebra.IsKilling.rootSystem_coroot_apply, e8Simple_coroot_subtype_eq i]
    rw [hcor] at hsub
    have hs := q.smul_mem (f ⟨e8SimpleH i, e8SimpleH_mem_splitE8Cartan i⟩)⁻¹ hsub
    rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at hs
  have hstep : ∀ j k : Fin 8, Tag.cartan .E8 j k = -1 →
      splitE8RootSystem.root (e8SimpleMathlibRoot j) ∈ q →
      splitE8RootSystem.root (e8SimpleMathlibRoot k) ∈ q := by
    intro j k hc hqj
    have hinv := (Module.End.mem_invtSubmodule _).mp
      (hq (e8SimpleMathlibRoot k)) hqj
    change (splitE8RootSystem.reflection (e8SimpleMathlibRoot k))
      (splitE8RootSystem.root (e8SimpleMathlibRoot j)) ∈ q at hinv
    rw [RootPairing.reflection_apply_root, splitE8RootSystem_pairing_simple,
      ← splitE8_cartan_eq_mathlib, hc, Int.cast_neg, Int.cast_one, neg_smul, sub_neg_eq_add,
      one_smul] at hinv
    have hk : splitE8RootSystem.root (e8SimpleMathlibRoot j) +
        splitE8RootSystem.root (e8SimpleMathlibRoot k) -
        splitE8RootSystem.root (e8SimpleMathlibRoot j) ∈ q :=
      q.sub_mem hinv hqj
    simpa using hk
  have hc02 : Tag.cartan .E8 (0 : Fin 8) (2 : Fin 8) = -1 := by decide
  have hc20 : Tag.cartan .E8 (2 : Fin 8) (0 : Fin 8) = -1 := by decide
  have hc13 : Tag.cartan .E8 (1 : Fin 8) (3 : Fin 8) = -1 := by decide
  have hc31 : Tag.cartan .E8 (3 : Fin 8) (1 : Fin 8) = -1 := by decide
  have hc23 : Tag.cartan .E8 (2 : Fin 8) (3 : Fin 8) = -1 := by decide
  have hc32 : Tag.cartan .E8 (3 : Fin 8) (2 : Fin 8) = -1 := by decide
  have hc34 : Tag.cartan .E8 (3 : Fin 8) (4 : Fin 8) = -1 := by decide
  have hc43 : Tag.cartan .E8 (4 : Fin 8) (3 : Fin 8) = -1 := by decide
  have hc45 : Tag.cartan .E8 (4 : Fin 8) (5 : Fin 8) = -1 := by decide
  have hc54 : Tag.cartan .E8 (5 : Fin 8) (4 : Fin 8) = -1 := by decide
  have hc56 : Tag.cartan .E8 (5 : Fin 8) (6 : Fin 8) = -1 := by decide
  have hc65 : Tag.cartan .E8 (6 : Fin 8) (5 : Fin 8) = -1 := by decide
  have hc67 : Tag.cartan .E8 (6 : Fin 8) (7 : Fin 8) = -1 := by decide
  have hc76 : Tag.cartan .E8 (7 : Fin 8) (6 : Fin 8) = -1 := by decide
  obtain ⟨i₀, hi₀⟩ := hex_i
  have hi₀_mem := hmem_of_refl i₀ hi₀
  have h3_mem : splitE8RootSystem.root (e8SimpleMathlibRoot 3) ∈ q := by
    fin_cases i₀
    · exact hstep 2 3 hc23 (hstep 0 2 hc02 hi₀_mem)
    · exact hstep 1 3 hc13 hi₀_mem
    · exact hstep 2 3 hc23 hi₀_mem
    · exact hi₀_mem
    · exact hstep 4 3 hc43 hi₀_mem
    · exact hstep 4 3 hc43 (hstep 5 4 hc54 hi₀_mem)
    · exact hstep 4 3 hc43 (hstep 5 4 hc54 (hstep 6 5 hc65 hi₀_mem))
    · exact hstep 4 3 hc43 (hstep 5 4 hc54 (hstep 6 5 hc65 (hstep 7 6 hc76 hi₀_mem)))
  have h2_mem := hstep 3 2 hc32 h3_mem
  have h0_mem := hstep 2 0 hc20 h2_mem
  have h1_mem := hstep 3 1 hc31 h3_mem
  have h4_mem := hstep 3 4 hc34 h3_mem
  have h5_mem := hstep 4 5 hc45 h4_mem
  have h6_mem := hstep 5 6 hc56 h5_mem
  have h7_mem := hstep 6 7 hc67 h6_mem
  have hall_simple : ∀ j : Fin 8, e8RootWeight (e8ESimpleIdx j) ∈ q := by
    intro j
    fin_cases j
    · exact h0_mem
    · exact h1_mem
    · exact h2_mem
    · exact h3_mem
    · exact h4_mem
    · exact h5_mem
    · exact h6_mem
    · exact h7_mem
  have hall_roots : ∀ α : splitE8Cartan.root, splitE8RootSystem.root α ∈ q := by
    intro α
    obtain ⟨r, hr⟩ := e8MathlibRoot_surjective α
    have hwt : splitE8RootSystem.root α = e8RootWeight r := by rw [← hr]; rfl
    rw [hwt, e8RootWeight_eq_sum_simple r]
    exact q.sum_mem fun j _ => q.smul_mem _ (hall_simple j)
  rw [eq_top_iff, ← RootPairing.IsRootSystem.span_root_eq_top (P := splitE8RootSystem),
    Submodule.span_le]
  rintro _ ⟨α, rfl⟩
  exact hall_roots α

/-- **Unconditional Simplicity of Split `𝔈₈(8)`**:
`SplitE8Lie` is a simple 248-dimensional real Lie algebra. -/
instance splitE8Lie_isSimple : LieAlgebra.IsSimple ℝ SplitE8Lie :=
  LieAlgebra.IsKilling.isSimple_iff_isIrreducible.mp splitE8RootSystem_isIrreducible

instance splitE8Lie_isSemisimple : LieAlgebra.IsSemisimple ℝ SplitE8Lie :=
  inferInstance

end Simplicity

end InfoGeometry.Algebra

end noncomputable section
