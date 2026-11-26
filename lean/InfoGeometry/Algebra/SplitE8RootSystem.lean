/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.MagicSquareTitsBracket
import InfoGeometry.Algebra.H3ZornF4Simplicity
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

/-!
# 8D Split Cartan Subalgebra, 240 Root Spaces, and Bourbaki `E₈` System for `SplitE8Lie` (`𝔈₈(8)`)

On the 248-dimensional split Freudenthal–Tits Magic Square Lie algebra `SplitE8Lie` (`𝔈₈(8)`),
this module constructs:
1. The 8-dimensional split Cartan subalgebra `splitE8Cartan : LieSubalgebra ℝ SplitE8Lie`
   spanned by `cartan8 : Fin 8 → SplitE8Lie` (`2D G₂ ⊕ 4D F₄ ⊕ (e₀ ⊗ (d₁, d₂))`), with
   `IsLieAbelian splitE8Cartan`, `Module.finrank ℝ splitE8Cartan = 8`, and
   `splitE8Cartan.IsCartanSubalgebra`.
2. All 240 root vectors `e8RootVec : Fin 240 → SplitE8Lie` across 5 exact eigenvector sectors
   (`6` pure `G₂`, `18` hybridized `G₂ ⊕ Mix`, `24` pure `F₄`, `48` hybridized `F₄ ⊕ Mix`,
   `144` pure `Mix`), with integer Cartan weights `cartan8Weight : Fin 240 → Fin 8 → ℤ`,
   the 248D basis `splitE8Cartan8Basis : Module.Basis (Fin 8 ⊕ Fin 240) ℝ SplitE8Lie`,
   and `LieModule.IsTriangularizable ℝ splitE8Cartan SplitE8Lie`.
3. The Bourbaki `E₈` simple Chevalley system `(e8SimpleE, e8SimpleF, e8SimpleH)` (`Fin 8`)
   matching `CartanMatrix.E 8`, proving `Submodule.span ℝ (Set.range e8SimpleH) =
   splitE8Cartan.toSubmodule`, `e8ChevalleyBasis`, `e8RootEquiv : Fin 240 ≃
   {v : Fin 8 → ℤ // IsRoot .E8 v}`, `IsSl2Triple`, opposite-root Cartan membership,
   and `e8_cartan_weight_kill_mem` for `SplitE8Simplicity`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open scoped TensorProduct BigOperators
open H3Zorn
open InfoGeometry.Algebra.MagicSquareTitsBracket
open InfoGeometry.Canonical.NativeTitsE8Carrier
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit
open InfoGeometry.Exceptional.CFSGPort.Chevalley
open InfoGeometry.Lie.CanonicalZornDerivationDimension

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private abbrev VZ := InfoGeometry.Canonical.NativeTitsE8Carrier.VZ

private instance : Module.Finite ℝ SplitE8Lie := inferInstance
private instance : Module.Finite ℝ (H3Zorn ℝ) := Module.Finite.of_basis h3ZornBasis

/-! ## 1. 8D Split Cartan Subalgebra `splitE8Cartan` -/

section CartanSubalgebra

private theorem h3DiagZero₁_eq_basis :
    (h3DiagZero₁ : H3Zorn ℝ) = h3ZornBasis 0 - h3ZornBasis 1 := by
  rw [h3DiagZero₁_coe, h3ZornBasis_zero, h3ZornBasis_one]

private theorem h3DiagZero₂_eq_basis :
    (h3DiagZero₂ : H3Zorn ℝ) = h3ZornBasis 1 - h3ZornBasis 2 := by
  rw [h3DiagZero₂_coe, h3ZornBasis_one, h3ZornBasis_two]

private theorem jordanLmul_sub_apply (x y : H3Zorn ℝ) :
    jordanLmul (R := ℝ) (x - y) = jordanLmul (R := ℝ) x - jordanLmul (R := ℝ) y := by
  apply LinearMap.ext
  intro z
  change (x - y) * z = x * z - y * z
  exact sub_mul x y z

private theorem h3zornToMatrix_two_jordanLmul_diag₁ :
    h3zornToMatrix ((2 : ℝ) • jordanLmul (R := ℝ) h3DiagZero₁.1) =
      (sparseToMat (sparseSub (twoLData 0) (twoLData 1))).map Int.cast := by
  rw [h3DiagZero₁_eq_basis, jordanLmul_sub_apply, smul_sub, map_sub,
    h3zornToMatrix_two_jordanLmul_basis 0, h3zornToMatrix_two_jordanLmul_basis 1, sparseToMat_sub]
  ext a b
  simp [Matrix.sub_apply]

private theorem h3zornToMatrix_two_jordanLmul_diag₂ :
    h3zornToMatrix ((2 : ℝ) • jordanLmul (R := ℝ) h3DiagZero₂.1) =
      (sparseToMat (sparseSub (twoLData 1) (twoLData 2))).map Int.cast := by
  rw [h3DiagZero₂_eq_basis, jordanLmul_sub_apply, smul_sub, map_sub,
    h3zornToMatrix_two_jordanLmul_basis 1, h3zornToMatrix_two_jordanLmul_basis 2, sparseToMat_sub]
  ext a b
  simp [Matrix.sub_apply]

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

private theorem h3ZornBasis_diag_mul_comm (i j : Fin 3) :
    h3ZornJordanInnerDerivation (h3ZornBasis ⟨i.val, by omega⟩)
      (h3ZornBasis ⟨j.val, by omega⟩) = 0 := by
  have hchk : (List.finRange 3).all (fun i => (List.finRange 3).all (fun j =>
      sparseZeroCheck (sparseComm (twoLData ⟨i.val, by omega⟩)
        (twoLData ⟨j.val, by omega⟩)))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  apply Subtype.ext
  have h4 : (4 : ℝ) • (h3ZornJordanInnerDerivation (h3ZornBasis ⟨i.val, by omega⟩)
      (h3ZornBasis ⟨j.val, by omega⟩) : Module.End ℝ (H3Zorn ℝ)) = 0 := by
    have h4eq : (4 : ℝ) • (h3ZornJordanInnerDerivation (h3ZornBasis ⟨i.val, by omega⟩)
        (h3ZornBasis ⟨j.val, by omega⟩) : Module.End ℝ (H3Zorn ℝ)) =
        ((2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis ⟨i.val, by omega⟩)) *
          ((2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis ⟨j.val, by omega⟩)) -
          ((2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis ⟨j.val, by omega⟩)) *
          ((2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis ⟨i.val, by omega⟩)) := by
      apply LinearMap.ext; intro z
      change (4 : ℝ) • (h3ZornBasis ⟨i.val, by omega⟩ * (h3ZornBasis ⟨j.val, by omega⟩ * z) -
          h3ZornBasis ⟨j.val, by omega⟩ * (h3ZornBasis ⟨i.val, by omega⟩ * z)) =
        (2 : ℝ) • (h3ZornBasis ⟨i.val, by omega⟩ * ((2 : ℝ) • (h3ZornBasis ⟨j.val, by omega⟩ * z))) -
          (2 : ℝ) • (h3ZornBasis ⟨j.val, by omega⟩ * ((2 : ℝ) • (h3ZornBasis ⟨i.val, by omega⟩ * z)))
      rw [mul_smul_comm, mul_smul_comm, smul_smul, smul_smul]
      norm_num
      module
    apply h3zornToMatrix.injective
    rw [h4eq, map_sub, map_mul, map_mul,
      h3zornToMatrix_two_jordanLmul_basis ⟨i.val, by omega⟩,
      h3zornToMatrix_two_jordanLmul_basis ⟨j.val, by omega⟩]
    have hcomm : (sparseToMat (twoLData ⟨i.val, by omega⟩)).map (Int.cast : ℤ → ℝ) *
          (sparseToMat (twoLData ⟨j.val, by omega⟩)).map Int.cast -
        (sparseToMat (twoLData ⟨j.val, by omega⟩)).map Int.cast *
          (sparseToMat (twoLData ⟨i.val, by omega⟩)).map Int.cast =
        (sparseToMat (sparseComm (twoLData ⟨i.val, by omega⟩)
          (twoLData ⟨j.val, by omega⟩))).map Int.cast := by
      rw [sparseToMat_comm]
      ext a b; simp [Matrix.mul_apply]
    rw [hcomm, sparseToMat_eq_zero_of_sparseZeroCheck (hchk i j), map_zero]
    ext a b; simp
  exact (smul_eq_zero.mp h4).resolve_left (by norm_num)

theorem f4Inner_h3DiagZero₁_h3DiagZero₂ : f4Inner h3DiagZero₁ h3DiagZero₂ = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  have h01 := congrArg (fun D : H3ZornF4Derivations => (D.1 : Module.End ℝ (H3Zorn ℝ)) z)
    (h3ZornBasis_diag_mul_comm 0 1)
  have h02 := congrArg (fun D : H3ZornF4Derivations => (D.1 : Module.End ℝ (H3Zorn ℝ)) z)
    (h3ZornBasis_diag_mul_comm 0 2)
  have h11 := congrArg (fun D : H3ZornF4Derivations => (D.1 : Module.End ℝ (H3Zorn ℝ)) z)
    (h3ZornBasis_diag_mul_comm 1 1)
  have h12 := congrArg (fun D : H3ZornF4Derivations => (D.1 : Module.End ℝ (H3Zorn ℝ)) z)
    (h3ZornBasis_diag_mul_comm 1 2)
  simp only [h3ZornJordanInnerDerivation_apply, ZeroMemClass.coe_zero, LinearMap.zero_apply]
    at h01 h02 h11 h12
  change (h3DiagZero₁ : H3Zorn ℝ) * ((h3DiagZero₂ : H3Zorn ℝ) * z) -
      (h3DiagZero₂ : H3Zorn ℝ) * ((h3DiagZero₁ : H3Zorn ℝ) * z) = 0
  rw [h3DiagZero₁_eq_basis, h3DiagZero₂_eq_basis]
  simp only [sub_mul, mul_sub]
  dsimp at h01 h02 h11 h12
  have htot : (h3ZornBasis 0 * (h3ZornBasis 1 * z) - h3ZornBasis 1 * (h3ZornBasis 0 * z)) -
      (h3ZornBasis 0 * (h3ZornBasis 2 * z) - h3ZornBasis 2 * (h3ZornBasis 0 * z)) -
      (h3ZornBasis 1 * (h3ZornBasis 1 * z) - h3ZornBasis 1 * (h3ZornBasis 1 * z)) +
      (h3ZornBasis 1 * (h3ZornBasis 2 * z) - h3ZornBasis 2 * (h3ZornBasis 1 * z)) = 0 := by
    rw [h01, h02, h11, h12]
    abel
  rw [← htot]
  abel

private theorem projG2_mk (g : G2DerivationCarrier) (m : MixedCarrier) (f : F4DerivationCarrier) :
    projG2 ⟨g, m, f⟩ = g := rfl
private theorem projF4_mk (g : G2DerivationCarrier) (m : MixedCarrier) (f : F4DerivationCarrier) :
    projF4 ⟨g, m, f⟩ = f := rfl
private theorem projMixed_mk (g : G2DerivationCarrier) (m : MixedCarrier) (f : F4DerivationCarrier) :
    projMixed ⟨g, m, f⟩ = m := rfl

/-- Canonical 8-element basis of the split Cartan subalgebra of `SplitE8Lie`:
- `0, 1`: 2D split Cartan of `G₂(2)`
- `2..5`: 4D split Cartan of `F₄(4)`
- `6, 7`: 2D mixed Cartan `e₀ ⊗ (d₁ - d₂)` and `e₀ ⊗ (d₂ - d₃)`. -/
def cartan8 : Fin 8 → SplitE8Lie
  | 0 => embedG2 (g2CartanBasis 0)
  | 1 => embedG2 (g2CartanBasis 1)
  | 2 => embedF4 (f4CartanBasis 0)
  | 3 => embedF4 (f4CartanBasis 1)
  | 4 => embedF4 (f4CartanBasis 2)
  | 5 => embedF4 (f4CartanBasis 3)
  | 6 => embedTensor zornE0 h3DiagZero₁
  | 7 => embedTensor zornE0 h3DiagZero₂

theorem cartan8_comm (a b : Fin 8) : ⁅cartan8 a, cartan8 b⁆ = 0 := by
  fin_cases a <;> fin_cases b <;>
    simp only [cartan8, bracket_g2_g2, bracket_f4_f4, bracket_g2_f4, bracket_f4_g2,
      bracket_g2_tensor, bracket_tensor_g2, bracket_f4_tensor, bracket_tensor_f4,
      bracket_tensor_tensor, g2CartanBasis_comm, f4CartanBasis_comm,
      g2CartanBasis_apply_zornE0, f4CartanBasis_apply_h3DiagZero₁,
      f4CartanBasis_apply_h3DiagZero₂, g2Inner_self, zornComm0_self, f4Inner_self,
      f4Inner_h3DiagZero₁_h3DiagZero₂, f4Inner_antisymm h3DiagZero₁ h3DiagZero₂,
      LinearMap.zero_apply, smul_zero, map_zero, neg_zero, add_zero]

theorem cartan8_linearIndependent : LinearIndependent ℝ cartan8 := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hg2 : c 0 • g2CartanBasis 0 + c 1 • g2CartanBasis 1 = 0 := by
    have hp := congrArg projG2 hc
    rw [map_sum, map_zero, Fin.sum_univ_eight] at hp
    simpa [cartan8, embedG2_apply, embedF4_apply, embedTensor_apply, embedMixed_apply,
      projG2_mk] using hp
  have hc_g2 := Fintype.linearIndependent_iff.mp g2CartanBasis_linearIndependent
    (fun i : Fin 2 => match i with | 0 => c 0 | 1 => c 1)
    (by simpa [Fin.sum_univ_two] using hg2)
  have hf4 : (∑ i : Fin 4, c ⟨i.val + 2, by omega⟩ • f4CartanBasis i) = 0 := by
    have hp := congrArg projF4 hc
    rw [map_sum, map_zero, Fin.sum_univ_eight] at hp
    rw [Fin.sum_univ_four]
    simpa [cartan8, embedG2_apply, embedF4_apply, embedTensor_apply, embedMixed_apply,
      projF4_mk, add_assoc] using hp
  have hc_f4 := Fintype.linearIndependent_iff.mp f4CartanBasis_linearIndependent
    (fun i : Fin 4 => c ⟨i.val + 2, by omega⟩) hf4
  have hmix : c 6 • (zornE0 ⊗ₜ[ℝ] h3DiagZero₁) + c 7 • (zornE0 ⊗ₜ[ℝ] h3DiagZero₂) = 0 := by
    have hp := congrArg projMixed hc
    rw [map_sum, map_zero, Fin.sum_univ_eight] at hp
    simpa [cartan8, embedG2_apply, embedF4_apply, embedTensor_apply, embedMixed_apply,
      projMixed_mk] using hp
  let fOct : splitOctonionTraceZero →ₗ[ℝ] ℝ :=
    { toFun := fun a => a.1.a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let fH3_1 : h3TraceZero →ₗ[ℝ] ℝ :=
    { toFun := fun x => x.1.α₁
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let fH3_3 : h3TraceZero →ₗ[ℝ] ℝ :=
    { toFun := fun x => x.1.α₃
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let phi1 : MixedCarrier →ₗ[ℝ] ℝ :=
    TensorProduct.lift (LinearMap.lsmul ℝ ℝ |>.compl₂ fH3_1 |>.comp fOct)
  let phi3 : MixedCarrier →ₗ[ℝ] ℝ :=
    TensorProduct.lift (LinearMap.lsmul ℝ ℝ |>.compl₂ fH3_3 |>.comp fOct)
  have hc6 : c 6 = 0 := by
    have h1 := congrArg phi1 hmix
    have hval1 : phi1 (zornE0 ⊗ₜ[ℝ] h3DiagZero₁) = 1 := by
      change zornE0.1.a * h3DiagZero₁.1.α₁ = 1
      simp [zornE0, ZornVectorMatrix.diagonal, h3DiagZero₁, H3Zorn.sub_readback,
        h3_diag₁, h3_diag₂]
    have hval2 : phi1 (zornE0 ⊗ₜ[ℝ] h3DiagZero₂) = 0 := by
      change zornE0.1.a * h3DiagZero₂.1.α₁ = 0
      simp [zornE0, ZornVectorMatrix.diagonal, h3DiagZero₂, H3Zorn.sub_readback,
        h3_diag₂, h3_diag₃]
    rw [map_add, map_smul, map_smul, hval1, hval2, map_zero] at h1
    simpa using h1
  have hc7 : c 7 = 0 := by
    have h3 := congrArg phi3 hmix
    have hval1 : phi3 (zornE0 ⊗ₜ[ℝ] h3DiagZero₁) = 0 := by
      change zornE0.1.a * h3DiagZero₁.1.α₃ = 0
      simp [zornE0, ZornVectorMatrix.diagonal, h3DiagZero₁, H3Zorn.sub_readback,
        h3_diag₁, h3_diag₂]
    have hval2 : phi3 (zornE0 ⊗ₜ[ℝ] h3DiagZero₂) = -1 := by
      change zornE0.1.a * h3DiagZero₂.1.α₃ = -1
      simp [zornE0, ZornVectorMatrix.diagonal, h3DiagZero₂, H3Zorn.sub_readback,
        h3_diag₂, h3_diag₃]
    rw [map_add, map_smul, map_smul, hval1, hval2, map_zero] at h3
    simpa [smul_eq_mul] using h3
  intro a
  fin_cases a
  · exact hc_g2 0
  · exact hc_g2 1
  · exact hc_f4 0
  · exact hc_f4 1
  · exact hc_f4 2
  · exact hc_f4 3
  · exact hc6
  · exact hc7

/-- The 8-dimensional split Cartan subalgebra of `SplitE8Lie`. -/
def splitE8Cartan : LieSubalgebra ℝ SplitE8Lie where
  __ := Submodule.span ℝ (Set.range cartan8)
  lie_mem' {x y} hx hy := by
    have hcomm_left : ∀ a : Fin 8, ∀ z : SplitE8Lie,
        z ∈ Submodule.span ℝ (Set.range cartan8) → ⁅cartan8 a, z⁆ = 0 := by
      intro a z hz
      induction hz using Submodule.span_induction with
      | zero => simp
      | add u v _ _ ihu ihv => rw [lie_add, ihu, ihv, add_zero]
      | smul r u _ ihu => rw [lie_smul, ihu, smul_zero]
      | mem _ hm =>
        rcases hm with ⟨b, rfl⟩
        exact cartan8_comm a b
    have hcomm : ⁅x, y⁆ = 0 := by
      induction hx using Submodule.span_induction with
      | zero => simp
      | add u v _ _ ihu ihv => rw [add_lie, ihu, ihv, add_zero]
      | smul r u _ ihu => rw [smul_lie, ihu, smul_zero]
      | mem _ hm =>
        rcases hm with ⟨a, rfl⟩
        exact hcomm_left a y hy
    rw [hcomm]
    exact Submodule.zero_mem _

@[simp] theorem mem_splitE8Cartan_iff (x : SplitE8Lie) :
    x ∈ splitE8Cartan ↔ x ∈ Submodule.span ℝ (Set.range cartan8) := Iff.rfl

@[simp] theorem cartan8_mem_splitE8Cartan (a : Fin 8) : cartan8 a ∈ splitE8Cartan :=
  (mem_splitE8Cartan_iff _).mpr (Submodule.subset_span ⟨a, rfl⟩)

instance splitE8Cartan_isLieAbelian : IsLieAbelian splitE8Cartan where
  trivial x y := by
    apply Subtype.ext
    rcases x with ⟨xv, hx⟩
    rcases y with ⟨yv, hy⟩
    change ⁅xv, yv⁆ = 0
    rw [mem_splitE8Cartan_iff] at hx hy
    induction hx using Submodule.span_induction with
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ => rw [add_lie, ih₁, ih₂, add_zero]
    | smul c _ _ ih => rw [smul_lie, ih, smul_zero]
    | mem _ hx =>
      rcases hx with ⟨a, rfl⟩
      induction hy using Submodule.span_induction with
      | zero => simp
      | add _ _ _ _ ih₁ ih₂ => rw [lie_add, ih₁, ih₂, add_zero]
      | smul c _ _ ih => rw [lie_smul, ih, smul_zero]
      | mem _ hy =>
        rcases hy with ⟨b, rfl⟩
        exact cartan8_comm a b

/-- Canonical 8-element basis of `splitE8Cartan`. -/
def splitE8CartanBasis : Module.Basis (Fin 8) ℝ splitE8Cartan :=
  let v : Fin 8 → splitE8Cartan := fun a => ⟨cartan8 a, cartan8_mem_splitE8Cartan a⟩
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : ∑ a : Fin 8, c a • cartan8 a = 0 := congrArg Subtype.val hc
    exact Fintype.linearIndependent_iff.mp cartan8_linearIndependent c hc'
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    rintro ⟨x, hx⟩ _
    have hx' : x ∈ Submodule.span ℝ (Set.range cartan8) := (mem_splitE8Cartan_iff x).mp hx
    suffices hmem : ∀ y (hy : y ∈ Submodule.span ℝ (Set.range cartan8)),
        (⟨y, (mem_splitE8Cartan_iff y).mpr hy⟩ : splitE8Cartan) ∈
          Submodule.span ℝ (Set.range v) from hmem x hx'
    intro y hy
    induction hy using Submodule.span_induction with
    | zero => exact Submodule.zero_mem _
    | add _ _ _ _ ih₁ ih₂ => exact Submodule.add_mem _ ih₁ ih₂
    | smul r _ _ ih => exact Submodule.smul_mem _ r ih
    | mem _ hm =>
      rcases hm with ⟨a, rfl⟩
      exact Submodule.subset_span ⟨a, rfl⟩
  Module.Basis.mk hli hsp

@[simp] theorem splitE8CartanBasis_apply (a : Fin 8) :
    (splitE8CartanBasis a : SplitE8Lie) = cartan8 a := by
  simp [splitE8CartanBasis]

theorem finrank_splitE8Cartan : Module.finrank ℝ splitE8Cartan = 8 := by
  rw [Module.finrank_eq_card_basis splitE8CartanBasis, Fintype.card_fin]

end CartanSubalgebra

/-! ## 2. Sector Helper Lemmas (5 Simultaneous-Eigenvector Sectors) -/

section SectorHelpers

/-- Coordinate basis derivation of `G₂(2)` in `G2DerivationCarrier`. -/
def g2Param (j : Fin 14) : G2DerivationCarrier :=
  parameterDerivation (fun i => if i = j then 1 else 0)

/-- The 6 long root parameter indices (`A₂ ⊂ G₂`) annihilating `zornE0`. -/
def g2LongIdx : Fin 6 → Fin 14 := ![1, 2, 5, 7, 11, 12]

/-- Integer eigenvalues of `g2CartanBasis 0, 1` on `g2Param (g2LongIdx s)`. -/
def g2LongWeight (s : Fin 6) (a : Fin 2) : ℤ :=
  match s.val, a.val with
  | 0, 0 => -2 | 0, 1 => -1
  | 1, 0 => -1 | 1, 1 => -2
  | 2, 0 => 2  | 2, 1 => 1
  | 3, 0 => 1  | 3, 1 => -1
  | 4, 0 => 1  | 4, 1 => 2
  | _, 0 => -1 | _, _ => 1

private theorem vz_sub_a (X Y : VZ) : (X - Y).a = X.a - Y.a := rfl
private theorem vz_sub_v (X Y : VZ) (i : Fin 3) : (X - Y).v i = X.v i - Y.v i := rfl
private theorem vz_sub_w (X Y : VZ) (i : Fin 3) : (X - Y).w i = X.w i - Y.w i := rfl
private theorem vz_sub_b (X Y : VZ) : (X - Y).b = X.b - Y.b := rfl

private theorem g2CartanBasis_bracket_g2Long_0 (a : Fin 2) :
    ⁅g2CartanBasis a, g2Param (g2LongIdx 0)⁆ =
      (g2LongWeight 0 a : ℝ) • g2Param (g2LongIdx 0) := by
  apply parameterLinearEquiv.symm.injective
  have lhs_eq : ∀ D₁ D₂ : G2DerivationCarrier,
      parameterLinearEquiv.symm ⁅D₁, D₂⁆ = derivationParameters ⁅D₁, D₂⁆ := fun _ _ => rfl
  have hbr : ∀ (D₁ D₂ : VDer) (X : VZ), (⁅D₁, D₂⁆).toFun X = D₁ (D₂ X) - D₂ (D₁ X) :=
    fun _ _ _ => rfl
  rw [lhs_eq, map_smul]
  have hgp : ∀ j : Fin 14, parameterLinearEquiv.symm (g2Param j) =
      fun i => if i = j then (1 : ℝ) else 0 := fun j =>
    parameterLinearEquiv.symm_apply_apply _
  rw [hgp]
  funext k
  fin_cases a <;> fin_cases k <;>
    simp [derivationParameters, hbr, g2CartanBasis, g2Param, g2LongIdx, g2LongWeight,
      parameterDerivation, parameterAction, ZornVectorMatrix.E22, ZornVectorMatrix.U,
      ZornVectorMatrix.V, ZornVec3.basis, vz_sub_w]
  all_goals norm_num

private theorem g2CartanBasis_bracket_g2Long_1 (a : Fin 2) :
    ⁅g2CartanBasis a, g2Param (g2LongIdx 1)⁆ =
      (g2LongWeight 1 a : ℝ) • g2Param (g2LongIdx 1) := by
  apply parameterLinearEquiv.symm.injective
  have lhs_eq : ∀ D₁ D₂ : G2DerivationCarrier,
      parameterLinearEquiv.symm ⁅D₁, D₂⁆ = derivationParameters ⁅D₁, D₂⁆ := fun _ _ => rfl
  have hbr : ∀ (D₁ D₂ : VDer) (X : VZ), (⁅D₁, D₂⁆).toFun X = D₁ (D₂ X) - D₂ (D₁ X) :=
    fun _ _ _ => rfl
  rw [lhs_eq, map_smul]
  have hgp : ∀ j : Fin 14, parameterLinearEquiv.symm (g2Param j) =
      fun i => if i = j then (1 : ℝ) else 0 := fun j =>
    parameterLinearEquiv.symm_apply_apply _
  rw [hgp]
  funext k
  fin_cases a <;> fin_cases k <;>
    simp [derivationParameters, hbr, g2CartanBasis, g2Param, g2LongIdx, g2LongWeight,
      parameterDerivation, parameterAction, ZornVectorMatrix.E22, ZornVectorMatrix.U,
      ZornVectorMatrix.V, ZornVec3.basis, vz_sub_w]
  all_goals norm_num

private theorem g2CartanBasis_bracket_g2Long_2 (a : Fin 2) :
    ⁅g2CartanBasis a, g2Param (g2LongIdx 2)⁆ =
      (g2LongWeight 2 a : ℝ) • g2Param (g2LongIdx 2) := by
  apply parameterLinearEquiv.symm.injective
  have lhs_eq : ∀ D₁ D₂ : G2DerivationCarrier,
      parameterLinearEquiv.symm ⁅D₁, D₂⁆ = derivationParameters ⁅D₁, D₂⁆ := fun _ _ => rfl
  have hbr : ∀ (D₁ D₂ : VDer) (X : VZ), (⁅D₁, D₂⁆).toFun X = D₁ (D₂ X) - D₂ (D₁ X) :=
    fun _ _ _ => rfl
  rw [lhs_eq, map_smul]
  have hgp : ∀ j : Fin 14, parameterLinearEquiv.symm (g2Param j) =
      fun i => if i = j then (1 : ℝ) else 0 := fun j =>
    parameterLinearEquiv.symm_apply_apply _
  rw [hgp]
  funext k
  fin_cases a <;> fin_cases k <;>
    simp [derivationParameters, hbr, g2CartanBasis, g2Param, g2LongIdx, g2LongWeight,
      parameterDerivation, parameterAction, ZornVectorMatrix.E22, ZornVectorMatrix.U,
      ZornVectorMatrix.V, ZornVec3.basis, vz_sub_w]
  all_goals norm_num

private theorem g2CartanBasis_bracket_g2Long_3 (a : Fin 2) :
    ⁅g2CartanBasis a, g2Param (g2LongIdx 3)⁆ =
      (g2LongWeight 3 a : ℝ) • g2Param (g2LongIdx 3) := by
  apply parameterLinearEquiv.symm.injective
  have lhs_eq : ∀ D₁ D₂ : G2DerivationCarrier,
      parameterLinearEquiv.symm ⁅D₁, D₂⁆ = derivationParameters ⁅D₁, D₂⁆ := fun _ _ => rfl
  have hbr : ∀ (D₁ D₂ : VDer) (X : VZ), (⁅D₁, D₂⁆).toFun X = D₁ (D₂ X) - D₂ (D₁ X) :=
    fun _ _ _ => rfl
  rw [lhs_eq, map_smul]
  have hgp : ∀ j : Fin 14, parameterLinearEquiv.symm (g2Param j) =
      fun i => if i = j then (1 : ℝ) else 0 := fun j =>
    parameterLinearEquiv.symm_apply_apply _
  rw [hgp]
  funext k
  fin_cases a <;> fin_cases k <;>
    simp [derivationParameters, hbr, g2CartanBasis, g2Param, g2LongIdx, g2LongWeight,
      parameterDerivation, parameterAction, ZornVectorMatrix.E22, ZornVectorMatrix.U,
      ZornVectorMatrix.V, ZornVec3.basis, vz_sub_w]

private theorem g2CartanBasis_bracket_g2Long_4 (a : Fin 2) :
    ⁅g2CartanBasis a, g2Param (g2LongIdx 4)⁆ =
      (g2LongWeight 4 a : ℝ) • g2Param (g2LongIdx 4) := by
  apply parameterLinearEquiv.symm.injective
  have lhs_eq : ∀ D₁ D₂ : G2DerivationCarrier,
      parameterLinearEquiv.symm ⁅D₁, D₂⁆ = derivationParameters ⁅D₁, D₂⁆ := fun _ _ => rfl
  have hbr : ∀ (D₁ D₂ : VDer) (X : VZ), (⁅D₁, D₂⁆).toFun X = D₁ (D₂ X) - D₂ (D₁ X) :=
    fun _ _ _ => rfl
  rw [lhs_eq, map_smul]
  have hgp : ∀ j : Fin 14, parameterLinearEquiv.symm (g2Param j) =
      fun i => if i = j then (1 : ℝ) else 0 := fun j =>
    parameterLinearEquiv.symm_apply_apply _
  rw [hgp]
  funext k
  fin_cases a <;> fin_cases k <;>
    simp [derivationParameters, hbr, g2CartanBasis, g2Param, g2LongIdx, g2LongWeight,
      parameterDerivation, parameterAction, ZornVectorMatrix.E22, ZornVectorMatrix.U,
      ZornVectorMatrix.V, ZornVec3.basis, vz_sub_w]
  all_goals norm_num

private theorem g2CartanBasis_bracket_g2Long_5 (a : Fin 2) :
    ⁅g2CartanBasis a, g2Param (g2LongIdx 5)⁆ =
      (g2LongWeight 5 a : ℝ) • g2Param (g2LongIdx 5) := by
  apply parameterLinearEquiv.symm.injective
  have lhs_eq : ∀ D₁ D₂ : G2DerivationCarrier,
      parameterLinearEquiv.symm ⁅D₁, D₂⁆ = derivationParameters ⁅D₁, D₂⁆ := fun _ _ => rfl
  have hbr : ∀ (D₁ D₂ : VDer) (X : VZ), (⁅D₁, D₂⁆).toFun X = D₁ (D₂ X) - D₂ (D₁ X) :=
    fun _ _ _ => rfl
  rw [lhs_eq, map_smul]
  have hgp : ∀ j : Fin 14, parameterLinearEquiv.symm (g2Param j) =
      fun i => if i = j then (1 : ℝ) else 0 := fun j =>
    parameterLinearEquiv.symm_apply_apply _
  rw [hgp]
  funext k
  fin_cases a <;> fin_cases k <;>
    simp [derivationParameters, hbr, g2CartanBasis, g2Param, g2LongIdx, g2LongWeight,
      parameterDerivation, parameterAction, ZornVectorMatrix.E22, ZornVectorMatrix.U,
      ZornVectorMatrix.V, ZornVec3.basis, vz_sub_w]

private theorem g2CartanBasis_bracket_g2Long (a : Fin 2) (s : Fin 6) :
    ⁅g2CartanBasis a, g2Param (g2LongIdx s)⁆ =
      (g2LongWeight s a : ℝ) • g2Param (g2LongIdx s) := by
  fin_cases s
  · exact g2CartanBasis_bracket_g2Long_0 a
  · exact g2CartanBasis_bracket_g2Long_1 a
  · exact g2CartanBasis_bracket_g2Long_2 a
  · exact g2CartanBasis_bracket_g2Long_3 a
  · exact g2CartanBasis_bracket_g2Long_4 a
  · exact g2CartanBasis_bracket_g2Long_5 a

private theorem g2Param_g2Long_apply_zornE0 (s : Fin 6) :
    g2Act (g2Param (g2LongIdx s)) zornE0 = 0 := by
  fin_cases s <;> apply Subtype.ext <;> apply ZornVectorMatrix.ext <;>
    simp [g2Param, g2LongIdx, parameterDerivation, parameterAction, zornE0,
      ZornVectorMatrix.diagonal, ZornVectorMatrix.zero]

private theorem g2Param_ne_zero (j : Fin 14) : g2Param j ≠ 0 := by
  intro h0
  have h1 : parameterLinearEquiv.symm (g2Param j) j = 1 := by
    change parameterLinearEquiv.symm (parameterLinearEquiv (fun i => if i = j then 1 else 0)) j = 1
    rw [parameterLinearEquiv.symm_apply_apply]
    simp
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

/-- Eigenvalues of `g2CartanBasis 0, 1` on `zornU i`. -/
def g2UWeight (i : Fin 3) (a : Fin 2) : ℤ :=
  match i.val, a.val with
  | 0, 0 => 1  | 0, 1 => 1
  | 1, 0 => -1 | 1, 1 => 0
  | _, 0 => 0  | _, _ => -1

/-- Eigenvalues of `g2CartanBasis 0, 1` on `zornV i`. -/
def g2VWeight (i : Fin 3) (a : Fin 2) : ℤ := -g2UWeight i a

private theorem g2CartanBasis_apply_zornU_weight (a : Fin 2) (i : Fin 3) :
    g2Act (g2CartanBasis a) (zornU i) = (g2UWeight i a : ℝ) • zornU i := by
  rw [g2CartanBasis_apply_zornU]
  fin_cases a <;> fin_cases i <;> simp [g2UWeight]

private theorem g2CartanBasis_apply_zornV_weight (a : Fin 2) (i : Fin 3) :
    g2Act (g2CartanBasis a) (zornV i) = (g2VWeight i a : ℝ) • zornV i := by
  rw [g2CartanBasis_apply_zornV]
  fin_cases a <;> fin_cases i <;> simp [g2VWeight, g2UWeight]

private theorem g2Act_g2Inner_zornE0_zornU (i : Fin 3) :
    g2Act (g2Inner zornE0 (zornU i)) zornE0 = (-4 : ℝ) • zornU i := by
  fin_cases i <;> apply Subtype.ext <;>
    (change stanDerMap (R := ℝ) zornE0.1 (zornU _).1 zornE0.1 = _
     apply ZornVectorMatrix.ext <;>
       simp [stanDerMap, L_map, R_map, zornE0, zornU, ZornVectorMatrix.diagonal, ZornVectorMatrix.U,
         ZornVectorMatrix.mul, ZornVectorMatrix.smul, ZornVectorMatrix.add,
         ZornVectorMatrix.neg, ZornVec3.dot, ZornVec3.cross,
         vz_sub_a, vz_sub_v, vz_sub_w, vz_sub_b];
     funext k; fin_cases k <;> (dsimp; simp [ZornVec3.basis, Fin.ext_iff]; try norm_num))

private theorem g2Act_g2Inner_zornE0_zornV (i : Fin 3) :
    g2Act (g2Inner zornE0 (zornV i)) zornE0 = (-4 : ℝ) • zornV i := by
  fin_cases i <;> apply Subtype.ext <;>
    (change stanDerMap (R := ℝ) zornE0.1 (zornV _).1 zornE0.1 = _
     apply ZornVectorMatrix.ext <;>
       simp [stanDerMap, L_map, R_map, zornE0, zornV, ZornVectorMatrix.diagonal, ZornVectorMatrix.V,
         ZornVectorMatrix.mul, ZornVectorMatrix.smul, ZornVectorMatrix.add,
         ZornVectorMatrix.neg, ZornVec3.dot, ZornVec3.cross,
         vz_sub_a, vz_sub_v, vz_sub_w, vz_sub_b];
     funext k; fin_cases k <;> (dsimp; simp [ZornVec3.basis, Fin.ext_iff]; try norm_num))

private theorem g2Inner_zornE0_zornU_ne_zero (i : Fin 3) :
    g2Inner zornE0 (zornU i) ≠ 0 := by
  intro h0
  have hact := g2Act_g2Inner_zornE0_zornU i
  rw [h0] at hact
  have hz : g2Act (0 : G2DerivationCarrier) zornE0 = 0 := rfl
  rw [hz] at hact
  have hsm : (zornU i) = 0 := (smul_eq_zero.mp hact.symm).resolve_left (by norm_num)
  have hv := congrArg (fun a : splitOctonionTraceZero => a.1.v i) hsm
  have h1 : (zornU i).1.v i = 1 := by simp [zornU, ZornVectorMatrix.U, ZornVec3.basis]
  rw [h1] at hv
  exact one_ne_zero hv

private theorem g2Inner_zornE0_zornV_ne_zero (i : Fin 3) :
    g2Inner zornE0 (zornV i) ≠ 0 := by
  intro h0
  have hact := g2Act_g2Inner_zornE0_zornV i
  rw [h0] at hact
  have hz : g2Act (0 : G2DerivationCarrier) zornE0 = 0 := rfl
  rw [hz] at hact
  have hsm : (zornV i) = 0 := (smul_eq_zero.mp hact.symm).resolve_left (by norm_num)
  have hw := congrArg (fun a : splitOctonionTraceZero => a.1.w i) hsm
  have h1 : (zornV i).1.w i = 1 := by simp [zornV, ZornVectorMatrix.V, ZornVec3.basis]
  rw [h1] at hw
  exact one_ne_zero hw

private theorem g2CartanBasis_bracket_g2Inner_zornU (a : Fin 2) (i : Fin 3) :
    ⁅g2CartanBasis a, g2Inner zornE0 (zornU i)⁆ =
      (g2UWeight i a : ℝ) • g2Inner zornE0 (zornU i) := by
  rw [g2_covariant, g2CartanBasis_apply_zornE0, g2CartanBasis_apply_zornU_weight]
  have h0 : g2Inner (0 : splitOctonionTraceZero) (zornU i) = 0 := by
    rw [← g2InnerLM_apply, map_zero, LinearMap.zero_apply]
  rw [h0, zero_add, ← g2InnerLM_apply, map_smul, g2InnerLM_apply]

private theorem g2CartanBasis_bracket_g2Inner_zornV (a : Fin 2) (i : Fin 3) :
    ⁅g2CartanBasis a, g2Inner zornE0 (zornV i)⁆ =
      (g2VWeight i a : ℝ) • g2Inner zornE0 (zornV i) := by
  rw [g2_covariant, g2CartanBasis_apply_zornE0, g2CartanBasis_apply_zornV_weight]
  have h0 : g2Inner (0 : splitOctonionTraceZero) (zornV i) = 0 := by
    rw [← g2InnerLM_apply, map_zero, LinearMap.zero_apply]
  rw [h0, zero_add, ← g2InnerLM_apply, map_smul, g2InnerLM_apply]

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

private theorem h3ZornBasis_mul_eq (p q : Fin 27) (v : H3Zorn ℝ)
    (hv : ∀ r : Fin 27, h3ZornBasis.repr v r = (sparseVal (twoLData p) r q : ℝ) / 2) :
    h3ZornBasis p * h3ZornBasis q = v := by
  have h2 : (2 : ℝ) • (h3ZornBasis p * h3ZornBasis q) = (2 : ℝ) • v := by
    apply h3ZornBasis.ext_elem
    intro r
    have hr : h3ZornBasis.repr ((2 : ℝ) • (h3ZornBasis p * h3ZornBasis q)) r =
        h3zornToMatrix ((2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis p)) r q := by
      rw [h3zornToMatrix_apply]; rfl
    rw [hr, h3zornToMatrix_two_jordanLmul_basis p, Matrix.map_apply, map_smul,
      Finsupp.smul_apply, smul_eq_mul, hv r]
    change (sparseVal (twoLData p) r q : ℝ) = _
    ring
  have hsub : (2 : ℝ) • (h3ZornBasis p * h3ZornBasis q - v) = 0 := by
    rw [smul_sub, h2, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_left (by norm_num))

private theorem h3ZornBasis_0_mul_0 : h3ZornBasis 0 * h3ZornBasis 0 = h3ZornBasis 0 := by
  apply h3ZornBasis_mul_eq 0 0 (h3ZornBasis 0)
  intro r
  rw [h3ZornBasis.repr_self, Finsupp.single_apply]
  fin_cases r <;> norm_num [twoLData]

private theorem h3ZornBasis_0_mul_1 : h3ZornBasis 0 * h3ZornBasis 1 = 0 := by
  apply h3ZornBasis_mul_eq 0 1 0
  intro r
  rw [map_zero, Finsupp.zero_apply]
  fin_cases r <;> norm_num [twoLData]

private theorem h3ZornBasis_1_mul_1 : h3ZornBasis 1 * h3ZornBasis 1 = h3ZornBasis 1 := by
  apply h3ZornBasis_mul_eq 1 1 (h3ZornBasis 1)
  intro r
  rw [h3ZornBasis.repr_self, Finsupp.single_apply]
  fin_cases r <;> norm_num [twoLData]

private theorem h3ZornBasis_1_mul_2 : h3ZornBasis 1 * h3ZornBasis 2 = 0 := by
  apply h3ZornBasis_mul_eq 1 2 0
  intro r
  rw [map_zero, Finsupp.zero_apply]
  fin_cases r <;> norm_num [twoLData]

private theorem h3ZornBasis_2_mul_2 : h3ZornBasis 2 * h3ZornBasis 2 = h3ZornBasis 2 := by
  apply h3ZornBasis_mul_eq 2 2 (h3ZornBasis 2)
  intro r
  rw [h3ZornBasis.repr_self, Finsupp.single_apply]
  fin_cases r <;> norm_num [twoLData]

private theorem h3_one_eq_basis_sum' :
    (1 : H3Zorn ℝ) = h3ZornBasis 0 + h3ZornBasis 1 + h3ZornBasis 2 := by
  rw [h3ZornBasis_zero, h3ZornBasis_one, h3ZornBasis_two]
  apply H3Zorn.ext_h3 <;>
    simp [H3Zorn.one_readback, H3Zorn.add_readback, h3_diag₁, h3_diag₂, h3_diag₃,
      ZornVectorMatrix.add_zero]

private theorem h3Mul0_h3DiagZero₁_self :
    h3Mul0 h3DiagZero₁ h3DiagZero₁ =
      (1 / 3 : ℝ) • h3DiagZero₁ + (2 / 3 : ℝ) • h3DiagZero₂ := by
  apply Subtype.ext
  rw [h3Mul0_coe, traceBilin_h3DiagZero₁_self]
  simp only [Submodule.coe_add, SetLike.val_smul, h3DiagZero₁_eq_basis, h3DiagZero₂_eq_basis,
    h3_one_eq_basis_sum']
  rw [sub_mul, mul_sub, mul_sub, h3ZornBasis_0_mul_0, h3ZornBasis_0_mul_1,
    mul_comm (h3ZornBasis 1) (h3ZornBasis 0), h3ZornBasis_0_mul_1, h3ZornBasis_1_mul_1]
  module

private theorem h3Mul0_h3DiagZero₁_two :
    h3Mul0 h3DiagZero₁ h3DiagZero₂ =
      (1 / 3 : ℝ) • h3DiagZero₁ - (1 / 3 : ℝ) • h3DiagZero₂ := by
  apply Subtype.ext
  rw [h3Mul0_coe, traceBilin_h3DiagZero₁_two]
  simp only [Submodule.coe_sub, SetLike.val_smul, h3DiagZero₁_eq_basis, h3DiagZero₂_eq_basis,
    h3_one_eq_basis_sum']
  rw [sub_mul, mul_sub, mul_sub, h3ZornBasis_0_mul_1,
    mul_comm (h3ZornBasis 0) (h3ZornBasis 2),
    show h3ZornBasis 2 * h3ZornBasis 0 = 0 from by
      apply h3ZornBasis_mul_eq 2 0 0; intro r; rw [map_zero, Finsupp.zero_apply]
      fin_cases r <;> norm_num [twoLData],
    h3ZornBasis_1_mul_1, h3ZornBasis_1_mul_2]
  module

private theorem h3Mul0_h3DiagZero₂_self :
    h3Mul0 h3DiagZero₂ h3DiagZero₂ =
      (-2 / 3 : ℝ) • h3DiagZero₁ - (1 / 3 : ℝ) • h3DiagZero₂ := by
  apply Subtype.ext
  rw [h3Mul0_coe, traceBilin_h3DiagZero₂_self]
  simp only [Submodule.coe_sub, SetLike.val_smul, h3DiagZero₁_eq_basis, h3DiagZero₂_eq_basis,
    h3_one_eq_basis_sum']
  rw [sub_mul, mul_sub, mul_sub, h3ZornBasis_1_mul_1, h3ZornBasis_1_mul_2,
    mul_comm (h3ZornBasis 2) (h3ZornBasis 1), h3ZornBasis_1_mul_2, h3ZornBasis_2_mul_2]
  module

/-- Hybridized `G₂ ⊕ Mix` root vectors (`U` branch, 9 vectors for `i, s : Fin 3`). -/
def sector2UVec (i s : Fin 3) : SplitE8Lie :=
  let v0 := embedG2 (g2Inner zornE0 (zornU i))
  let v1 := embedTensor (zornU i) h3DiagZero₁
  let v2 := embedTensor (zornU i) h3DiagZero₂
  match s.val with
  | 0 => v0 + (4 : ℝ) • v1 + (2 : ℝ) • v2
  | 1 => v0 - (2 : ℝ) • v1 + (2 : ℝ) • v2
  | _ => v0 - (2 : ℝ) • v1 - (4 : ℝ) • v2

/-- Hybridized `G₂ ⊕ Mix` root vectors (`V` branch, 9 vectors for `i, s : Fin 3`). -/
def sector2VVec (i s : Fin 3) : SplitE8Lie :=
  let v0 := embedG2 (g2Inner zornE0 (zornV i))
  let v1 := embedTensor (zornV i) h3DiagZero₁
  let v2 := embedTensor (zornV i) h3DiagZero₂
  match s.val with
  | 0 => v0 - (4 : ℝ) • v1 - (2 : ℝ) • v2
  | 1 => v0 + (2 : ℝ) • v1 - (2 : ℝ) • v2
  | _ => v0 + (2 : ℝ) • v1 + (4 : ℝ) • v2

/-- `(H_mix0, H_mix1)` weight pairs for the 3 `U`-branch Sector 2 eigenvectors. -/
def s2UWeight (s : Fin 3) : ℤ × ℤ :=
  match s.val with
  | 0 => (2, 0)
  | 1 => (-2, 2)
  | _ => (0, -2)

/-- `(H_mix0, H_mix1)` weight pairs for the 3 `V`-branch Sector 2 eigenvectors. -/
def s2VWeight (s : Fin 3) : ℤ × ℤ :=
  match s.val with
  | 0 => (-2, 0)
  | 1 => (2, -2)
  | _ => (0, 2)

private theorem cartan8_bracket_sector2UVec (a : Fin 8) (i s : Fin 3) :
    ⁅cartan8 a, sector2UVec i s⁆ =
      (if ha2 : a.val < 2 then (g2UWeight i ⟨a.val, ha2⟩ : ℝ)
       else if a.val < 6 then 0
       else if a.val = 6 then ((s2UWeight s).1 : ℝ)
       else ((s2UWeight s).2 : ℝ)) • sector2UVec i s := by
  fin_cases a
  · fin_cases s <;> fin_cases i <;>
      (dsimp only [cartan8, sector2UVec]
       simp only [Nat.zero_lt_succ, ↓reduceDIte, lie_add, lie_sub, lie_smul,
         bracket_g2_g2, bracket_g2_tensor, g2CartanBasis_bracket_g2Inner_zornU,
         g2CartanBasis_apply_zornU_weight, g2UWeight, Fin.val_zero,
         LinearMap.smul_apply, map_smul,
         smul_add, smul_sub, smul_smul, Int.cast_one, Int.cast_neg, Int.cast_zero]
       module)
  · fin_cases s <;> fin_cases i <;>
      (dsimp only [cartan8, sector2UVec]
       simp only [Nat.one_lt_two, ↓reduceDIte, lie_add, lie_sub, lie_smul,
         bracket_g2_g2, bracket_g2_tensor, g2CartanBasis_bracket_g2Inner_zornU,
         g2CartanBasis_apply_zornU_weight, g2UWeight, Fin.val_one,
         LinearMap.smul_apply, map_smul,
         smul_add, smul_sub, smul_smul, Int.cast_one, Int.cast_neg, Int.cast_zero]
       module)
  · fin_cases s <;>
      (dsimp only [cartan8, sector2UVec]
       simp only [Nat.reduceLT, ↓reduceDIte, ↓reduceIte, lie_add, lie_sub, lie_smul,
         bracket_f4_g2, bracket_f4_tensor, f4CartanBasis_apply_h3DiagZero₁,
         f4CartanBasis_apply_h3DiagZero₂, map_zero, smul_zero, add_zero, sub_zero, zero_smul])
  · fin_cases s <;>
      (dsimp only [cartan8, sector2UVec]
       simp only [Nat.reduceLT, ↓reduceDIte, ↓reduceIte, lie_add, lie_sub, lie_smul,
         bracket_f4_g2, bracket_f4_tensor, f4CartanBasis_apply_h3DiagZero₁,
         f4CartanBasis_apply_h3DiagZero₂, map_zero, smul_zero, add_zero, sub_zero, zero_smul])
  · fin_cases s <;>
      (dsimp only [cartan8, sector2UVec]
       simp only [Nat.reduceLT, ↓reduceDIte, ↓reduceIte, lie_add, lie_sub, lie_smul,
         bracket_f4_g2, bracket_f4_tensor, f4CartanBasis_apply_h3DiagZero₁,
         f4CartanBasis_apply_h3DiagZero₂, map_zero, smul_zero, add_zero, sub_zero, zero_smul])
  · fin_cases s <;>
      (dsimp only [cartan8, sector2UVec]
       simp only [Nat.reduceLT, ↓reduceDIte, ↓reduceIte, lie_add, lie_sub, lie_smul,
         bracket_f4_g2, bracket_f4_tensor, f4CartanBasis_apply_h3DiagZero₁,
         f4CartanBasis_apply_h3DiagZero₂, map_zero, smul_zero, add_zero, sub_zero, zero_smul])
  · fin_cases s <;>
      (dsimp only [cartan8, sector2UVec, s2UWeight]
       simp only [Nat.reduceLT, ↓reduceDIte, ↓reduceIte,
         lie_add, lie_sub, lie_smul, bracket_tensor_g2,
         bracket_tensor_tensor, g2Act_g2Inner_zornE0_zornU, traceBilin_h3DiagZero₁_self,
         traceBilin_h3DiagZero₁_two, h3Mul0_h3DiagZero₁_self,
         h3Mul0_h3DiagZero₁_two, f4Inner_self, f4Inner_h3DiagZero₁_h3DiagZero₂,
         zornBilin_zornE0_zornU, zornComm0_zornE0_zornU,
         mul_zero, zero_smul, map_zero, add_zero,
         LinearMap.smul_apply, map_smul, map_add, map_sub,
         smul_add, smul_sub, smul_smul, Int.cast_ofNat, Int.cast_neg, Int.cast_zero]
       module)
  · fin_cases s <;>
      (dsimp only [cartan8, sector2UVec, s2UWeight]
       simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceDIte, ↓reduceIte,
         lie_add, lie_sub, lie_smul, bracket_tensor_g2,
         bracket_tensor_tensor, g2Act_g2Inner_zornE0_zornU, traceBilin_h3DiagZero₁_two,
         traceBilin_h3DiagZero₂_self, traceBilin_symm h3DiagZero₂.1 h3DiagZero₁.1,
         h3Mul0_h3DiagZero₁_two, h3Mul0_h3DiagZero₂_self,
         h3Mul0_comm h3DiagZero₂ h3DiagZero₁, f4Inner_self,
         f4Inner_antisymm h3DiagZero₁ h3DiagZero₂, f4Inner_h3DiagZero₁_h3DiagZero₂,
         zornBilin_zornE0_zornU, zornComm0_zornE0_zornU,
         mul_zero, zero_smul, map_zero, zero_add, add_zero,
         LinearMap.smul_apply, map_smul, map_sub,
         smul_add, smul_sub, smul_smul, Int.cast_ofNat, Int.cast_neg, Int.cast_zero]
       module)

private theorem cartan8_bracket_sector2VVec (a : Fin 8) (i s : Fin 3) :
    ⁅cartan8 a, sector2VVec i s⁆ =
      (if ha2 : a.val < 2 then (g2VWeight i ⟨a.val, ha2⟩ : ℝ)
       else if a.val < 6 then 0
       else if a.val = 6 then ((s2VWeight s).1 : ℝ)
       else ((s2VWeight s).2 : ℝ)) • sector2VVec i s := by
  fin_cases a
  · fin_cases s <;> fin_cases i <;>
      (dsimp only [cartan8, sector2VVec]
       simp only [Nat.zero_lt_succ, ↓reduceDIte, lie_add, lie_sub, lie_smul,
         bracket_g2_g2, bracket_g2_tensor, g2CartanBasis_bracket_g2Inner_zornV,
         g2CartanBasis_apply_zornV_weight, g2VWeight, g2UWeight, Fin.val_zero,
         LinearMap.smul_apply, map_smul,
         smul_add, smul_sub, smul_smul, Int.cast_one, Int.cast_neg, Int.cast_zero]
       module)
  · fin_cases s <;> fin_cases i <;>
      (dsimp only [cartan8, sector2VVec]
       simp only [Nat.one_lt_two, ↓reduceDIte, lie_add, lie_sub, lie_smul,
         bracket_g2_g2, bracket_g2_tensor, g2CartanBasis_bracket_g2Inner_zornV,
         g2CartanBasis_apply_zornV_weight, g2VWeight, g2UWeight, Fin.val_one,
         LinearMap.smul_apply, map_smul,
         smul_add, smul_sub, smul_smul, Int.cast_one, Int.cast_neg, Int.cast_zero]
       module)
  · fin_cases s <;>
      (dsimp only [cartan8, sector2VVec]
       simp only [Nat.reduceLT, ↓reduceDIte, ↓reduceIte, lie_add, lie_sub, lie_smul,
         bracket_f4_g2, bracket_f4_tensor, f4CartanBasis_apply_h3DiagZero₁,
         f4CartanBasis_apply_h3DiagZero₂, map_zero, smul_zero, add_zero, sub_zero, zero_smul])
  · fin_cases s <;>
      (dsimp only [cartan8, sector2VVec]
       simp only [Nat.reduceLT, ↓reduceDIte, ↓reduceIte, lie_add, lie_sub, lie_smul,
         bracket_f4_g2, bracket_f4_tensor, f4CartanBasis_apply_h3DiagZero₁,
         f4CartanBasis_apply_h3DiagZero₂, map_zero, smul_zero, add_zero, sub_zero, zero_smul])
  · fin_cases s <;>
      (dsimp only [cartan8, sector2VVec]
       simp only [Nat.reduceLT, ↓reduceDIte, ↓reduceIte, lie_add, lie_sub, lie_smul,
         bracket_f4_g2, bracket_f4_tensor, f4CartanBasis_apply_h3DiagZero₁,
         f4CartanBasis_apply_h3DiagZero₂, map_zero, smul_zero, add_zero, sub_zero, zero_smul])
  · fin_cases s <;>
      (dsimp only [cartan8, sector2VVec]
       simp only [Nat.reduceLT, ↓reduceDIte, ↓reduceIte, lie_add, lie_sub, lie_smul,
         bracket_f4_g2, bracket_f4_tensor, f4CartanBasis_apply_h3DiagZero₁,
         f4CartanBasis_apply_h3DiagZero₂, map_zero, smul_zero, add_zero, sub_zero, zero_smul])
  · fin_cases s <;>
      (dsimp only [cartan8, sector2VVec, s2VWeight]
       simp only [Nat.reduceLT, ↓reduceDIte, ↓reduceIte,
         lie_add, lie_sub, lie_smul, bracket_tensor_g2,
         bracket_tensor_tensor, g2Act_g2Inner_zornE0_zornV, traceBilin_h3DiagZero₁_self,
         traceBilin_h3DiagZero₁_two, h3Mul0_h3DiagZero₁_self,
         h3Mul0_h3DiagZero₁_two, f4Inner_self, f4Inner_h3DiagZero₁_h3DiagZero₂,
         zornBilin_zornE0_zornV, zornComm0_zornE0_zornV,
         mul_zero, zero_smul, map_zero, zero_add, add_zero,
         LinearMap.smul_apply, map_smul, map_add, map_sub,
         smul_add, smul_sub, smul_smul, Int.cast_ofNat, Int.cast_neg, Int.cast_zero]
       module)
  · fin_cases s <;>
      (dsimp only [cartan8, sector2VVec, s2VWeight]
       simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceDIte, ↓reduceIte,
         lie_add, lie_sub, lie_smul, bracket_tensor_g2,
         bracket_tensor_tensor, g2Act_g2Inner_zornE0_zornV, traceBilin_h3DiagZero₁_two,
         traceBilin_h3DiagZero₂_self, traceBilin_symm h3DiagZero₂.1 h3DiagZero₁.1,
         h3Mul0_h3DiagZero₁_two, h3Mul0_h3DiagZero₂_self,
         h3Mul0_comm h3DiagZero₂ h3DiagZero₁, f4Inner_self,
         f4Inner_antisymm h3DiagZero₁ h3DiagZero₂, f4Inner_h3DiagZero₁_h3DiagZero₂,
         zornBilin_zornE0_zornV, zornComm0_zornE0_zornV,
         mul_zero, zero_smul, map_zero, add_zero,
         LinearMap.smul_apply, map_smul, map_sub,
         smul_add, smul_sub, smul_smul, Int.cast_ofNat, Int.cast_neg, Int.cast_zero]
       module)

/-- Permutation aligning `f4CartanBasis` (`MagicSquareTitsBracket`) with `f4SimpleH` (`H3ZornF4Simplicity`). -/
def f4Perm : Fin 4 → Fin 4 := ![0, 1, 3, 2]

private theorem f4CartanBasis_eq_f4SimpleH (i : Fin 4) :
    f4CartanBasis i = f4SimpleH (f4Perm i) := by
  fin_cases i
  · apply Subtype.ext; change (e6SimpleH 1 : Module.End ℝ (H3Zorn ℝ)) = _; rw [f4SimpleH_coe_eq]; rfl
  · apply Subtype.ext; change (e6SimpleH 3 : Module.End ℝ (H3Zorn ℝ)) = _; rw [f4SimpleH_coe_eq]; rfl
  · apply Subtype.ext
    change ((e6SimpleH 0 + e6SimpleH 5 : h3zornCubicStabilizer) : Module.End ℝ (H3Zorn ℝ)) = _
    rw [f4SimpleH_coe_eq]; rfl
  · apply Subtype.ext
    change ((e6SimpleH 2 + e6SimpleH 4 : h3zornCubicStabilizer) : Module.End ℝ (H3Zorn ℝ)) = _
    rw [f4SimpleH_coe_eq]; rfl

private theorem f4CartanBasis_bracket_f4RootVec (i : Fin 4) (r : Fin 48) :
    ⁅f4CartanBasis i, f4RootVec r⁆ = (f4RootEigenvalue (f4Perm i) r : ℝ) • f4RootVec r := by
  rw [f4CartanBasis_eq_f4SimpleH i, f4RootVec_bracket_H]

private theorem f4RootSparse_lt24_diag_zero (j : Fin 24) (r : Fin 27) (c : Fin 3) :
    sparseVal (f4RootSparse ⟨j.val, by omega⟩) r ⟨c.val, by omega⟩ = 0 := by
  have hchk : (List.finRange 24).all (fun j => (List.finRange 27).all (fun r =>
      (List.finRange 3).all (fun c =>
        sparseVal (f4RootSparse ⟨j.val, by omega⟩) r ⟨c.val, by omega⟩ == 0))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
  exact hchk j r c

private theorem f4Act_f4RootVec_lt24_diag (j : Fin 24) (d : Fin 3) :
    (f4RootVec ⟨j.val, by omega⟩ : H3ZornF4Derivations).1 (h3ZornBasis ⟨d.val, by omega⟩) = 0 := by
  apply h3ZornBasis.ext_elem
  intro r
  have h1 : h3ZornBasis.repr ((f4RootVec ⟨j.val, by omega⟩ : H3ZornF4Derivations).1
      (h3ZornBasis ⟨d.val, by omega⟩)) r =
      h3zornToMatrix (f4RootVec ⟨j.val, by omega⟩ : Module.End ℝ (H3Zorn ℝ)) r ⟨d.val, by omega⟩ := by
    rw [h3zornToMatrix_apply]; rfl
  rw [h1, h3zornToMatrix_f4RootVec, Matrix.map_apply, map_zero, Finsupp.zero_apply]
  change (sparseVal (f4RootSparse ⟨j.val, by omega⟩) r ⟨d.val, by omega⟩ : ℝ) = 0
  rw [f4RootSparse_lt24_diag_zero j r d, Int.cast_zero]

private theorem f4Act_f4RootVec_lt24_h3DiagZero₁ (j : Fin 24) :
    f4Act (f4RootVec ⟨j.val, by omega⟩) h3DiagZero₁ = 0 := by
  apply Subtype.ext
  have h0 := f4Act_f4RootVec_lt24_diag j 0
  have h1 := f4Act_f4RootVec_lt24_diag j 1
  dsimp at h0 h1
  rw [f4Act_coe, h3DiagZero₁_eq_basis, map_sub, h0, h1, sub_self, Submodule.coe_zero]

private theorem f4Act_f4RootVec_lt24_h3DiagZero₂ (j : Fin 24) :
    f4Act (f4RootVec ⟨j.val, by omega⟩) h3DiagZero₂ = 0 := by
  apply Subtype.ext
  have h1 := f4Act_f4RootVec_lt24_diag j 1
  have h2 := f4Act_f4RootVec_lt24_diag j 2
  dsimp at h1 h2
  rw [f4Act_coe, h3DiagZero₂_eq_basis, map_sub, h1, h2, sub_self, Submodule.coe_zero]

/-- The 24 off-diagonal basis elements `h3ZornBasis (3 + k)` inside `h3TraceZero`. -/
def h3TraceZeroOff (k : Fin 24) : h3TraceZero :=
  ⟨h3ZornBasis ⟨3 + k.val, by omega⟩, by
    change linearTrace (h3ZornBasis ⟨3 + k.val, by omega⟩) = 0
    have htr : ∀ x : H3Zorn ℝ,
        linearTrace x = h3ZornCoordinate x 0 + h3ZornCoordinate x 1 + h3ZornCoordinate x 2 :=
      fun _ => rfl
    rw [htr, h3ZornCoordinate_basis_self, h3ZornCoordinate_basis_self,
      h3ZornCoordinate_basis_self]
    have h0 : (⟨3 + k.val, by omega⟩ : Fin 27) ≠ 0 := by
      intro h; have hv := congrArg Fin.val h; dsimp at hv; omega
    have h1 : (⟨3 + k.val, by omega⟩ : Fin 27) ≠ 1 := by
      intro h; have hv := congrArg Fin.val h; dsimp at hv; omega
    have h2 : (⟨3 + k.val, by omega⟩ : Fin 27) ≠ 2 := by
      intro h; have hv := congrArg Fin.val h; dsimp at hv; omega
    simp [h0, h1, h2]⟩

@[simp] theorem h3TraceZeroOff_coe (k : Fin 24) :
    (h3TraceZeroOff k : H3Zorn ℝ) = h3ZornBasis ⟨3 + k.val, by omega⟩ := rfl

/-- `(H_mix0, H_mix1)` weight pairs for the `F₄ ⊕ Mix` hybridized Sector 4 eigenvectors. -/
def f4MixPair (k : Fin 24) : ℤ × ℤ :=
  if k.val < 8 then (2, -1) else if k.val < 16 then (-1, 2) else (-1, -1)

/-- `(H_mix0, H_mix1)` weight pairs for the pure `Mix` (`U ⊗ off`) Sector 5 eigenvectors. -/
def uMixPair (k : Fin 24) : ℤ × ℤ :=
  if k.val < 8 then (0, 1) else if k.val < 16 then (-1, 0) else (1, -1)

private theorem f4RootEigenvalue_ge24_eq (i : Fin 4) (k : Fin 24) :
    f4RootEigenvalue (f4Perm i) ⟨24 + k.val, by omega⟩ =
      f4CartanWeight ⟨3 + k.val, by omega⟩ i := by
  have hchk : (List.finRange 4).all (fun i => (List.finRange 24).all (fun k =>
      f4RootEigenvalue (f4Perm i) ⟨24 + k.val, by omega⟩ ==
        f4CartanWeight ⟨3 + k.val, by omega⟩ i)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
  exact hchk i k

private theorem f4RootSparse_ge24_col_d1 (k : Fin 24) (r : Fin 27) :
    sparseVal (f4RootSparse ⟨24 + k.val, by omega⟩) r 0 -
      sparseVal (f4RootSparse ⟨24 + k.val, by omega⟩) r 1 =
      if r.val = 3 + k.val then -(f4MixPair k).1 else 0 := by
  have hchk : (List.finRange 24).all (fun k => (List.finRange 27).all (fun r =>
      sparseVal (f4RootSparse ⟨24 + k.val, by omega⟩) r 0 -
        sparseVal (f4RootSparse ⟨24 + k.val, by omega⟩) r 1 ==
        if r.val = 3 + k.val then -(f4MixPair k).1 else 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
  exact hchk k r

private theorem f4RootSparse_ge24_col_d2 (k : Fin 24) (r : Fin 27) :
    sparseVal (f4RootSparse ⟨24 + k.val, by omega⟩) r 1 -
      sparseVal (f4RootSparse ⟨24 + k.val, by omega⟩) r 2 =
      if r.val = 3 + k.val then -(f4MixPair k).2 else 0 := by
  have hchk : (List.finRange 24).all (fun k => (List.finRange 27).all (fun r =>
      sparseVal (f4RootSparse ⟨24 + k.val, by omega⟩) r 1 -
        sparseVal (f4RootSparse ⟨24 + k.val, by omega⟩) r 2 ==
        if r.val = 3 + k.val then -(f4MixPair k).2 else 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
  exact hchk k r

private theorem f4Act_f4RootVec_ge24_h3DiagZero₁ (k : Fin 24) :
    f4Act (f4RootVec ⟨24 + k.val, by omega⟩) h3DiagZero₁ =
      (-(f4MixPair k).1 : ℝ) • h3TraceZeroOff k := by
  apply Subtype.ext
  apply h3ZornBasis.ext_elem
  intro r
  rw [f4Act_coe, h3DiagZero₁_eq_basis, map_sub, map_sub, SetLike.val_smul, map_smul,
    h3TraceZeroOff_coe, h3ZornBasis.repr_self, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply]
  have h0 : h3ZornBasis.repr ((f4RootVec ⟨24 + k.val, by omega⟩ : H3ZornF4Derivations).1
      (h3ZornBasis 0)) r =
      h3zornToMatrix (f4RootVec ⟨24 + k.val, by omega⟩ : Module.End ℝ (H3Zorn ℝ)) r 0 := by
    rw [h3zornToMatrix_apply]; rfl
  have h1 : h3ZornBasis.repr ((f4RootVec ⟨24 + k.val, by omega⟩ : H3ZornF4Derivations).1
      (h3ZornBasis 1)) r =
      h3zornToMatrix (f4RootVec ⟨24 + k.val, by omega⟩ : Module.End ℝ (H3Zorn ℝ)) r 1 := by
    rw [h3zornToMatrix_apply]; rfl
  rw [Finsupp.sub_apply, h0, h1, h3zornToMatrix_f4RootVec]
  simp only [Matrix.map_apply]
  change (sparseVal (f4RootSparse ⟨24 + k.val, by omega⟩) r 0 : ℝ) -
      (sparseVal (f4RootSparse ⟨24 + k.val, by omega⟩) r 1 : ℝ) = _
  rw [← Int.cast_sub, f4RootSparse_ge24_col_d1 k r]
  by_cases hr : (⟨3 + k.val, by omega⟩ : Fin 27) = r
  · subst hr; simp
  · have hne : r.val ≠ 3 + k.val := fun h => hr (Fin.ext h.symm)
    simp [hr, hne]

private theorem f4Act_f4RootVec_ge24_h3DiagZero₂ (k : Fin 24) :
    f4Act (f4RootVec ⟨24 + k.val, by omega⟩) h3DiagZero₂ =
      (-(f4MixPair k).2 : ℝ) • h3TraceZeroOff k := by
  apply Subtype.ext
  apply h3ZornBasis.ext_elem
  intro r
  rw [f4Act_coe, h3DiagZero₂_eq_basis, map_sub, map_sub, SetLike.val_smul, map_smul,
    h3TraceZeroOff_coe, h3ZornBasis.repr_self, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply]
  have h1 : h3ZornBasis.repr ((f4RootVec ⟨24 + k.val, by omega⟩ : H3ZornF4Derivations).1
      (h3ZornBasis 1)) r =
      h3zornToMatrix (f4RootVec ⟨24 + k.val, by omega⟩ : Module.End ℝ (H3Zorn ℝ)) r 1 := by
    rw [h3zornToMatrix_apply]; rfl
  have h2 : h3ZornBasis.repr ((f4RootVec ⟨24 + k.val, by omega⟩ : H3ZornF4Derivations).1
      (h3ZornBasis 2)) r =
      h3zornToMatrix (f4RootVec ⟨24 + k.val, by omega⟩ : Module.End ℝ (H3Zorn ℝ)) r 2 := by
    rw [h3zornToMatrix_apply]; rfl
  rw [Finsupp.sub_apply, h1, h2, h3zornToMatrix_f4RootVec]
  simp only [Matrix.map_apply]
  change (sparseVal (f4RootSparse ⟨24 + k.val, by omega⟩) r 1 : ℝ) -
      (sparseVal (f4RootSparse ⟨24 + k.val, by omega⟩) r 2 : ℝ) = _
  rw [← Int.cast_sub, f4RootSparse_ge24_col_d2 k r]
  by_cases hr : (⟨3 + k.val, by omega⟩ : Fin 27) = r
  · subst hr; simp
  · have hne : r.val ≠ 3 + k.val := fun h => hr (Fin.ext h.symm)
    simp [hr, hne]

private theorem f4Inner_d1_off_check (k : Fin 24) :
    sparseEq (sparseComm (sparseSub (twoLData 0) (twoLData 1)) (twoLData ⟨3 + k.val, by omega⟩))
      (sparseSmul (f4MixPair k).1 (f4RootSparse ⟨24 + k.val, by omega⟩)) = true := by
  have hchk : (List.finRange 24).all (fun k =>
      sparseEq (sparseComm (sparseSub (twoLData 0) (twoLData 1)) (twoLData ⟨3 + k.val, by omega⟩))
        (sparseSmul (f4MixPair k).1 (f4RootSparse ⟨24 + k.val, by omega⟩))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  exact hchk k

private theorem f4Inner_d2_off_check (k : Fin 24) :
    sparseEq (sparseComm (sparseSub (twoLData 1) (twoLData 2)) (twoLData ⟨3 + k.val, by omega⟩))
      (sparseSmul (f4MixPair k).2 (f4RootSparse ⟨24 + k.val, by omega⟩)) = true := by
  have hchk : (List.finRange 24).all (fun k =>
      sparseEq (sparseComm (sparseSub (twoLData 1) (twoLData 2)) (twoLData ⟨3 + k.val, by omega⟩))
        (sparseSmul (f4MixPair k).2 (f4RootSparse ⟨24 + k.val, by omega⟩))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  exact hchk k

private theorem four_f4Inner_h3DiagZero₁_off (k : Fin 24) :
    (4 : ℝ) • f4Inner h3DiagZero₁ (h3TraceZeroOff k) =
      ((f4MixPair k).1 : ℝ) • f4RootVec ⟨24 + k.val, by omega⟩ := by
  apply Subtype.ext
  apply h3zornToMatrix.injective
  change h3zornToMatrix ((4 : ℝ) • (f4Inner h3DiagZero₁ (h3TraceZeroOff k) :
      Module.End ℝ (H3Zorn ℝ))) =
    h3zornToMatrix (((f4MixPair k).1 : ℝ) • (f4RootVec ⟨24 + k.val, by omega⟩ :
      Module.End ℝ (H3Zorn ℝ)))
  rw [h3zornToMatrix_four_f4Inner h3DiagZero₁ (h3TraceZeroOff k) _ _
      h3zornToMatrix_two_jordanLmul_diag₁ (h3zornToMatrix_two_jordanLmul_basis ⟨3 + k.val, by omega⟩),
    map_smul, h3zornToMatrix_f4RootVec,
    sparseToMat_eq_of_sparseEq (f4Inner_d1_off_check k), sparseToMat_smul]
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

private theorem four_f4Inner_h3DiagZero₂_off (k : Fin 24) :
    (4 : ℝ) • f4Inner h3DiagZero₂ (h3TraceZeroOff k) =
      ((f4MixPair k).2 : ℝ) • f4RootVec ⟨24 + k.val, by omega⟩ := by
  apply Subtype.ext
  apply h3zornToMatrix.injective
  change h3zornToMatrix ((4 : ℝ) • (f4Inner h3DiagZero₂ (h3TraceZeroOff k) :
      Module.End ℝ (H3Zorn ℝ))) =
    h3zornToMatrix (((f4MixPair k).2 : ℝ) • (f4RootVec ⟨24 + k.val, by omega⟩ :
      Module.End ℝ (H3Zorn ℝ)))
  rw [h3zornToMatrix_four_f4Inner h3DiagZero₂ (h3TraceZeroOff k) _ _
      h3zornToMatrix_two_jordanLmul_diag₂ (h3zornToMatrix_two_jordanLmul_basis ⟨3 + k.val, by omega⟩),
    map_smul, h3zornToMatrix_f4RootVec,
    sparseToMat_eq_of_sparseEq (f4Inner_d2_off_check k), sparseToMat_smul]
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

private theorem f4Inner_h3DiagZero₁_off (k : Fin 24) :
    f4Inner h3DiagZero₁ (h3TraceZeroOff k) =
      (((f4MixPair k).1 : ℝ) / 4) • f4RootVec ⟨24 + k.val, by omega⟩ := by
  have h := congrArg (fun D : F4DerivationCarrier => (1 / 4 : ℝ) • D) (four_f4Inner_h3DiagZero₁_off k)
  simpa [smul_smul, div_eq_mul_inv, mul_comm] using h

private theorem f4Inner_h3DiagZero₂_off (k : Fin 24) :
    f4Inner h3DiagZero₂ (h3TraceZeroOff k) =
      (((f4MixPair k).2 : ℝ) / 4) • f4RootVec ⟨24 + k.val, by omega⟩ := by
  have h := congrArg (fun D : F4DerivationCarrier => (1 / 4 : ℝ) • D) (four_f4Inner_h3DiagZero₂_off k)
  simpa [smul_smul, div_eq_mul_inv, mul_comm] using h

private theorem traceBilin_h3DiagZero₁_off (k : Fin 24) :
    traceBilin h3DiagZero₁.1 (h3TraceZeroOff k).1 = 0 := by
  by_cases hk8 : k.val < 8
  · have h := h3ZornBasis_12 ⟨k.val, hk8⟩
    have heq : (h3TraceZeroOff k : H3Zorn ℝ) =
        (h3EmbedJ12 (zorn_basis ⟨k.val, hk8⟩) : H3Zorn ℝ) := by
      simpa [h3TraceZeroOff_coe, h3EmbedJ12_coe] using h
    change traceBilin h3DiagZero₁.1 (h3TraceZeroOff k : H3Zorn ℝ) = 0
    rw [heq]
    exact traceBilin_h3DiagZero₁_h3EmbedJ12 _
  · by_cases hk16 : k.val < 16
    · have hk' : 11 + (k.val - 8) = 3 + k.val := by omega
      have h := h3ZornBasis_23 ⟨k.val - 8, by omega⟩
      have heq : (h3TraceZeroOff k : H3Zorn ℝ) =
          (h3EmbedJ23 (zorn_basis ⟨k.val - 8, by omega⟩) : H3Zorn ℝ) := by
        simpa [h3TraceZeroOff_coe, h3EmbedJ23_coe, hk'] using h
      change traceBilin h3DiagZero₁.1 (h3TraceZeroOff k : H3Zorn ℝ) = 0
      rw [heq]
      exact traceBilin_h3DiagZero₁_h3EmbedJ23 _
    · have hk' : 19 + (k.val - 16) = 3 + k.val := by omega
      have h := h3ZornBasis_31 ⟨k.val - 16, by omega⟩
      have heq : (h3TraceZeroOff k : H3Zorn ℝ) =
          (h3EmbedJ31 (zorn_basis ⟨k.val - 16, by omega⟩) : H3Zorn ℝ) := by
        simpa [h3TraceZeroOff_coe, h3EmbedJ31_coe, hk'] using h
      change traceBilin h3DiagZero₁.1 (h3TraceZeroOff k : H3Zorn ℝ) = 0
      rw [heq]
      exact traceBilin_h3DiagZero₁_h3EmbedJ31 _

private theorem traceBilin_h3DiagZero₂_off (k : Fin 24) :
    traceBilin h3DiagZero₂.1 (h3TraceZeroOff k).1 = 0 := by
  have h0 : h3DiagZero₂.1.a = 0 ∧ h3DiagZero₂.1.b = 0 ∧ h3DiagZero₂.1.c = 0 :=
    ⟨sub_self _, sub_self _, sub_self _⟩
  have vz0 : ∀ u : VZ, (ZornVectorMatrix.mul (0 : VZ) u).trace = 0 := fun u => by
    simp [ZornVectorMatrix.mul, ZornVectorMatrix.trace, ZornVectorMatrix.zero, ZornVec3.dot]
  by_cases hk8 : k.val < 8
  · have heq : (h3TraceZeroOff k : H3Zorn ℝ) =
        (h3EmbedJ12 (zorn_basis ⟨k.val, hk8⟩) : H3Zorn ℝ) := by
      simpa [h3TraceZeroOff_coe, h3EmbedJ12_coe] using h3ZornBasis_12 ⟨k.val, hk8⟩
    change traceBilin h3DiagZero₂.1 (h3TraceZeroOff k : H3Zorn ℝ) = 0
    rw [heq]
    simp only [traceBilin, h0.1, h0.2.1, h0.2.2, h3EmbedJ12_coe,
      InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12, vz0, mul_zero, add_zero]
  · by_cases hk16 : k.val < 16
    · have hk' : 11 + (k.val - 8) = 3 + k.val := by omega
      have heq : (h3TraceZeroOff k : H3Zorn ℝ) =
          (h3EmbedJ23 (zorn_basis ⟨k.val - 8, by omega⟩) : H3Zorn ℝ) := by
        simpa [h3TraceZeroOff_coe, h3EmbedJ23_coe, hk'] using h3ZornBasis_23 ⟨k.val - 8, by omega⟩
      change traceBilin h3DiagZero₂.1 (h3TraceZeroOff k : H3Zorn ℝ) = 0
      rw [heq]
      simp only [traceBilin, h0.1, h0.2.1, h0.2.2, h3EmbedJ23_coe, embedJ23, vz0, mul_zero, add_zero]
    · have hk' : 19 + (k.val - 16) = 3 + k.val := by omega
      have heq : (h3TraceZeroOff k : H3Zorn ℝ) =
          (h3EmbedJ31 (zorn_basis ⟨k.val - 16, by omega⟩) : H3Zorn ℝ) := by
        simpa [h3TraceZeroOff_coe, h3EmbedJ31_coe, hk'] using h3ZornBasis_31 ⟨k.val - 16, by omega⟩
      change traceBilin h3DiagZero₂.1 (h3TraceZeroOff k : H3Zorn ℝ) = 0
      rw [heq]
      simp only [traceBilin, h0.1, h0.2.1, h0.2.2, h3EmbedJ31_coe, embedJ31, vz0, mul_zero, add_zero]

private theorem h3Mul0_h3DiagZero₁_off (k : Fin 24) :
    h3Mul0 h3DiagZero₁ (h3TraceZeroOff k) =
      (((uMixPair k).1 : ℝ) / 2) • h3TraceZeroOff k := by
  by_cases hk8 : k.val < 8
  · have heq : h3TraceZeroOff k = h3EmbedJ12 (zorn_basis ⟨k.val, hk8⟩) := by
      apply Subtype.ext
      simpa [h3TraceZeroOff_coe, h3EmbedJ12_coe] using h3ZornBasis_12 ⟨k.val, hk8⟩
    rw [heq, h3Mul0_h3DiagZero₁_h3EmbedJ12]
    simp [uMixPair, hk8]
  · by_cases hk16 : k.val < 16
    · have hk' : 11 + (k.val - 8) = 3 + k.val := by omega
      have heq : h3TraceZeroOff k = h3EmbedJ23 (zorn_basis ⟨k.val - 8, by omega⟩) := by
        apply Subtype.ext
        simpa [h3TraceZeroOff_coe, h3EmbedJ23_coe, hk'] using h3ZornBasis_23 ⟨k.val - 8, by omega⟩
      rw [heq, h3Mul0_h3DiagZero₁_h3EmbedJ23]
      simp [uMixPair, hk8, hk16]
    · have hk' : 19 + (k.val - 16) = 3 + k.val := by omega
      have heq : h3TraceZeroOff k = h3EmbedJ31 (zorn_basis ⟨k.val - 16, by omega⟩) := by
        apply Subtype.ext
        simpa [h3TraceZeroOff_coe, h3EmbedJ31_coe, hk'] using h3ZornBasis_31 ⟨k.val - 16, by omega⟩
      rw [heq, h3Mul0_h3DiagZero₁_h3EmbedJ31]
      simp [uMixPair, hk8, hk16]

private theorem h3Mul0_h3DiagZero₂_off (k : Fin 24) :
    h3Mul0 h3DiagZero₂ (h3TraceZeroOff k) =
      (((uMixPair k).2 : ℝ) / 2) • h3TraceZeroOff k := by
  by_cases hk8 : k.val < 8
  · have heq : h3TraceZeroOff k = h3EmbedJ12 (zorn_basis ⟨k.val, hk8⟩) := by
      apply Subtype.ext
      simpa [h3TraceZeroOff_coe, h3EmbedJ12_coe] using h3ZornBasis_12 ⟨k.val, hk8⟩
    rw [heq, h3Mul0_h3DiagZero₂_h3EmbedJ12]
    simp [uMixPair, hk8]
  · by_cases hk16 : k.val < 16
    · have hk' : 11 + (k.val - 8) = 3 + k.val := by omega
      have heq : h3TraceZeroOff k = h3EmbedJ23 (zorn_basis ⟨k.val - 8, by omega⟩) := by
        apply Subtype.ext
        simpa [h3TraceZeroOff_coe, h3EmbedJ23_coe, hk'] using h3ZornBasis_23 ⟨k.val - 8, by omega⟩
      rw [heq, h3Mul0_h3DiagZero₂_h3EmbedJ23]
      simp [uMixPair, hk8, hk16]
    · have hk' : 19 + (k.val - 16) = 3 + k.val := by omega
      have heq : h3TraceZeroOff k = h3EmbedJ31 (zorn_basis ⟨k.val - 16, by omega⟩) := by
        apply Subtype.ext
        simpa [h3TraceZeroOff_coe, h3EmbedJ31_coe, hk'] using h3ZornBasis_31 ⟨k.val - 16, by omega⟩
      rw [heq, h3Mul0_h3DiagZero₂_h3EmbedJ31]
      simp [uMixPair, hk8, hk16]

private theorem f4Act_f4CartanBasis_off (i : Fin 4) (k : Fin 24) :
    f4Act (f4CartanBasis i) (h3TraceZeroOff k) =
      (f4CartanWeight ⟨3 + k.val, by omega⟩ i : ℝ) • h3TraceZeroOff k := by
  apply Subtype.ext
  rw [f4Act_coe, SetLike.val_smul, h3TraceZeroOff_coe, f4CartanBasis_apply_basis]

/-- Hybridized `F₄ ⊕ Mix` root vectors (`48` vectors for `k : Fin 24, sgn ∈ {1, -1}`). -/
def sector4Vec (k : Fin 24) (sgn : ℤ) : SplitE8Lie :=
  embedF4 (f4RootVec ⟨24 + k.val, by omega⟩) +
    (sgn : ℝ) • embedTensor zornE0 (h3TraceZeroOff k)

private theorem cartan8_bracket_sector4Vec (a : Fin 8) (k : Fin 24) (sgn : ℤ)
    (hsgn : sgn = 1 ∨ sgn = -1) :
    ⁅cartan8 a, sector4Vec k sgn⁆ =
      (if a.val < 2 then 0
       else if ha6 : a.val < 6 then
         (f4CartanWeight ⟨3 + k.val, by omega⟩ ⟨a.val - 2, by omega⟩ : ℝ)
       else if a.val = 6 then (sgn * (f4MixPair k).1 : ℤ)
       else (sgn * (f4MixPair k).2 : ℤ)) • sector4Vec k sgn := by
  fin_cases a
  · dsimp only [cartan8, sector4Vec]
    simp only [Nat.zero_lt_succ, ↓reduceIte, lie_add, lie_smul, bracket_g2_f4,
      bracket_g2_tensor, g2CartanBasis_apply_zornE0, map_zero, LinearMap.zero_apply,
      smul_zero, add_zero, zero_smul]
  · dsimp only [cartan8, sector4Vec]
    simp only [Nat.one_lt_two, ↓reduceIte, lie_add, lie_smul, bracket_g2_f4,
      bracket_g2_tensor, g2CartanBasis_apply_zornE0, map_zero, LinearMap.zero_apply,
      smul_zero, add_zero, zero_smul]
  · dsimp only [cartan8, sector4Vec]
    simp only [Nat.reduceLT, ↓reduceIte, ↓reduceDIte, lie_add, lie_smul, bracket_f4_f4,
      bracket_f4_tensor, f4CartanBasis_bracket_f4RootVec, f4RootEigenvalue_ge24_eq,
      f4Act_f4CartanBasis_off, map_smul, smul_add, smul_smul]
    rw [show (⟨(2 : ℕ) - 2, by omega⟩ : Fin 4) = 0 from rfl]; module
  · dsimp only [cartan8, sector4Vec]
    simp only [Nat.reduceLT, ↓reduceIte, ↓reduceDIte, lie_add, lie_smul, bracket_f4_f4,
      bracket_f4_tensor, f4CartanBasis_bracket_f4RootVec, f4RootEigenvalue_ge24_eq,
      f4Act_f4CartanBasis_off, map_smul, smul_add, smul_smul]
    rw [show (⟨(3 : ℕ) - 2, by omega⟩ : Fin 4) = 1 from rfl]; module
  · dsimp only [cartan8, sector4Vec]
    simp only [Nat.reduceLT, ↓reduceIte, ↓reduceDIte, lie_add, lie_smul, bracket_f4_f4,
      bracket_f4_tensor, f4CartanBasis_bracket_f4RootVec, f4RootEigenvalue_ge24_eq,
      f4Act_f4CartanBasis_off, map_smul, smul_add, smul_smul]
    rw [show (⟨(4 : ℕ) - 2, by omega⟩ : Fin 4) = 2 from rfl]; module
  · dsimp only [cartan8, sector4Vec]
    simp only [Nat.reduceLT, ↓reduceIte, ↓reduceDIte, lie_add, lie_smul, bracket_f4_f4,
      bracket_f4_tensor, f4CartanBasis_bracket_f4RootVec, f4RootEigenvalue_ge24_eq,
      f4Act_f4CartanBasis_off, map_smul, smul_add, smul_smul]
    rw [show (⟨(5 : ℕ) - 2, by omega⟩ : Fin 4) = 3 from rfl]; module
  · rcases hsgn with rfl | rfl <;>
    · dsimp only [cartan8, sector4Vec]
      simp only [Nat.reduceLT, ↓reduceIte, ↓reduceDIte,
        lie_add, lie_neg, bracket_tensor_f4, bracket_tensor_tensor,
        f4Act_f4RootVec_ge24_h3DiagZero₁, traceBilin_h3DiagZero₁_off, g2Inner_self,
        zornComm0_self, f4Inner_h3DiagZero₁_off, mul_zero, zero_smul, map_zero, zero_add, add_zero,
        LinearMap.zero_apply, zornBilin_zornE0_self, Int.cast_one, Int.cast_neg,
        one_mul, neg_one_mul, one_smul, neg_smul, smul_smul, smul_add, map_neg, map_smul, neg_neg]
      module
  · rcases hsgn with rfl | rfl <;>
    · dsimp only [cartan8, sector4Vec]
      simp only [Nat.reduceLT, ↓reduceIte, ↓reduceDIte,
        Nat.reduceEqDiff, lie_add, lie_neg, bracket_tensor_f4, bracket_tensor_tensor,
        f4Act_f4RootVec_ge24_h3DiagZero₂, traceBilin_h3DiagZero₂_off, g2Inner_self,
        zornComm0_self, f4Inner_h3DiagZero₂_off, mul_zero, zero_smul, map_zero, zero_add, add_zero,
        LinearMap.zero_apply, zornBilin_zornE0_self, Int.cast_one, Int.cast_neg,
        one_mul, neg_one_mul, one_smul, neg_smul, smul_smul, smul_add, map_neg, map_smul, neg_neg]
      module

private theorem cartan8_bracket_sector5UVec (a : Fin 8) (i : Fin 3) (k : Fin 24) :
    ⁅cartan8 a, embedTensor (zornU i) (h3TraceZeroOff k)⁆ =
      (if ha2 : a.val < 2 then (g2UWeight i ⟨a.val, ha2⟩ : ℝ)
       else if ha6 : a.val < 6 then
         (f4CartanWeight ⟨3 + k.val, by omega⟩ ⟨a.val - 2, by omega⟩ : ℝ)
       else if a.val = 6 then ((uMixPair k).1 : ℝ)
       else ((uMixPair k).2 : ℝ)) • embedTensor (zornU i) (h3TraceZeroOff k) := by
  fin_cases a <;>
    (dsimp only [cartan8]
     simp only [Nat.zero_lt_succ, Nat.one_lt_two, Nat.reduceLT, Nat.reduceEqDiff,
       ↓reduceDIte, ↓reduceIte, bracket_g2_tensor, bracket_f4_tensor, bracket_tensor_tensor,
       g2CartanBasis_apply_zornU_weight, f4Act_f4CartanBasis_off,
       traceBilin_h3DiagZero₁_off, traceBilin_h3DiagZero₂_off, zornBilin_zornE0_zornU,
       zornComm0_zornE0_zornU, h3Mul0_h3DiagZero₁_off, h3Mul0_h3DiagZero₂_off,
       Fin.val_zero, Fin.val_one, g2UWeight, mul_zero, zero_smul, map_zero, zero_add, add_zero,
       LinearMap.smul_apply, map_smul, smul_smul]
     try (first | rfl | (congr 1; ring)))

private theorem cartan8_bracket_sector5VVec (a : Fin 8) (i : Fin 3) (k : Fin 24) :
    ⁅cartan8 a, embedTensor (zornV i) (h3TraceZeroOff k)⁆ =
      (if ha2 : a.val < 2 then (g2VWeight i ⟨a.val, ha2⟩ : ℝ)
       else if ha6 : a.val < 6 then
         (f4CartanWeight ⟨3 + k.val, by omega⟩ ⟨a.val - 2, by omega⟩ : ℝ)
       else if a.val = 6 then (-(uMixPair k).1 : ℝ)
       else (-(uMixPair k).2 : ℝ)) • embedTensor (zornV i) (h3TraceZeroOff k) := by
  fin_cases a <;>
    (dsimp only [cartan8]
     simp only [Nat.zero_lt_succ, Nat.one_lt_two, Nat.reduceLT, Nat.reduceEqDiff,
       ↓reduceDIte, ↓reduceIte, bracket_g2_tensor, bracket_f4_tensor, bracket_tensor_tensor,
       g2CartanBasis_apply_zornV_weight, f4Act_f4CartanBasis_off,
       traceBilin_h3DiagZero₁_off, traceBilin_h3DiagZero₂_off, zornBilin_zornE0_zornV,
       zornComm0_zornE0_zornV, h3Mul0_h3DiagZero₁_off, h3Mul0_h3DiagZero₂_off,
       Fin.val_zero, Fin.val_one, g2VWeight, g2UWeight, mul_zero, zero_smul, map_zero, zero_add,
       add_zero, LinearMap.smul_apply, map_smul, smul_smul, Int.cast_neg]
     try (first | rfl | (congr 1; ring)))

end SectorHelpers

/-! ## 3. 240 Root Vectors, Weights, `E₈` Certificate Bijection & `IsTriangularizable` -/

section RootVectorsAndWeights

/-- All 240 root vectors of `SplitE8Lie` across the 5 simultaneous-eigenvector sectors:
- `0..5`: 6 pure `G₂` long roots
- `6..14`: 9 hybridized `G₂ ⊕ Mix` (`U` branch)
- `15..23`: 9 hybridized `G₂ ⊕ Mix` (`V` branch)
- `24..47`: 24 pure `F₄` long roots
- `48..95`: 48 hybridized `F₄ ⊕ Mix` roots
- `96..167`: 72 pure `Mix` (`U ⊗ off`) roots
- `168..239`: 72 pure `Mix` (`V ⊗ off`) roots. -/
def e8RootVec (r : Fin 240) : SplitE8Lie :=
  if h1 : r.val < 6 then
    embedG2 (g2Param (g2LongIdx ⟨r.val, h1⟩))
  else if h2 : r.val < 15 then
    sector2UVec ⟨(r.val - 6) / 3, by omega⟩ ⟨(r.val - 6) % 3, by omega⟩
  else if h3 : r.val < 24 then
    sector2VVec ⟨(r.val - 15) / 3, by omega⟩ ⟨(r.val - 15) % 3, by omega⟩
  else if h4 : r.val < 48 then
    embedF4 (f4RootVec ⟨r.val - 24, by omega⟩)
  else if h5 : r.val < 96 then
    let k : Fin 24 := ⟨(r.val - 48) / 2, by omega⟩
    let sgn : ℤ := if (r.val - 48) % 2 = 0 then 1 else -1
    sector4Vec k sgn
  else if h6 : r.val < 168 then
    embedTensor (zornU ⟨(r.val - 96) / 24, by omega⟩)
      (h3TraceZeroOff ⟨(r.val - 96) % 24, by omega⟩)
  else
    embedTensor (zornV ⟨(r.val - 168) / 24, by omega⟩)
      (h3TraceZeroOff ⟨(r.val - 168) % 24, by omega⟩)

/-- Exact integer eigenvalues of `cartan8 a` on `e8RootVec r`. -/
def cartan8Weight (r : Fin 240) (a : Fin 8) : ℤ :=
  if h1 : r.val < 6 then
    if ha : a.val < 2 then g2LongWeight ⟨r.val, h1⟩ ⟨a.val, ha⟩ else 0
  else if h2 : r.val < 15 then
    let i : Fin 3 := ⟨(r.val - 6) / 3, by omega⟩
    let s : Fin 3 := ⟨(r.val - 6) % 3, by omega⟩
    if ha : a.val < 2 then g2UWeight i ⟨a.val, ha⟩
    else if a.val < 6 then 0
    else if a.val = 6 then (s2UWeight s).1
    else (s2UWeight s).2
  else if h3 : r.val < 24 then
    let i : Fin 3 := ⟨(r.val - 15) / 3, by omega⟩
    let s : Fin 3 := ⟨(r.val - 15) % 3, by omega⟩
    if ha : a.val < 2 then g2VWeight i ⟨a.val, ha⟩
    else if a.val < 6 then 0
    else if a.val = 6 then (s2VWeight s).1
    else (s2VWeight s).2
  else if h4 : r.val < 48 then
    if a.val < 2 then 0
    else if ha : a.val < 6 then f4RootEigenvalue (f4Perm ⟨a.val - 2, by omega⟩) ⟨r.val - 24, by omega⟩
    else 0
  else if h5 : r.val < 96 then
    let k : Fin 24 := ⟨(r.val - 48) / 2, by omega⟩
    let sgn : ℤ := if (r.val - 48) % 2 = 0 then 1 else -1
    if ha2 : a.val < 2 then 0
    else if ha6 : a.val < 6 then f4CartanWeight ⟨3 + k.val, by omega⟩ ⟨a.val - 2, by omega⟩
    else if a.val = 6 then sgn * (f4MixPair k).1
    else sgn * (f4MixPair k).2
  else if h6 : r.val < 168 then
    let i : Fin 3 := ⟨(r.val - 96) / 24, by omega⟩
    let k : Fin 24 := ⟨(r.val - 96) % 24, by omega⟩
    if ha : a.val < 2 then g2UWeight i ⟨a.val, ha⟩
    else if ha6 : a.val < 6 then f4CartanWeight ⟨3 + k.val, by omega⟩ ⟨a.val - 2, by omega⟩
    else if a.val = 6 then (uMixPair k).1
    else (uMixPair k).2
  else
    let i : Fin 3 := ⟨(r.val - 168) / 24, by omega⟩
    let k : Fin 24 := ⟨(r.val - 168) % 24, by omega⟩
    if ha : a.val < 2 then g2VWeight i ⟨a.val, ha⟩
    else if ha6 : a.val < 6 then f4CartanWeight ⟨3 + k.val, by omega⟩ ⟨a.val - 2, by omega⟩
    else if a.val = 6 then -(uMixPair k).1
    else -(uMixPair k).2

theorem e8RootVec_bracket_cartan8 (a : Fin 8) (r : Fin 240) :
    ⁅cartan8 a, e8RootVec r⁆ = (cartan8Weight r a : ℝ) • e8RootVec r := by
  by_cases h1 : r.val < 6
  · simp only [e8RootVec, cartan8Weight, h1, ↓reduceDIte]
    fin_cases a
    · simp only [cartan8, Nat.zero_lt_succ, ↓reduceDIte, bracket_g2_g2,
        g2CartanBasis_bracket_g2Long, map_smul]; rfl
    · simp only [cartan8, Nat.one_lt_two, ↓reduceDIte, bracket_g2_g2,
        g2CartanBasis_bracket_g2Long, map_smul]; rfl
    · simp only [cartan8, Nat.reduceLT, ↓reduceDIte, bracket_f4_g2, Int.cast_zero, zero_smul]
    · simp only [cartan8, Nat.reduceLT, ↓reduceDIte, bracket_f4_g2, Int.cast_zero, zero_smul]
    · simp only [cartan8, Nat.reduceLT, ↓reduceDIte, bracket_f4_g2, Int.cast_zero, zero_smul]
    · simp only [cartan8, Nat.reduceLT, ↓reduceDIte, bracket_f4_g2, Int.cast_zero, zero_smul]
    · simp only [cartan8, Nat.reduceLT, ↓reduceDIte, bracket_tensor_g2,
        g2Param_g2Long_apply_zornE0, LinearMap.zero_apply, map_zero, neg_zero,
        Int.cast_zero, zero_smul]
    · simp only [cartan8, Nat.reduceLT, ↓reduceDIte, bracket_tensor_g2,
        g2Param_g2Long_apply_zornE0, LinearMap.zero_apply, map_zero, neg_zero,
        Int.cast_zero, zero_smul]
  · by_cases h2 : r.val < 15
    · simp only [e8RootVec, cartan8Weight, h1, h2, ↓reduceDIte]
      rw [cartan8_bracket_sector2UVec]
      by_cases ha2 : a.val < 2
      · simp [ha2]
      · by_cases ha6 : a.val < 6
        · simp [ha2, ha6]
        · by_cases ha6' : a.val = 6 <;> simp [ha2, ha6, ha6']
    · by_cases h3 : r.val < 24
      · simp only [e8RootVec, cartan8Weight, h1, h2, h3, ↓reduceDIte]
        rw [cartan8_bracket_sector2VVec]
        by_cases ha2 : a.val < 2
        · simp [ha2]
        · by_cases ha6 : a.val < 6
          · simp [ha2, ha6]
          · by_cases ha6' : a.val = 6 <;> simp [ha2, ha6, ha6']
      · by_cases h4 : r.val < 48
        · have hfa1 : f4Act (f4RootVec ⟨r.val - 24, by omega⟩) h3DiagZero₁ = 0 :=
            f4Act_f4RootVec_lt24_h3DiagZero₁ ⟨r.val - 24, by omega⟩
          have hfa2 : f4Act (f4RootVec ⟨r.val - 24, by omega⟩) h3DiagZero₂ = 0 :=
            f4Act_f4RootVec_lt24_h3DiagZero₂ ⟨r.val - 24, by omega⟩
          simp only [e8RootVec, cartan8Weight, h1, h2, h3, h4, ↓reduceDIte]
          fin_cases a
          · simp only [cartan8, bracket_g2_f4, Nat.zero_lt_succ, ↓reduceIte,
              Int.cast_zero, zero_smul]
          · simp only [cartan8, bracket_g2_f4, Nat.one_lt_two, ↓reduceIte,
              Int.cast_zero, zero_smul]
          · simp only [cartan8, bracket_f4_f4, f4CartanBasis_bracket_f4RootVec, map_smul,
              Nat.reduceLT, ↓reduceIte, ↓reduceDIte]; rfl
          · simp only [cartan8, bracket_f4_f4, f4CartanBasis_bracket_f4RootVec, map_smul,
              Nat.reduceLT, ↓reduceIte, ↓reduceDIte]; rfl
          · simp only [cartan8, bracket_f4_f4, f4CartanBasis_bracket_f4RootVec, map_smul,
              Nat.reduceLT, ↓reduceIte, ↓reduceDIte]; rfl
          · simp only [cartan8, bracket_f4_f4, f4CartanBasis_bracket_f4RootVec, map_smul,
              Nat.reduceLT, ↓reduceIte, ↓reduceDIte]; rfl
          · simp only [cartan8, bracket_tensor_f4, hfa1,
              Nat.reduceLT, ↓reduceIte, ↓reduceDIte, map_zero, neg_zero,
              Int.cast_zero, zero_smul]
          · simp only [cartan8, bracket_tensor_f4, hfa2,
              Nat.reduceLT, ↓reduceIte, ↓reduceDIte, map_zero, neg_zero,
              Int.cast_zero, zero_smul]
        · by_cases h5 : r.val < 96
          · simp only [e8RootVec, cartan8Weight, h1, h2, h3, h4, h5, ↓reduceDIte]
            rw [cartan8_bracket_sector4Vec _ _ _ (by split_ifs <;> simp)]
            by_cases ha2 : a.val < 2
            · simp [ha2]
            · by_cases ha6 : a.val < 6
              · simp [ha2, ha6]
              · by_cases ha6' : a.val = 6 <;> simp [ha2, ha6, ha6']
          · by_cases h6 : r.val < 168
            · simp only [e8RootVec, cartan8Weight, h1, h2, h3, h4, h5, h6, ↓reduceDIte]
              rw [cartan8_bracket_sector5UVec]
              by_cases ha2 : a.val < 2
              · simp [ha2]
              · by_cases ha6 : a.val < 6
                · simp [ha2, ha6]
                · by_cases ha6' : a.val = 6 <;> simp [ha2, ha6, ha6']
            · simp only [e8RootVec, cartan8Weight, h1, h2, h3, h4, h5, h6, ↓reduceDIte]
              rw [cartan8_bracket_sector5VVec]
              by_cases ha2 : a.val < 2
              · simp [ha2]
              · by_cases ha6 : a.val < 6
                · simp [ha2, ha6]
                · by_cases ha6' : a.val = 6 <;> simp [ha2, ha6, ha6']

private theorem embedTensor_zornU_off_ne_zero (i : Fin 3) (k : Fin 24) :
    embedTensor (zornU i) (h3TraceZeroOff k) ≠ 0 := by
  let f1 : splitOctonionTraceZero →ₗ[ℝ] ℝ :=
    { toFun := fun a => a.1.v i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let f2 : h3TraceZero →ₗ[ℝ] ℝ :=
    { toFun := fun x => h3ZornCoordinate x.1 ⟨3 + k.val, by omega⟩
      map_add' := fun x y => h3ZornCoordinate_add x.1 y.1 _
      map_smul' := fun r x => h3ZornCoordinate_smul r x.1 _ }
  let f : MixedCarrier →ₗ[ℝ] ℝ :=
    TensorProduct.lift (LinearMap.lsmul ℝ ℝ |>.compl₂ f2 |>.comp f1)
  intro h0
  have hm := congrArg (fun X => f (projMixed X)) h0
  have hfv : f (projMixed (embedTensor (zornU i) (h3TraceZeroOff k))) = 1 := by
    change (zornU i).1.v i * h3ZornCoordinate (h3ZornBasis ⟨3 + k.val, by omega⟩)
        ⟨3 + k.val, by omega⟩ = 1
    rw [h3ZornCoordinate_basis_self]
    simp [zornU, ZornVectorMatrix.U, ZornVec3.basis]
  rw [hfv, map_zero, map_zero] at hm
  exact one_ne_zero hm

private theorem embedTensor_zornV_off_ne_zero (i : Fin 3) (k : Fin 24) :
    embedTensor (zornV i) (h3TraceZeroOff k) ≠ 0 := by
  let f1 : splitOctonionTraceZero →ₗ[ℝ] ℝ :=
    { toFun := fun a => a.1.w i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let f2 : h3TraceZero →ₗ[ℝ] ℝ :=
    { toFun := fun x => h3ZornCoordinate x.1 ⟨3 + k.val, by omega⟩
      map_add' := fun x y => h3ZornCoordinate_add x.1 y.1 _
      map_smul' := fun r x => h3ZornCoordinate_smul r x.1 _ }
  let f : MixedCarrier →ₗ[ℝ] ℝ :=
    TensorProduct.lift (LinearMap.lsmul ℝ ℝ |>.compl₂ f2 |>.comp f1)
  intro h0
  have hm := congrArg (fun X => f (projMixed X)) h0
  have hfv : f (projMixed (embedTensor (zornV i) (h3TraceZeroOff k))) = 1 := by
    change (zornV i).1.w i * h3ZornCoordinate (h3ZornBasis ⟨3 + k.val, by omega⟩)
        ⟨3 + k.val, by omega⟩ = 1
    rw [h3ZornCoordinate_basis_self]
    simp [zornV, ZornVectorMatrix.V, ZornVec3.basis]
  rw [hfv, map_zero, map_zero] at hm
  exact one_ne_zero hm

private theorem projG2_sector2UVec (i s : Fin 3) :
    projG2 (sector2UVec i s) = g2Inner zornE0 (zornU i) := by
  fin_cases s <;>
    simp [sector2UVec, projG2_mk, embedG2_apply, embedTensor_apply, embedMixed_apply]

private theorem projG2_sector2VVec (i s : Fin 3) :
    projG2 (sector2VVec i s) = g2Inner zornE0 (zornV i) := by
  fin_cases s <;>
    simp [sector2VVec, projG2_mk, embedG2_apply, embedTensor_apply, embedMixed_apply]

theorem e8RootVec_ne_zero (r : Fin 240) : e8RootVec r ≠ 0 := by
  by_cases h1 : r.val < 6
  · simp only [e8RootVec, h1, ↓reduceDIte]
    intro h0
    exact g2Param_ne_zero _ (congrArg projG2 h0)
  · by_cases h2 : r.val < 15
    · simp only [e8RootVec, h1, h2, ↓reduceDIte]
      intro h0
      have hg := congrArg projG2 h0
      rw [projG2_sector2UVec, map_zero] at hg
      exact g2Inner_zornE0_zornU_ne_zero _ hg
    · by_cases h3 : r.val < 24
      · simp only [e8RootVec, h1, h2, h3, ↓reduceDIte]
        intro h0
        have hg := congrArg projG2 h0
        rw [projG2_sector2VVec, map_zero] at hg
        exact g2Inner_zornE0_zornV_ne_zero _ hg
      · by_cases h4 : r.val < 48
        · simp only [e8RootVec, h1, h2, h3, h4, ↓reduceDIte]
          intro h0
          exact f4RootVec_ne_zero _ (congrArg projF4 h0)
        · by_cases h5 : r.val < 96
          · simp only [e8RootVec, h1, h2, h3, h4, h5, ↓reduceDIte]
            intro h0
            have hf := congrArg projF4 h0
            rw [sector4Vec, map_add, map_smul] at hf
            simp only [projF4_mk, embedF4_apply, embedTensor_apply, embedMixed_apply,
              smul_zero, add_zero] at hf
            exact f4RootVec_ne_zero _ hf
          · by_cases h6 : r.val < 168
            · simp only [e8RootVec, h1, h2, h3, h4, h5, h6, ↓reduceDIte]
              exact embedTensor_zornU_off_ne_zero _ _
            · simp only [e8RootVec, h1, h2, h3, h4, h5, h6, ↓reduceDIte]
              exact embedTensor_zornV_off_ne_zero _ _

private def e8NzBlockCheck (offset : ℕ) (h : offset + 24 ≤ 240) : Bool :=
  (List.finRange 24).all fun k =>
    let r : Fin 240 := ⟨offset + k.val, by omega⟩
    (List.finRange 8).any fun a => cartan8Weight r a != 0

private theorem e8NzBlock_0 : e8NzBlockCheck 0 (by decide) = true := by decide
private theorem e8NzBlock_1 : e8NzBlockCheck 24 (by decide) = true := by decide
private theorem e8NzBlock_2 : e8NzBlockCheck 48 (by decide) = true := by decide
private theorem e8NzBlock_3 : e8NzBlockCheck 72 (by decide) = true := by decide
private theorem e8NzBlock_4 : e8NzBlockCheck 96 (by decide) = true := by decide
private theorem e8NzBlock_5 : e8NzBlockCheck 120 (by decide) = true := by decide
private theorem e8NzBlock_6 : e8NzBlockCheck 144 (by decide) = true := by decide
private theorem e8NzBlock_7 : e8NzBlockCheck 168 (by decide) = true := by decide
private theorem e8NzBlock_8 : e8NzBlockCheck 192 (by decide) = true := by decide
private theorem e8NzBlock_9 : e8NzBlockCheck 216 (by decide) = true := by decide

theorem cartan8Weight_ne_zero (r : Fin 240) : ∃ a : Fin 8, cartan8Weight r a ≠ 0 := by
  have hb : ∀ (off : ℕ) (h : off + 24 ≤ 240), e8NzBlockCheck off h = true →
      ∀ k : Fin 24, ∃ a : Fin 8, cartan8Weight ⟨off + k.val, by omega⟩ a ≠ 0 := by
    intro off h hchk k
    dsimp [e8NzBlockCheck] at hchk
    simp only [List.all_eq_true, List.mem_finRange, true_implies, List.any_eq_true,
      bne_iff_ne, ne_eq] at hchk
    obtain ⟨a, _, ha⟩ := hchk k
    exact ⟨a, ha⟩
  by_cases h0 : r.val < 24
  · have heq : (⟨0 + (⟨r.val, h0⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
      Fin.ext (by dsimp; omega)
    simpa [heq] using hb 0 (by decide) e8NzBlock_0 ⟨r.val, h0⟩
  · by_cases h1 : r.val < 48
    · have hk : r.val - 24 < 24 := by omega
      have heq : (⟨24 + (⟨r.val - 24, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
        Fin.ext (by dsimp; omega)
      simpa [heq] using hb 24 (by decide) e8NzBlock_1 ⟨r.val - 24, hk⟩
    · by_cases h2 : r.val < 72
      · have hk : r.val - 48 < 24 := by omega
        have heq : (⟨48 + (⟨r.val - 48, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
          Fin.ext (by dsimp; omega)
        simpa [heq] using hb 48 (by decide) e8NzBlock_2 ⟨r.val - 48, hk⟩
      · by_cases h3 : r.val < 96
        · have hk : r.val - 72 < 24 := by omega
          have heq : (⟨72 + (⟨r.val - 72, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
            Fin.ext (by dsimp; omega)
          simpa [heq] using hb 72 (by decide) e8NzBlock_3 ⟨r.val - 72, hk⟩
        · by_cases h4 : r.val < 120
          · have hk : r.val - 96 < 24 := by omega
            have heq : (⟨96 + (⟨r.val - 96, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
              Fin.ext (by dsimp; omega)
            simpa [heq] using hb 96 (by decide) e8NzBlock_4 ⟨r.val - 96, hk⟩
          · by_cases h5 : r.val < 144
            · have hk : r.val - 120 < 24 := by omega
              have heq : (⟨120 + (⟨r.val - 120, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                Fin.ext (by dsimp; omega)
              simpa [heq] using hb 120 (by decide) e8NzBlock_5 ⟨r.val - 120, hk⟩
            · by_cases h6 : r.val < 168
              · have hk : r.val - 144 < 24 := by omega
                have heq : (⟨144 + (⟨r.val - 144, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                  Fin.ext (by dsimp; omega)
                simpa [heq] using hb 144 (by decide) e8NzBlock_6 ⟨r.val - 144, hk⟩
              · by_cases h7 : r.val < 192
                · have hk : r.val - 168 < 24 := by omega
                  have heq : (⟨168 + (⟨r.val - 168, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                    Fin.ext (by dsimp; omega)
                  simpa [heq] using hb 168 (by decide) e8NzBlock_7 ⟨r.val - 168, hk⟩
                · by_cases h8 : r.val < 216
                  · have hk : r.val - 192 < 24 := by omega
                    have heq : (⟨192 + (⟨r.val - 192, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                      Fin.ext (by dsimp; omega)
                    simpa [heq] using hb 192 (by decide) e8NzBlock_8 ⟨r.val - 192, hk⟩
                  · have hk : r.val - 216 < 24 := by omega
                    have heq : (⟨216 + (⟨r.val - 216, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                      Fin.ext (by dsimp; omega)
                    simpa [heq] using hb 216 (by decide) e8NzBlock_9 ⟨r.val - 216, hk⟩

/-- Integer change-of-basis numerator matrix (`6 * e8RootCoord r j = ∑ a, e8CoordNum j a * cartan8Weight r a`). -/
def e8CoordNum : Fin 8 → Fin 8 → ℤ :=
  ![ ![0,  0, 0,  0,  0,  0,  6, 0],
     ![0,  0, 0, -6, -3, -6,  9, 3],
     ![0,  0, 6,  6,  3,  3, 12, 3],
     ![0,  0, 6,  0,  0,  0, 18, 6],
     ![0,  0, 6,  6,  0,  3, 15, 6],
     ![0,  0, 0,  0,  0,  0, 12, 6],
     ![4, -2, 0,  0,  0,  0,  8, 4],
     ![2,  2, 0,  0,  0,  0,  4, 2] ]

/-- Bourbaki `E₈` simple-root coordinates of the 240 root vectors. -/
def e8RootCoord (r : Fin 240) (j : Fin 8) : ℤ :=
  (∑ a : Fin 8, e8CoordNum j a * cartan8Weight r a) / 6

private def e8RootCertIdx (r : Fin 240) : Fin 240 :=
  match r.val with
  | 0 => 36 | 1 => 22 | 2 => 21 | 3 => 6 | 4 => 7 | 5 => 20 | 6 => 238 | 7 => 196 | 8 => 127 | 9 => 234
  | 10 => 209 | 11 => 152 | 12 => 236 | 13 => 203 | 14 => 140 | 15 => 239 | 16 => 192 | 17 => 116 | 18 => 235 | 19 => 206
  | 20 => 141 | 21 => 237 | 22 => 200 | 23 => 129 | 24 => 41 | 25 => 13 | 26 => 2 | 27 => 29 | 28 => 25 | 29 => 10
  | 30 => 16 | 31 => 30 | 32 => 70 | 33 => 55 | 34 => 44 | 35 => 26 | 36 => 57 | 37 => 3 | 38 => 11 | 39 => 42
  | 40 => 14 | 41 => 1 | 42 => 4 | 43 => 15 | 44 => 27 | 45 => 40 | 46 => 28 | 47 => 12 | 48 => 225 | 49 => 226
  | 50 => 212 | 51 => 233 | 52 => 230 | 53 => 218 | 54 => 228 | 55 => 222 | 56 => 232 | 57 => 214 | 58 => 216 | 59 => 231
  | 60 => 220 | 61 => 229 | 62 => 224 | 63 => 227 | 64 => 52 | 65 => 38 | 66 => 93 | 67 => 0 | 68 => 23 | 69 => 67
  | 70 => 37 | 71 => 53 | 72 => 8 | 73 => 82 | 74 => 79 | 75 => 9 | 76 => 65 | 77 => 24 | 78 => 51 | 79 => 39
  | 80 => 210 | 81 => 208 | 82 => 223 | 83 => 187 | 84 => 199 | 85 => 217 | 86 => 205 | 87 => 213 | 88 => 191 | 89 => 221
  | 90 => 219 | 91 => 195 | 92 => 215 | 93 => 202 | 94 => 211 | 95 => 207 | 96 => 77 | 97 => 35 | 98 => 105 | 99 => 91
  | 100 => 117 | 101 => 49 | 102 => 63 | 103 => 75 | 104 => 165 | 105 => 188 | 106 => 144 | 107 => 154 | 108 => 133 | 109 => 180
  | 110 => 172 | 111 => 163 | 112 => 126 | 113 => 85 | 114 => 149 | 115 => 138 | 116 => 159 | 117 => 100 | 118 => 113 | 119 => 124
  | 120 => 45 | 121 => 5 | 122 => 73 | 123 => 58 | 124 => 89 | 125 => 17 | 126 => 31 | 127 => 43 | 128 => 183 | 129 => 204
  | 130 => 167 | 131 => 175 | 132 => 157 | 133 => 198 | 134 => 190 | 135 => 182 | 136 => 98 | 137 => 54 | 138 => 122 | 139 => 110
  | 140 => 135 | 141 => 68 | 142 => 83 | 143 => 97 | 144 => 61 | 145 => 19 | 146 => 90 | 147 => 74 | 148 => 104 | 149 => 33
  | 150 => 47 | 151 => 59 | 152 => 174 | 153 => 197 | 154 => 156 | 155 => 166 | 156 => 146 | 157 => 189 | 158 => 181 | 159 => 173
  | 160 => 112 | 161 => 69 | 162 => 136 | 163 => 123 | 164 => 147 | 165 => 84 | 166 => 99 | 167 => 111 | 168 => 88 | 169 => 128
  | 170 => 64 | 171 => 78 | 172 => 50 | 173 => 115 | 174 => 103 | 175 => 92 | 176 => 158 | 177 => 125 | 178 => 176 | 179 => 168
  | 180 => 184 | 181 => 137 | 182 => 148 | 183 => 160 | 184 => 132 | 185 => 164 | 186 => 109 | 187 => 121 | 188 => 96 | 189 => 155
  | 190 => 145 | 191 => 134 | 192 => 56 | 193 => 101 | 194 => 32 | 195 => 46 | 196 => 18 | 197 => 86 | 198 => 71 | 199 => 60
  | 200 => 178 | 201 => 151 | 202 => 194 | 203 => 186 | 204 => 201 | 205 => 162 | 206 => 171 | 207 => 179 | 208 => 106 | 209 => 142
  | 210 => 80 | 211 => 94 | 212 => 66 | 213 => 130 | 214 => 118 | 215 => 107 | 216 => 72 | 217 => 114 | 218 => 48 | 219 => 62
  | 220 => 34 | 221 => 102 | 222 => 87 | 223 => 76 | 224 => 169 | 225 => 139 | 226 => 185 | 227 => 177 | 228 => 193 | 229 => 150
  | 230 => 161 | 231 => 170 | 232 => 119 | 233 => 153 | 234 => 95 | 235 => 108 | 236 => 81 | 237 => 143 | 238 => 131 | _ => 120

private def e8CertInvIdx (c : Fin 240) : Fin 240 :=
  match c.val with
  | 0 => 67 | 1 => 41 | 2 => 26 | 3 => 37 | 4 => 42 | 5 => 121 | 6 => 3 | 7 => 4 | 8 => 72 | 9 => 75
  | 10 => 29 | 11 => 38 | 12 => 47 | 13 => 25 | 14 => 40 | 15 => 43 | 16 => 30 | 17 => 125 | 18 => 196 | 19 => 145
  | 20 => 5 | 21 => 2 | 22 => 1 | 23 => 68 | 24 => 77 | 25 => 28 | 26 => 35 | 27 => 44 | 28 => 46 | 29 => 27
  | 30 => 31 | 31 => 126 | 32 => 194 | 33 => 149 | 34 => 220 | 35 => 97 | 36 => 0 | 37 => 70 | 38 => 65 | 39 => 79
  | 40 => 45 | 41 => 24 | 42 => 39 | 43 => 127 | 44 => 34 | 45 => 120 | 46 => 195 | 47 => 150 | 48 => 218 | 49 => 101
  | 50 => 172 | 51 => 78 | 52 => 64 | 53 => 71 | 54 => 137 | 55 => 33 | 56 => 192 | 57 => 36 | 58 => 123 | 59 => 151
  | 60 => 199 | 61 => 144 | 62 => 219 | 63 => 102 | 64 => 170 | 65 => 76 | 66 => 212 | 67 => 69 | 68 => 141 | 69 => 161
  | 70 => 32 | 71 => 198 | 72 => 216 | 73 => 122 | 74 => 147 | 75 => 103 | 76 => 223 | 77 => 96 | 78 => 171 | 79 => 74
  | 80 => 210 | 81 => 236 | 82 => 73 | 83 => 142 | 84 => 165 | 85 => 113 | 86 => 197 | 87 => 222 | 88 => 168 | 89 => 124
  | 90 => 146 | 91 => 99 | 92 => 175 | 93 => 66 | 94 => 211 | 95 => 234 | 96 => 188 | 97 => 143 | 98 => 136 | 99 => 166
  | 100 => 117 | 101 => 193 | 102 => 221 | 103 => 174 | 104 => 148 | 105 => 98 | 106 => 208 | 107 => 215 | 108 => 235 | 109 => 186
  | 110 => 139 | 111 => 167 | 112 => 160 | 113 => 118 | 114 => 217 | 115 => 173 | 116 => 17 | 117 => 100 | 118 => 214 | 119 => 232
  | 120 => 239 | 121 => 187 | 122 => 138 | 123 => 163 | 124 => 119 | 125 => 177 | 126 => 112 | 127 => 8 | 128 => 169 | 129 => 23
  | 130 => 213 | 131 => 238 | 132 => 184 | 133 => 108 | 134 => 191 | 135 => 140 | 136 => 162 | 137 => 181 | 138 => 115 | 139 => 225
  | 140 => 14 | 141 => 20 | 142 => 209 | 143 => 237 | 144 => 106 | 145 => 190 | 146 => 156 | 147 => 164 | 148 => 182 | 149 => 114
  | 150 => 229 | 151 => 201 | 152 => 11 | 153 => 233 | 154 => 107 | 155 => 189 | 156 => 154 | 157 => 132 | 158 => 176 | 159 => 116
  | 160 => 183 | 161 => 230 | 162 => 205 | 163 => 111 | 164 => 185 | 165 => 104 | 166 => 155 | 167 => 130 | 168 => 179 | 169 => 224
  | 170 => 231 | 171 => 206 | 172 => 110 | 173 => 159 | 174 => 152 | 175 => 131 | 176 => 178 | 177 => 227 | 178 => 200 | 179 => 207
  | 180 => 109 | 181 => 158 | 182 => 135 | 183 => 128 | 184 => 180 | 185 => 226 | 186 => 203 | 187 => 83 | 188 => 105 | 189 => 157
  | 190 => 134 | 191 => 88 | 192 => 16 | 193 => 228 | 194 => 202 | 195 => 91 | 196 => 7 | 197 => 153 | 198 => 133 | 199 => 84
  | 200 => 22 | 201 => 204 | 202 => 93 | 203 => 13 | 204 => 129 | 205 => 86 | 206 => 19 | 207 => 95 | 208 => 81 | 209 => 10
  | 210 => 80 | 211 => 94 | 212 => 50 | 213 => 87 | 214 => 57 | 215 => 92 | 216 => 58 | 217 => 85 | 218 => 53 | 219 => 90
  | 220 => 60 | 221 => 89 | 222 => 55 | 223 => 82 | 224 => 62 | 225 => 48 | 226 => 49 | 227 => 63 | 228 => 54 | 229 => 61
  | 230 => 52 | 231 => 59 | 232 => 56 | 233 => 51 | 234 => 9 | 235 => 18 | 236 => 12 | 237 => 21 | 238 => 6 | _ => 15

private def e8CertBlockCheck (offset : ℕ) (h : offset + 24 ≤ 240) : Bool :=
  (List.finRange 24).all fun k =>
    let r : Fin 240 := ⟨offset + k.val, by omega⟩
    List.ofFn (e8RootCoord r) == List.ofFn (e8Certificate.root (e8RootCertIdx r).val)

private theorem e8CertBlock_0 : e8CertBlockCheck 0 (by decide) = true := by decide
private theorem e8CertBlock_1 : e8CertBlockCheck 24 (by decide) = true := by decide
private theorem e8CertBlock_2 : e8CertBlockCheck 48 (by decide) = true := by decide
private theorem e8CertBlock_3 : e8CertBlockCheck 72 (by decide) = true := by decide
private theorem e8CertBlock_4 : e8CertBlockCheck 96 (by decide) = true := by decide
private theorem e8CertBlock_5 : e8CertBlockCheck 120 (by decide) = true := by decide
private theorem e8CertBlock_6 : e8CertBlockCheck 144 (by decide) = true := by decide
private theorem e8CertBlock_7 : e8CertBlockCheck 168 (by decide) = true := by decide
private theorem e8CertBlock_8 : e8CertBlockCheck 192 (by decide) = true := by decide
private theorem e8CertBlock_9 : e8CertBlockCheck 216 (by decide) = true := by decide

theorem e8RootCoord_eq_cert (r : Fin 240) :
    e8RootCoord r = e8Certificate.root (e8RootCertIdx r).val := by
  apply List.ofFn_injective
  have hb : ∀ (off : ℕ) (h : off + 24 ≤ 240), e8CertBlockCheck off h = true →
      ∀ k : Fin 24,
        List.ofFn (e8RootCoord ⟨off + k.val, by omega⟩) =
          List.ofFn (e8Certificate.root (e8RootCertIdx ⟨off + k.val, by omega⟩).val) := by
    intro off h hchk k
    dsimp [e8CertBlockCheck] at hchk
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
    exact hchk k
  by_cases h0 : r.val < 24
  · have heq : (⟨0 + (⟨r.val, h0⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
      Fin.ext (by dsimp; omega)
    have hres := hb 0 (by decide) e8CertBlock_0 ⟨r.val, h0⟩
    rwa [heq] at hres
  · by_cases h1 : r.val < 48
    · have hk : r.val - 24 < 24 := by omega
      have heq : (⟨24 + (⟨r.val - 24, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
        Fin.ext (by dsimp; omega)
      have hres := hb 24 (by decide) e8CertBlock_1 ⟨r.val - 24, hk⟩
      rwa [heq] at hres
    · by_cases h2 : r.val < 72
      · have hk : r.val - 48 < 24 := by omega
        have heq : (⟨48 + (⟨r.val - 48, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
          Fin.ext (by dsimp; omega)
        have hres := hb 48 (by decide) e8CertBlock_2 ⟨r.val - 48, hk⟩
        rwa [heq] at hres
      · by_cases h3 : r.val < 96
        · have hk : r.val - 72 < 24 := by omega
          have heq : (⟨72 + (⟨r.val - 72, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
            Fin.ext (by dsimp; omega)
          have hres := hb 72 (by decide) e8CertBlock_3 ⟨r.val - 72, hk⟩
          rwa [heq] at hres
        · by_cases h4 : r.val < 120
          · have hk : r.val - 96 < 24 := by omega
            have heq : (⟨96 + (⟨r.val - 96, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
              Fin.ext (by dsimp; omega)
            have hres := hb 96 (by decide) e8CertBlock_4 ⟨r.val - 96, hk⟩
            rwa [heq] at hres
          · by_cases h5 : r.val < 144
            · have hk : r.val - 120 < 24 := by omega
              have heq : (⟨120 + (⟨r.val - 120, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                Fin.ext (by dsimp; omega)
              have hres := hb 120 (by decide) e8CertBlock_5 ⟨r.val - 120, hk⟩
              rwa [heq] at hres
            · by_cases h6 : r.val < 168
              · have hk : r.val - 144 < 24 := by omega
                have heq : (⟨144 + (⟨r.val - 144, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                  Fin.ext (by dsimp; omega)
                have hres := hb 144 (by decide) e8CertBlock_6 ⟨r.val - 144, hk⟩
                rwa [heq] at hres
              · by_cases h7 : r.val < 192
                · have hk : r.val - 168 < 24 := by omega
                  have heq : (⟨168 + (⟨r.val - 168, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                    Fin.ext (by dsimp; omega)
                  have hres := hb 168 (by decide) e8CertBlock_7 ⟨r.val - 168, hk⟩
                  rwa [heq] at hres
                · by_cases h8 : r.val < 216
                  · have hk : r.val - 192 < 24 := by omega
                    have heq : (⟨192 + (⟨r.val - 192, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                      Fin.ext (by dsimp; omega)
                    have hres := hb 192 (by decide) e8CertBlock_8 ⟨r.val - 192, hk⟩
                    rwa [heq] at hres
                  · have hk : r.val - 216 < 24 := by omega
                    have heq : (⟨216 + (⟨r.val - 216, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                      Fin.ext (by dsimp; omega)
                    have hres := hb 216 (by decide) e8CertBlock_9 ⟨r.val - 216, hk⟩
                    rwa [heq] at hres

private theorem e8Certificate_roots_length : e8Certificate.roots.length = 240 :=
  Tag.rootCertificate_length .E8

theorem e8RootCoord_isRoot (r : Fin 240) : IsRoot .E8 (e8RootCoord r) := by
  rw [e8RootCoord_eq_cert r]
  exact RootCertificate.isRoot_root e8Certificate_check (e8RootCertIdx r).val
    (Nat.lt_of_lt_of_eq (e8RootCertIdx r).isLt e8Certificate_roots_length.symm)

private def e8InvBlockCheck (offset : ℕ) (h : offset + 24 ≤ 240) : Bool :=
  (List.finRange 24).all fun k =>
    let r : Fin 240 := ⟨offset + k.val, by omega⟩
    e8CertInvIdx (e8RootCertIdx r) == r

private theorem e8InvBlock_0 : e8InvBlockCheck 0 (by decide) = true := by decide
private theorem e8InvBlock_1 : e8InvBlockCheck 24 (by decide) = true := by decide
private theorem e8InvBlock_2 : e8InvBlockCheck 48 (by decide) = true := by decide
private theorem e8InvBlock_3 : e8InvBlockCheck 72 (by decide) = true := by decide
private theorem e8InvBlock_4 : e8InvBlockCheck 96 (by decide) = true := by decide
private theorem e8InvBlock_5 : e8InvBlockCheck 120 (by decide) = true := by decide
private theorem e8InvBlock_6 : e8InvBlockCheck 144 (by decide) = true := by decide
private theorem e8InvBlock_7 : e8InvBlockCheck 168 (by decide) = true := by decide
private theorem e8InvBlock_8 : e8InvBlockCheck 192 (by decide) = true := by decide
private theorem e8InvBlock_9 : e8InvBlockCheck 216 (by decide) = true := by decide

private theorem e8CertInvIdx_left_inv (r : Fin 240) : e8CertInvIdx (e8RootCertIdx r) = r := by
  have hb : ∀ (off : ℕ) (h : off + 24 ≤ 240), e8InvBlockCheck off h = true →
      ∀ k : Fin 24, e8CertInvIdx (e8RootCertIdx ⟨off + k.val, by omega⟩) =
        ⟨off + k.val, by omega⟩ := by
    intro off h hchk k
    dsimp [e8InvBlockCheck] at hchk
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
    exact hchk k
  by_cases h0 : r.val < 24
  · have heq : (⟨0 + (⟨r.val, h0⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
      Fin.ext (by dsimp; omega)
    simpa [heq] using hb 0 (by decide) e8InvBlock_0 ⟨r.val, h0⟩
  · by_cases h1 : r.val < 48
    · have hk : r.val - 24 < 24 := by omega
      have heq : (⟨24 + (⟨r.val - 24, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
        Fin.ext (by dsimp; omega)
      simpa [heq] using hb 24 (by decide) e8InvBlock_1 ⟨r.val - 24, hk⟩
    · by_cases h2 : r.val < 72
      · have hk : r.val - 48 < 24 := by omega
        have heq : (⟨48 + (⟨r.val - 48, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
          Fin.ext (by dsimp; omega)
        simpa [heq] using hb 48 (by decide) e8InvBlock_2 ⟨r.val - 48, hk⟩
      · by_cases h3 : r.val < 96
        · have hk : r.val - 72 < 24 := by omega
          have heq : (⟨72 + (⟨r.val - 72, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
            Fin.ext (by dsimp; omega)
          simpa [heq] using hb 72 (by decide) e8InvBlock_3 ⟨r.val - 72, hk⟩
        · by_cases h4 : r.val < 120
          · have hk : r.val - 96 < 24 := by omega
            have heq : (⟨96 + (⟨r.val - 96, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
              Fin.ext (by dsimp; omega)
            simpa [heq] using hb 96 (by decide) e8InvBlock_4 ⟨r.val - 96, hk⟩
          · by_cases h5 : r.val < 144
            · have hk : r.val - 120 < 24 := by omega
              have heq : (⟨120 + (⟨r.val - 120, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                Fin.ext (by dsimp; omega)
              simpa [heq] using hb 120 (by decide) e8InvBlock_5 ⟨r.val - 120, hk⟩
            · by_cases h6 : r.val < 168
              · have hk : r.val - 144 < 24 := by omega
                have heq : (⟨144 + (⟨r.val - 144, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                  Fin.ext (by dsimp; omega)
                simpa [heq] using hb 144 (by decide) e8InvBlock_6 ⟨r.val - 144, hk⟩
              · by_cases h7 : r.val < 192
                · have hk : r.val - 168 < 24 := by omega
                  have heq : (⟨168 + (⟨r.val - 168, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                    Fin.ext (by dsimp; omega)
                  simpa [heq] using hb 168 (by decide) e8InvBlock_7 ⟨r.val - 168, hk⟩
                · by_cases h8 : r.val < 216
                  · have hk : r.val - 192 < 24 := by omega
                    have heq : (⟨192 + (⟨r.val - 192, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                      Fin.ext (by dsimp; omega)
                    simpa [heq] using hb 192 (by decide) e8InvBlock_8 ⟨r.val - 192, hk⟩
                  · have hk : r.val - 216 < 24 := by omega
                    have heq : (⟨216 + (⟨r.val - 216, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r :=
                      Fin.ext (by dsimp; omega)
                    simpa [heq] using hb 216 (by decide) e8InvBlock_9 ⟨r.val - 216, hk⟩

private theorem e8RootCertIdx_injective : Function.Injective e8RootCertIdx :=
  Function.HasLeftInverse.injective ⟨e8CertInvIdx, e8CertInvIdx_left_inv⟩

private theorem e8Certificate_root_injective :
    Function.Injective (fun c : Fin 240 => e8Certificate.root c.val) := by
  intro c₁ c₂ heq
  have hn := e8Certificate_checkNodup
  simp only [RootCertificate.checkNodup, decide_eq_true_eq] at hn
  have h1 := (List.nodup_map_iff_inj_on List.nodup_range).mp hn c₁.val
    (List.mem_range.mpr (by rw [e8Certificate_roots_length]; exact c₁.isLt))
    c₂.val (List.mem_range.mpr (by rw [e8Certificate_roots_length]; exact c₂.isLt))
    (congrArg List.ofFn heq)
  exact Fin.ext h1

theorem e8RootCoord_injective : Function.Injective e8RootCoord := by
  intro r₁ r₂ heq
  rw [e8RootCoord_eq_cert r₁, e8RootCoord_eq_cert r₂] at heq
  exact e8RootCertIdx_injective (e8Certificate_root_injective heq)

/-- Canonical bijection between the 240 `SplitE8Lie` root vectors and `CFSGPort` `E₈` roots. -/
def e8RootEquiv : Fin 240 ≃ {v : Fin 8 → ℤ // IsRoot .E8 v} :=
  letI : Fintype {v : Fin 8 → ℤ // IsRoot .E8 v} :=
    (inferInstance : Fintype {v : Fin (Tag.rank .E8) → ℤ // IsRoot .E8 v})
  Equiv.ofBijective (fun r => ⟨e8RootCoord r, e8RootCoord_isRoot r⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun _ _ h => e8RootCoord_injective (congrArg Subtype.val h),
       by rw [Fintype.card_fin]; exact (card_isRoot .E8).symm⟩)

theorem cartan8Weight_eq_imp {r₁ r₂ : Fin 240}
    (h : ∀ a : Fin 8, cartan8Weight r₁ a = cartan8Weight r₂ a) : r₁ = r₂ := by
  apply e8RootCoord_injective
  ext j
  simp only [e8RootCoord, h]

/-- The 248-element family `(cartan8 ⊕ e8RootVec)` in `SplitE8Lie` is linearly independent. -/
theorem splitE8Cartan8_linearIndependent :
    LinearIndependent ℝ (Sum.elim cartan8 e8RootVec) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  have hkill := cartan_weight_kill_mem_generic cartan8 e8RootVec (fun a r => cartan8Weight r a)
    cartan8_comm e8RootVec_bracket_cartan8 cartan8Weight_ne_zero
    (fun {r₁ r₂} h => cartan8Weight_eq_imp h)
    ⊥ (fun _ x hx => by rw [Submodule.mem_bot] at hx; subst hx; simp)
    Finset.univ (∑ a : Fin 8, g (Sum.inl a) • cartan8 a)
    (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
    (fun r => g (Sum.inr r))
    (by rw [hg]; exact Submodule.zero_mem _)
  have ha0 : ∀ a : Fin 8, g (Sum.inl a) = 0 := by
    have h0 : ∑ a : Fin 8, g (Sum.inl a) • cartan8 a = 0 := (Submodule.mem_bot ℝ).mp hkill.1
    exact Fintype.linearIndependent_iff.mp cartan8_linearIndependent (fun a => g (Sum.inl a)) h0
  have hb0 : ∀ r : Fin 240, g (Sum.inr r) = 0 := by
    intro r
    have h0 : g (Sum.inr r) • e8RootVec r = 0 :=
      (Submodule.mem_bot ℝ).mp (hkill.2 r (Finset.mem_univ r))
    exact (smul_eq_zero.mp h0).resolve_right (e8RootVec_ne_zero r)
  rintro (a | r)
  · exact ha0 a
  · exact hb0 r

/-- The 248-element basis `(cartan8 ⊕ e8RootVec)` of `SplitE8Lie`. -/
def splitE8Cartan8Basis : Module.Basis (Fin 8 ⊕ Fin 240) ℝ SplitE8Lie :=
  basisOfLinearIndependentOfCardEqFinrank splitE8Cartan8_linearIndependent
    (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, finrank_splitE8Lie])

@[simp] theorem splitE8Cartan8Basis_inl (a : Fin 8) :
    splitE8Cartan8Basis (Sum.inl a) = cartan8 a := by
  simp [splitE8Cartan8Basis]

@[simp] theorem splitE8Cartan8Basis_inr (r : Fin 240) :
    splitE8Cartan8Basis (Sum.inr r) = e8RootVec r := by
  simp [splitE8Cartan8Basis]

/-- Vandermonde weight-killing lemma for `SplitE8Lie` submodules invariant under `splitE8Cartan`:
if `h + ∑ r ∈ A, b r • e8RootVec r ∈ S` with `h ∈ splitE8Cartan`, then `h ∈ S` and each
`b r • e8RootVec r ∈ S`. -/
theorem e8_cartan_weight_kill_mem
    (S : Submodule ℝ SplitE8Lie)
    (hS : ∀ (a : Fin 8) (x : SplitE8Lie), x ∈ S → ⁅cartan8 a, x⁆ ∈ S)
    (A : Finset (Fin 240)) (h : SplitE8Lie) (hh : h ∈ splitE8Cartan)
    (b : Fin 240 → ℝ) (hx : h + ∑ r ∈ A, b r • e8RootVec r ∈ S) :
    h ∈ S ∧ ∀ r ∈ A, b r • e8RootVec r ∈ S :=
  cartan_weight_kill_mem_generic cartan8 e8RootVec (fun a r => cartan8Weight r a)
    cartan8_comm e8RootVec_bracket_cartan8 cartan8Weight_ne_zero
    cartan8Weight_eq_imp S hS A h
    ((mem_splitE8Cartan_iff h).mp hh) b hx

/-- The 240 root weights in `(splitE8Cartan)⋆`. -/
def e8RootWeight (r : Fin 240) : Module.Dual ℝ splitE8Cartan :=
  splitE8CartanBasis.constr ℝ (fun a => (cartan8Weight r a : ℝ))

@[simp] theorem e8RootWeight_cartan8 (r : Fin 240) (a : Fin 8) :
    e8RootWeight r ⟨cartan8 a, cartan8_mem_splitE8Cartan a⟩ = (cartan8Weight r a : ℝ) := by
  have ha : splitE8CartanBasis a = ⟨cartan8 a, cartan8_mem_splitE8Cartan a⟩ :=
    Subtype.ext (splitE8CartanBasis_apply a)
  rw [← ha]
  exact Module.Basis.constr_basis splitE8CartanBasis ℝ (fun b => (cartan8Weight r b : ℝ)) a

theorem e8RootVec_bracket_cartan (H : splitE8Cartan) (r : Fin 240) :
    ⁅(H : SplitE8Lie), e8RootVec r⁆ = e8RootWeight r H • e8RootVec r := by
  have hrep := splitE8CartanBasis.sum_repr H
  conv_lhs => rw [← hrep]
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, splitE8CartanBasis_apply,
    sum_lie, smul_lie, e8RootVec_bracket_cartan8, smul_smul, ← Finset.sum_smul]
  congr 1
  have hlin : e8RootWeight r H =
      ∑ a : Fin 8, (splitE8CartanBasis.repr H a) * (cartan8Weight r a : ℝ) := by
    conv_lhs => rw [← hrep]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, smul_eq_mul]
    congr 1
    have h := Module.Basis.constr_basis splitE8CartanBasis ℝ (fun b => (cartan8Weight r b : ℝ)) a
    simpa only [e8RootWeight] using h
  rw [hlin]

theorem e8RootVec_mem_rootSpace (r : Fin 240) :
    e8RootVec r ∈ LieAlgebra.rootSpace splitE8Cartan (e8RootWeight r) := by
  rw [LieAlgebra.rootSpace, LieModule.mem_genWeightSpace]
  intro H
  refine ⟨1, ?_⟩
  simp only [pow_one]
  change ⁅(H : SplitE8Lie), e8RootVec r⁆ - e8RootWeight r H • e8RootVec r = 0
  rw [e8RootVec_bracket_cartan H r, sub_self]

theorem e8RootSpace_ne_bot (r : Fin 240) :
    LieAlgebra.rootSpace splitE8Cartan (e8RootWeight r) ≠ ⊥ := by
  intro hbot
  have hmem := e8RootVec_mem_rootSpace r
  rw [hbot, LieSubmodule.mem_bot] at hmem
  exact e8RootVec_ne_zero r hmem

theorem e8RootWeight_ne_zero (r : Fin 240) : e8RootWeight r ≠ 0 := by
  intro h0
  obtain ⟨a, ha⟩ := cartan8Weight_ne_zero r
  have hval := congrArg (fun f : Module.Dual ℝ splitE8Cartan =>
    f ⟨cartan8 a, cartan8_mem_splitE8Cartan a⟩) h0
  rw [e8RootWeight_cartan8, LinearMap.zero_apply] at hval
  exact ha (Int.cast_eq_zero.mp hval)

theorem e8RootWeight_injective : Function.Injective e8RootWeight := by
  intro r₁ r₂ heq
  apply cartan8Weight_eq_imp
  intro a
  have hval := congrArg (fun f : Module.Dual ℝ splitE8Cartan =>
    f ⟨cartan8 a, cartan8_mem_splitE8Cartan a⟩) heq
  rw [e8RootWeight_cartan8, e8RootWeight_cartan8] at hval
  exact Int.cast_injective hval

/-- `splitE8Cartan` is a genuine 8D split Cartan subalgebra of `SplitE8Lie`. -/
instance splitE8Cartan_isCartanSubalgebra : splitE8Cartan.IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := by
    apply le_antisymm _ splitE8Cartan.le_normalizer
    intro x hx
    have hrep := splitE8Cartan8Basis.sum_repr x
    rw [Fintype.sum_sum_type] at hrep
    simp only [splitE8Cartan8Basis_inl, splitE8Cartan8Basis_inr] at hrep
    have hhpart : (∑ a : Fin 8, (splitE8Cartan8Basis.repr x) (Sum.inl a) • cartan8 a) ∈
        splitE8Cartan :=
      Submodule.sum_mem _ fun a _ => splitE8Cartan.smul_mem _ (cartan8_mem_splitE8Cartan a)
    have hb0 : ∀ r : Fin 240, (splitE8Cartan8Basis.repr x) (Sum.inr r) = 0 := by
      intro r
      obtain ⟨a, ha⟩ := cartan8Weight_ne_zero r
      have hnorm : ⁅cartan8 a, x⁆ ∈ splitE8Cartan := by
        have hxmem := (LieSubalgebra.mem_normalizer_iff splitE8Cartan x).mp hx (cartan8 a)
          (cartan8_mem_splitE8Cartan a)
        have hneg := splitE8Cartan.neg_mem hxmem
        rw [← lie_skew, neg_neg] at hneg
        exact hneg
      have hKillH : ⁅cartan8 a, ∑ b : Fin 8, (splitE8Cartan8Basis.repr x) (Sum.inl b) • cartan8 b⁆ =
          0 := by
        have hc := (inferInstance : IsLieAbelian splitE8Cartan).trivial
          ⟨cartan8 a, cartan8_mem_splitE8Cartan a⟩ ⟨_, hhpart⟩
        exact congrArg Subtype.val hc
      have hbr : ⁅cartan8 a, x⁆ =
          ∑ q : Fin 240, ((splitE8Cartan8Basis.repr x) (Sum.inr q) *
            (cartan8Weight q a : ℝ)) • e8RootVec q := by
        conv_lhs => rw [← hrep]
        rw [lie_add, hKillH, zero_add, lie_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [lie_smul, e8RootVec_bracket_cartan8, smul_smul]
      have hmem : (-⁅cartan8 a, x⁆) +
          ∑ q : Fin 240, ((splitE8Cartan8Basis.repr x) (Sum.inr q) *
            (cartan8Weight q a : ℝ)) • e8RootVec q ∈ (⊥ : Submodule ℝ SplitE8Lie) := by
        rw [← hbr, neg_add_cancel]
        exact Submodule.zero_mem _
      have hkill := e8_cartan_weight_kill_mem ⊥
        (fun _ y hy => by rw [Submodule.mem_bot] at hy; subst hy; simp)
        Finset.univ (-⁅cartan8 a, x⁆) (splitE8Cartan.neg_mem hnorm)
        (fun q => (splitE8Cartan8Basis.repr x) (Sum.inr q) * (cartan8Weight q a : ℝ)) hmem
      have hr0 : ((splitE8Cartan8Basis.repr x) (Sum.inr r) *
          (cartan8Weight r a : ℝ)) • e8RootVec r = 0 :=
        (Submodule.mem_bot ℝ).mp (hkill.2 r (Finset.mem_univ r))
      have hmul0 := (smul_eq_zero.mp hr0).resolve_right (e8RootVec_ne_zero r)
      exact (mul_eq_zero.mp hmul0).resolve_right (Int.cast_ne_zero.mpr ha)
    have hs0 : (∑ r : Fin 240, (splitE8Cartan8Basis.repr x) (Sum.inr r) • e8RootVec r) = 0 :=
      Finset.sum_eq_zero fun r _ => by rw [hb0 r, zero_smul]
    rw [← hrep, hs0, add_zero]
    exact hhpart

instance splitE8Cartan_isTriangularizable :
    LieModule.IsTriangularizable ℝ splitE8Cartan SplitE8Lie := by
  refine ⟨fun H => ?_⟩
  apply (Submodule.eq_top_iff_forall_basis_mem splitE8Cartan8Basis).mpr
  rintro (a | r)
  · apply Submodule.mem_iSup_of_mem (0 : ℝ)
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff, splitE8Cartan8Basis_inl, zero_smul]
    have hc := (inferInstance : IsLieAbelian splitE8Cartan).trivial H
      ⟨cartan8 a, cartan8_mem_splitE8Cartan a⟩
    exact congrArg Subtype.val hc
  · apply Submodule.mem_iSup_of_mem (e8RootWeight r H)
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff, splitE8Cartan8Basis_inr]
    exact e8RootVec_bracket_cartan H r

end RootVectorsAndWeights

/-! ## 4. Bourbaki `E₈` Simple Chevalley System and M6c Readiness Exports -/

section BourbakiE8SimpleSystem

/-- Root indices in `Fin 240` of the 8 Bourbaki `E₈` simple `E` generators. -/
def e8ESimpleIdx : Fin 8 → Fin 240 := ![67, 41, 26, 37, 42, 121, 3, 4]

/-- Root indices in `Fin 240` of the 8 Bourbaki `E₈` simple `F` generators. -/
def e8FSimpleIdx : Fin 8 → Fin 240 := ![72, 29, 47, 40, 30, 196, 5, 1]

/-- Rational scales for `e8SimpleF` (`1/4` at `i = 0`, `±1` elsewhere). -/
def e8FSimpleScale : Fin 8 → ℝ := ![1 / 4, -1, -1, 1, -1, -1, 1, 1]

/-- Highest root index in `Fin 240` (`e8RootCoord 6 = ![2, 3, 4, 6, 5, 4, 3, 2]`). -/
def e8HighestRootIdx : Fin 240 := ⟨6, by decide⟩

/-- The 8 simple raising Chevalley generators of `SplitE8Lie` (`E₈`). -/
def e8SimpleE (i : Fin 8) : SplitE8Lie := e8RootVec (e8ESimpleIdx i)

/-- The 8 simple lowering Chevalley generators of `SplitE8Lie` (`E₈`). -/
def e8SimpleF (i : Fin 8) : SplitE8Lie := e8FSimpleScale i • e8RootVec (e8FSimpleIdx i)

/-- The 8 simple Cartan generators `H_i := [E_i, F_i]` of `SplitE8Lie` (`E₈`). -/
def e8SimpleH (i : Fin 8) : SplitE8Lie := ⁅e8SimpleE i, e8SimpleF i⁆

private def sparseMulEntry (a b : SparseMat27) (r c : Fin 27) : ℤ :=
  (a.map fun p => if p.1 = r then p.2.2 * sparseVal b p.2.1 c else 0).sum

private theorem sparseMulEntry_eq (a b : SparseMat27) (r c : Fin 27) :
    sparseMulEntry a b r c = ∑ k : Fin 27, sparseVal a r k * sparseVal b k c := by
  induction a with
  | nil => simp [sparseMulEntry]
  | cons p a ih =>
    rcases p with ⟨r', k', v⟩
    rw [sparseMulEntry, List.map_cons, List.sum_cons]
    change (if r' = r then v * sparseVal b k' c else 0) + sparseMulEntry a b r c = _
    rw [ih]
    simp only [sparseVal_cons, add_mul, Finset.sum_add_distrib]
    congr 1
    by_cases hr : r' = r
    · subst hr
      simp
    · simp [hr]

private def matCommEntry (a b : SparseMat27) (r c : Fin 27) : ℤ :=
  sparseMulEntry a b r c - sparseMulEntry b a r c

private theorem matCommEntry_eq (a b : SparseMat27) (r c : Fin 27) :
    (matCommEntry a b r c : ℝ) =
      ((sparseToMat a).map (Int.cast : ℤ → ℝ) * (sparseToMat b).map (Int.cast : ℤ → ℝ) -
        (sparseToMat b).map (Int.cast : ℤ → ℝ) * (sparseToMat a).map (Int.cast : ℤ → ℝ)) r c := by
  have hsum : matCommEntry a b r c =
      ∑ k : Fin 27, sparseVal a r k * sparseVal b k c -
        ∑ k : Fin 27, sparseVal b r k * sparseVal a k c := by
    rw [matCommEntry, sparseMulEntry_eq, sparseMulEntry_eq]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, ← Int.cast_mul,
    ← Int.cast_sum, ← Int.cast_sub, Int.cast_inj]
  exact hsum

private def matCommLinRowCheck (a1 b1 a2 b2 rhs : SparseMat27) (s1 s2 : ℤ)
    (off : ℕ) (h : off + 9 ≤ 27) : Bool :=
  (List.finRange 9).all fun nr =>
    let r : Fin 27 := ⟨off + nr.val, by omega⟩
    (List.finRange 27).all fun c =>
      s1 * matCommEntry a1 b1 r c + s2 * matCommEntry a2 b2 r c == sparseVal rhs r c

private theorem sparseToMat_comm_lin_eq (a1 b1 a2 b2 rhs : SparseMat27) (s1 s2 : ℤ)
    (h0 : matCommLinRowCheck a1 b1 a2 b2 rhs s1 s2 0 (by decide) = true)
    (h1 : matCommLinRowCheck a1 b1 a2 b2 rhs s1 s2 9 (by decide) = true)
    (h2 : matCommLinRowCheck a1 b1 a2 b2 rhs s1 s2 18 (by decide) = true) :
    (s1 : ℝ) • ((sparseToMat a1).map (Int.cast : ℤ → ℝ) * (sparseToMat b1).map (Int.cast : ℤ → ℝ) -
        (sparseToMat b1).map (Int.cast : ℤ → ℝ) * (sparseToMat a1).map (Int.cast : ℤ → ℝ)) +
      (s2 : ℝ) • ((sparseToMat a2).map (Int.cast : ℤ → ℝ) * (sparseToMat b2).map (Int.cast : ℤ → ℝ) -
        (sparseToMat b2).map (Int.cast : ℤ → ℝ) * (sparseToMat a2).map (Int.cast : ℤ → ℝ)) =
      (sparseToMat rhs).map (Int.cast : ℤ → ℝ) := by
  have hrow : ∀ r c : Fin 27,
      s1 * matCommEntry a1 b1 r c + s2 * matCommEntry a2 b2 r c = sparseVal rhs r c := by
    have hb : ∀ (off : ℕ) (h : off + 9 ≤ 27),
        matCommLinRowCheck a1 b1 a2 b2 rhs s1 s2 off h = true →
        ∀ nr : Fin 9, ∀ c : Fin 27,
          s1 * matCommEntry a1 b1 ⟨off + nr.val, by omega⟩ c +
            s2 * matCommEntry a2 b2 ⟨off + nr.val, by omega⟩ c =
            sparseVal rhs ⟨off + nr.val, by omega⟩ c := by
      intro off h hchk nr c
      dsimp [matCommLinRowCheck] at hchk
      simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
      exact hchk nr c
    intro r c
    by_cases hr0 : r.val < 9
    · have heq : (⟨0 + (⟨r.val, hr0⟩ : Fin 9).val, by omega⟩ : Fin 27) = r :=
        Fin.ext (by dsimp; omega)
      simpa [heq] using hb 0 (by decide) h0 ⟨r.val, hr0⟩ c
    · by_cases hr1 : r.val < 18
      · have hk : r.val - 9 < 9 := by omega
        have heq : (⟨9 + (⟨r.val - 9, hk⟩ : Fin 9).val, by omega⟩ : Fin 27) = r :=
          Fin.ext (by dsimp; omega)
        simpa [heq] using hb 9 (by decide) h1 ⟨r.val - 9, hk⟩ c
      · have hk : r.val - 18 < 9 := by omega
        have heq : (⟨18 + (⟨r.val - 18, hk⟩ : Fin 9).val, by omega⟩ : Fin 27) = r :=
          Fin.ext (by dsimp; omega)
        simpa [heq] using hb 18 (by decide) h2 ⟨r.val - 18, hk⟩ c
  ext r c
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply]
  rw [← matCommEntry_eq a1 b1 r c, ← matCommEntry_eq a2 b2 r c, ← Int.cast_mul,
    ← Int.cast_mul, ← Int.cast_add, hrow r c]
  rfl

private theorem sparseToMat_comm_one_eq (a b rhs : SparseMat27) (s : ℤ)
    (h0 : matCommLinRowCheck a b [] [] rhs s 0 0 (by decide) = true)
    (h1 : matCommLinRowCheck a b [] [] rhs s 0 9 (by decide) = true)
    (h2 : matCommLinRowCheck a b [] [] rhs s 0 18 (by decide) = true) :
    (s : ℝ) • ((sparseToMat a).map (Int.cast : ℤ → ℝ) * (sparseToMat b).map (Int.cast : ℤ → ℝ) -
        (sparseToMat b).map (Int.cast : ℤ → ℝ) * (sparseToMat a).map (Int.cast : ℤ → ℝ)) =
      (sparseToMat rhs).map (Int.cast : ℤ → ℝ) := by
  have h := sparseToMat_comm_lin_eq a b [] [] rhs s 0 h0 h1 h2
  simpa using h

private def f4SimpleRhs0 : SparseMat27 :=
  sparseAdd (sparseNeg (f4CartanDiagSparse 0))
    (sparseAdd (sparseSmul (-2) (f4CartanDiagSparse 1))
      (sparseAdd (sparseNeg (f4CartanDiagSparse 3))
        (sparseSmul (-2) (f4CartanDiagSparse 2))))

private def f4SimpleRhs1 : SparseMat27 :=
  sparseAdd (f4CartanDiagSparse 0)
    (sparseAdd (sparseSmul 2 (f4CartanDiagSparse 1))
      (sparseAdd (f4CartanDiagSparse 3) (f4CartanDiagSparse 2)))

private def f4SimpleRhs2 : SparseMat27 := sparseNeg (f4CartanDiagSparse 1)

private def f4SimpleRhs3 : SparseMat27 :=
  sparseAdd (f4CartanDiagSparse 0)
    (sparseAdd (sparseSmul 2 (f4CartanDiagSparse 1)) (f4CartanDiagSparse 2))

private def e8H0Rhs : SparseMat27 :=
  sparseAdd (sparseSmul (-4) (f4CartanDiagSparse 0))
    (sparseAdd (sparseSmul (-4) (f4CartanDiagSparse 1))
      (sparseAdd (sparseSmul (-2) (f4CartanDiagSparse 3))
        (sparseSmul (-2) (f4CartanDiagSparse 2))))

private def e8H5Rhs : SparseMat27 :=
  sparseAdd (sparseSmul 2 (f4CartanDiagSparse 0))
    (sparseAdd (sparseSmul 2 (f4CartanDiagSparse 1)) (f4CartanDiagSparse 2))

private theorem f4Simple0_mat :
    (-1 : ℝ) • ((sparseToMat (f4RootSparse 17)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (f4RootSparse 5)).map Int.cast -
      (sparseToMat (f4RootSparse 5)).map Int.cast *
        (sparseToMat (f4RootSparse 17)).map Int.cast) =
      (sparseToMat f4SimpleRhs0).map Int.cast := by
  simpa using sparseToMat_comm_one_eq (f4RootSparse 17) (f4RootSparse 5) f4SimpleRhs0 (-1)
    (by decide) (by decide) (by decide)

private theorem f4Simple1_mat :
    (-1 : ℝ) • ((sparseToMat (f4RootSparse 2)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (f4RootSparse 23)).map Int.cast -
      (sparseToMat (f4RootSparse 23)).map Int.cast *
        (sparseToMat (f4RootSparse 2)).map Int.cast) =
      (sparseToMat f4SimpleRhs1).map Int.cast := by
  simpa using sparseToMat_comm_one_eq (f4RootSparse 2) (f4RootSparse 23) f4SimpleRhs1 (-1)
    (by decide) (by decide) (by decide)

private theorem f4Simple2_mat :
    (1 : ℝ) • ((sparseToMat (f4RootSparse 13)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (f4RootSparse 16)).map Int.cast -
      (sparseToMat (f4RootSparse 16)).map Int.cast *
        (sparseToMat (f4RootSparse 13)).map Int.cast) =
      (sparseToMat f4SimpleRhs2).map Int.cast := by
  simpa using sparseToMat_comm_one_eq (f4RootSparse 13) (f4RootSparse 16) f4SimpleRhs2 1
    (by decide) (by decide) (by decide)

private theorem f4Simple3_mat :
    (-1 : ℝ) • ((sparseToMat (f4RootSparse 18)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (f4RootSparse 6)).map Int.cast -
      (sparseToMat (f4RootSparse 6)).map Int.cast *
        (sparseToMat (f4RootSparse 18)).map Int.cast) =
      (sparseToMat f4SimpleRhs3).map Int.cast := by
  simpa using sparseToMat_comm_one_eq (f4RootSparse 18) (f4RootSparse 6) f4SimpleRhs3 (-1)
    (by decide) (by decide) (by decide)

private theorem e8SimpleH0_f4_mat :
    ((sparseToMat (f4RootSparse 33)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (f4RootSparse 36)).map Int.cast -
      (sparseToMat (f4RootSparse 36)).map Int.cast *
        (sparseToMat (f4RootSparse 33)).map Int.cast) -
      ((sparseToMat (twoLData 12)).map Int.cast *
        (sparseToMat (twoLData 15)).map Int.cast -
      (sparseToMat (twoLData 15)).map Int.cast *
        (sparseToMat (twoLData 12)).map Int.cast) =
      (sparseToMat e8H0Rhs).map Int.cast := by
  have h := sparseToMat_comm_lin_eq (f4RootSparse 33) (f4RootSparse 36)
    (twoLData 12) (twoLData 15) e8H0Rhs 1 (-1) (by decide) (by decide) (by decide)
  simpa [sub_eq_add_neg, add_comm] using h

private theorem e8SimpleH5_f4_mat :
    (sparseToMat (twoLData 4)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (twoLData 7)).map Int.cast -
      (sparseToMat (twoLData 7)).map Int.cast *
        (sparseToMat (twoLData 4)).map Int.cast =
      (sparseToMat e8H5Rhs).map Int.cast := by
  have h := sparseToMat_comm_one_eq (twoLData 4) (twoLData 7) e8H5Rhs 1
    (by decide) (by decide) (by decide)
  simpa using h

private theorem f4RootVec_33_apply_15 :
    f4Act (f4RootVec 33) (h3TraceZeroOff 12) = (-1 : ℝ) • h3DiagZero₂ := by
  have hcol : (List.finRange 27).all (fun r =>
      sparseVal (f4RootSparse 33) r 15 ==
        (if r.val = 1 then (-1 : ℤ) else if r.val = 2 then 1 else 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hcol
  apply Subtype.ext
  apply h3ZornBasis.ext_elem
  intro r
  have h15 : (⟨3 + (12 : Fin 24).val, by omega⟩ : Fin 27) = 15 := rfl
  rw [f4Act_coe, SetLike.val_smul, h3TraceZeroOff_coe, h15,
    h3DiagZero₂_eq_basis, map_smul, map_sub, h3ZornBasis.repr_self, h3ZornBasis.repr_self]
  have hr : h3ZornBasis.repr ((f4RootVec 33 : H3ZornF4Derivations).1 (h3ZornBasis 15)) r =
      h3zornToMatrix (f4RootVec 33 : Module.End ℝ (H3Zorn ℝ)) r 15 := by
    rw [h3zornToMatrix_apply]; rfl
  rw [hr, h3zornToMatrix_f4RootVec]
  simp only [Matrix.map_apply]
  change (sparseVal (f4RootSparse 33) r 15 : ℝ) = _
  rw [hcol r]
  fin_cases r <;> simp

private theorem f4RootVec_36_apply_12 :
    f4Act (f4RootVec 36) (h3TraceZeroOff 9) = (-1 : ℝ) • h3DiagZero₂ := by
  have hcol : (List.finRange 27).all (fun r =>
      sparseVal (f4RootSparse 36) r 12 ==
        (if r.val = 1 then (-1 : ℤ) else if r.val = 2 then 1 else 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hcol
  apply Subtype.ext
  apply h3ZornBasis.ext_elem
  intro r
  have h12 : (⟨3 + (9 : Fin 24).val, by omega⟩ : Fin 27) = 12 := rfl
  rw [f4Act_coe, SetLike.val_smul, h3TraceZeroOff_coe, h12,
    h3DiagZero₂_eq_basis, map_smul, map_sub, h3ZornBasis.repr_self, h3ZornBasis.repr_self]
  have hr : h3ZornBasis.repr ((f4RootVec 36 : H3ZornF4Derivations).1 (h3ZornBasis 12)) r =
      h3zornToMatrix (f4RootVec 36 : Module.End ℝ (H3Zorn ℝ)) r 12 := by
    rw [h3zornToMatrix_apply]; rfl
  rw [hr, h3zornToMatrix_f4RootVec]
  simp only [Matrix.map_apply]
  change (sparseVal (f4RootSparse 36) r 12 : ℝ) = _
  rw [hcol r]
  fin_cases r <;> simp

private theorem g2Param_7_bracket_12 :
    ⁅g2Param 7, g2Param 12⁆ = g2CartanBasis 0 - g2CartanBasis 1 := by
  apply parameterLinearEquiv.symm.injective
  have lhs_eq : parameterLinearEquiv.symm ⁅g2Param 7, g2Param 12⁆ =
      derivationParameters ⁅g2Param 7, g2Param 12⁆ := rfl
  have hbr : ∀ (D₁ D₂ : VDer) (X : VZ), (⁅D₁, D₂⁆).toFun X = D₁ (D₂ X) - D₂ (D₁ X) :=
    fun _ _ _ => rfl
  have hsub : parameterLinearEquiv.symm (g2CartanBasis 0 - g2CartanBasis 1) =
      parameterLinearEquiv.symm (g2CartanBasis 0) - parameterLinearEquiv.symm (g2CartanBasis 1) :=
    map_sub parameterLinearEquiv.symm (g2CartanBasis 0) (g2CartanBasis 1)
  rw [lhs_eq, hsub]
  have hc0 : parameterLinearEquiv.symm (g2CartanBasis 0) = fun i => if i = 6 then 1 else 0 :=
    parameterLinearEquiv.symm_apply_apply _
  have hc1 : parameterLinearEquiv.symm (g2CartanBasis 1) = fun i => if i = 13 then 1 else 0 :=
    parameterLinearEquiv.symm_apply_apply _
  rw [hc0, hc1]
  funext k; fin_cases k <;>
    simp [derivationParameters, hbr, g2Param, parameterDerivation, parameterAction,
      ZornVectorMatrix.E22, ZornVectorMatrix.U, ZornVectorMatrix.V,
      ZornVec3.basis, vz_sub_w]

private theorem g2Param_11_bracket_2 :
    ⁅g2Param 11, g2Param 2⁆ = g2CartanBasis 1 := by
  apply parameterLinearEquiv.symm.injective
  have lhs_eq : parameterLinearEquiv.symm ⁅g2Param 11, g2Param 2⁆ =
      derivationParameters ⁅g2Param 11, g2Param 2⁆ := rfl
  have hbr : ∀ (D₁ D₂ : VDer) (X : VZ), (⁅D₁, D₂⁆).toFun X = D₁ (D₂ X) - D₂ (D₁ X) :=
    fun _ _ _ => rfl
  rw [lhs_eq]
  have hc1 : parameterLinearEquiv.symm (g2CartanBasis 1) = fun i => if i = 13 then 1 else 0 :=
    parameterLinearEquiv.symm_apply_apply _
  rw [hc1]
  funext k; fin_cases k <;>
    simp [derivationParameters, hbr, g2Param, parameterDerivation, parameterAction,
      ZornVectorMatrix.E22, ZornVectorMatrix.U, ZornVectorMatrix.V,
      ZornVec3.basis, vz_sub_w]

private theorem g2Inner_zornU1_zornV1 :
    g2Inner (zornU 1) (zornV 1) = (-2 : ℝ) • g2CartanBasis 0 + g2CartanBasis 1 := by
  apply parameterLinearEquiv.symm.injective
  have lhs_eq : parameterLinearEquiv.symm (g2Inner (zornU 1) (zornV 1)) =
      derivationParameters (g2Inner (zornU 1) (zornV 1)) := rfl
  have hst : ∀ (x y z : VZ),
      (fromNonAssocDerivation (zornStanDerivation (R := ℝ) x y)).toFun z =
        stanDerMap (R := ℝ) x y z := fun _ _ _ => rfl
  rw [lhs_eq, map_add, map_smul]
  have hc0 : parameterLinearEquiv.symm (g2CartanBasis 0) = fun i => if i = 6 then 1 else 0 :=
    parameterLinearEquiv.symm_apply_apply _
  have hc1 : parameterLinearEquiv.symm (g2CartanBasis 1) = fun i => if i = 13 then 1 else 0 :=
    parameterLinearEquiv.symm_apply_apply _
  rw [hc0, hc1]
  funext k; fin_cases k <;>
    simp [derivationParameters, g2Inner, hst, stanDerMap, L_map, R_map,
      zornU, zornV, ZornVectorMatrix.E22, ZornVectorMatrix.U, ZornVectorMatrix.V,
      ZornVectorMatrix.mul, ZornVectorMatrix.add,
      vz_sub_a, vz_sub_v, vz_sub_w, vz_sub_b, ZornVec3.dot, ZornVec3.cross,
      ZornVec3.basis]

private theorem zornBilin_zornU1_zornV1 :
    zornBilin (zornU 1).1 (zornV 1).1 = -1 := by
  simp [zornBilin, zornU, zornV, ZornVectorMatrix.U, ZornVectorMatrix.V,
    ZornVectorMatrix.conj, ZornVectorMatrix.mul, ZornVectorMatrix.trace,
    ZornVec3.dot, ZornVec3.basis]

private theorem zornComm0_zornU1_zornV1 :
    zornComm0 (zornU 1) (zornV 1) = zornE0 := by
  apply Subtype.ext
  apply ZornVectorMatrix.ext
  · simp [zornComm0, zornU, zornV, zornE0, ZornVectorMatrix.U, ZornVectorMatrix.V,
      ZornVectorMatrix.diagonal, ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.basis,
      vz_sub_a]
  · funext k; fin_cases k <;>
      simp [zornComm0, zornU, zornV, zornE0, ZornVectorMatrix.U, ZornVectorMatrix.V,
        ZornVectorMatrix.diagonal, ZornVectorMatrix.mul, ZornVec3.cross, ZornVec3.basis,
        vz_sub_v]
  · funext k; fin_cases k <;>
      simp [zornComm0, zornU, zornV, zornE0, ZornVectorMatrix.U, ZornVectorMatrix.V,
        ZornVectorMatrix.diagonal, ZornVectorMatrix.mul, ZornVec3.cross, ZornVec3.basis,
        vz_sub_w]
  · simp [zornComm0, zornU, zornV, zornE0, ZornVectorMatrix.U, ZornVectorMatrix.V,
      ZornVectorMatrix.diagonal, ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.basis,
      vz_sub_b]

private theorem traceBilin_off1_off4 :
    traceBilin (h3TraceZeroOff 1).1 (h3TraceZeroOff 4).1 = -1 := by
  have h1 : (h3TraceZeroOff 1 : H3Zorn ℝ) = embedJ12 (zorn_basis 1) := by
    simpa [h3TraceZeroOff_coe] using h3ZornBasis_12 1
  have h4 : (h3TraceZeroOff 4 : H3Zorn ℝ) = embedJ12 (zorn_basis 4) := by
    simpa [h3TraceZeroOff_coe] using h3ZornBasis_12 4
  change traceBilin (h3TraceZeroOff 1 : H3Zorn ℝ) (h3TraceZeroOff 4 : H3Zorn ℝ) = -1
  rw [h1, h4]
  simp [traceBilin, InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit.embedJ12,
    zorn_basis, ZornVectorMatrix.mul, ZornVectorMatrix.trace, ZornVectorMatrix.conj,
    ZornVectorMatrix.zero, ZornVec3.dot]

private theorem h3Mul0_off1_off4 :
    h3Mul0 (h3TraceZeroOff 1) (h3TraceZeroOff 4) =
      (-1 / 6 : ℝ) • h3DiagZero₁ + (-1 / 3 : ℝ) • h3DiagZero₂ := by
  have hmul : h3ZornBasis 4 * h3ZornBasis 7 =
      (-1 / 2 : ℝ) • h3ZornBasis 0 + (-1 / 2 : ℝ) • h3ZornBasis 1 := by
    apply h3ZornBasis_mul_eq 4 7
    intro r
    rw [map_add, map_smul, map_smul, h3ZornBasis.repr_self, h3ZornBasis.repr_self,
      Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
      Finsupp.single_apply, Finsupp.single_apply]
    fin_cases r <;> norm_num [twoLData]
  apply Subtype.ext
  rw [h3Mul0_coe, traceBilin_off1_off4]
  change (h3ZornBasis 4 * h3ZornBasis 7 : H3Zorn ℝ) -
      ((1 / 3 : ℝ) * (-1 : ℝ)) • (1 : H3Zorn ℝ) = _
  rw [hmul, h3_one_eq_basis_sum']
  simp only [Submodule.coe_add, SetLike.val_smul, h3DiagZero₁_eq_basis, h3DiagZero₂_eq_basis]
  module

private theorem h3zornToMatrix_f4CartanBasis (i : Fin 4) :
    h3zornToMatrix (f4CartanBasis i : Module.End ℝ (H3Zorn ℝ)) =
      (sparseToMat (f4CartanDiagSparse (f4Perm i))).map Int.cast := by
  rw [f4CartanBasis_eq_f4SimpleH i]
  exact h3zornToMatrix_f4SimpleH (f4Perm i)

private theorem e8SimpleH0_eq :
    e8SimpleH 0 =
      -cartan8 2 - cartan8 3 - (1 / 2 : ℝ) • cartan8 4 -
        (1 / 2 : ℝ) • cartan8 5 - (1 / 2 : ℝ) • cartan8 7 := by
  have he : e8SimpleE 0 =
      embedF4 (f4RootVec 33) - embedTensor zornE0 (h3TraceZeroOff 9) := by
    change sector4Vec 9 (-1) = _
    dsimp [sector4Vec]
    simp only [Int.cast_neg, Int.cast_one, neg_smul, one_smul, sub_eq_add_neg]
  have hf : e8SimpleF 0 =
      (1 / 4 : ℝ) • (embedF4 (f4RootVec 36) + embedTensor zornE0 (h3TraceZeroOff 12)) := by
    change (1 / 4 : ℝ) • sector4Vec 12 1 = _
    dsimp [sector4Vec]
    simp only [Int.cast_one, one_smul]
  have hbr : e8SimpleH 0 =
      (1 / 4 : ℝ) • (embedF4 (⁅f4RootVec 33, f4RootVec 36⁆ -
          (4 : ℝ) • f4Inner (h3TraceZeroOff 9) (h3TraceZeroOff 12)) +
        embedTensor zornE0 (f4Act (f4RootVec 33) (h3TraceZeroOff 12) +
          f4Act (f4RootVec 36) (h3TraceZeroOff 9))) := by
    change ⁅e8SimpleE 0, e8SimpleF 0⁆ = _
    rw [he, hf, lie_smul, lie_add, sub_lie, sub_lie, bracket_f4_f4, bracket_f4_tensor,
      bracket_tensor_f4, bracket_tensor_tensor, g2Inner_self, zornComm0_self,
      zornBilin_zornE0_self]
    have htz : ∀ x : h3TraceZero, embedTensor (0 : splitOctonionTraceZero) x = 0 := fun x => by
      change embedMixed (0 ⊗ₜ[ℝ] x) = 0
      apply SplitE8Lie.ext <;> simp [embedMixed_apply]
    rw [htz]
    simp only [smul_zero, map_zero, zero_add]
    apply congrArg ((1 / 4 : ℝ) • ·)
    apply SplitE8Lie.ext
    · simp only [SplitE8Lie.add_g2, SplitE8Lie.sub_g2, SplitE8Lie.neg_g2,
        embedF4_apply, embedTensor_apply, embedMixed_apply, add_zero]
      abel
    · simp only [SplitE8Lie.add_mixed, SplitE8Lie.sub_mixed, SplitE8Lie.neg_mixed,
        embedF4_apply, embedTensor_apply, embedMixed_apply, TensorProduct.tmul_add]
      abel
    · simp only [SplitE8Lie.add_f4, SplitE8Lie.sub_f4, SplitE8Lie.neg_f4,
        embedF4_apply, embedTensor_apply]
      norm_num; abel
  have hf4 : ⁅f4RootVec 33, f4RootVec 36⁆ -
      (4 : ℝ) • f4Inner (h3TraceZeroOff 9) (h3TraceZeroOff 12) =
      (-4 : ℝ) • f4CartanBasis 0 - (4 : ℝ) • f4CartanBasis 1 -
        (2 : ℝ) • f4CartanBasis 2 - (2 : ℝ) • f4CartanBasis 3 := by
    apply Subtype.ext
    apply h3zornToMatrix.injective
    have h4in : h3zornToMatrix ((4 : ℝ) • (f4Inner (h3TraceZeroOff 9) (h3TraceZeroOff 12) :
        Module.End ℝ (H3Zorn ℝ))) =
        (sparseToMat (sparseComm (twoLData 12) (twoLData 15))).map Int.cast :=
      h3zornToMatrix_four_f4Inner _ _ _ _
        (h3zornToMatrix_two_jordanLmul_basis 12) (h3zornToMatrix_two_jordanLmul_basis 15)
    change h3zornToMatrix ((⁅f4RootVec 33, f4RootVec 36⁆ : Module.End ℝ (H3Zorn ℝ)) -
        (4 : ℝ) • (f4Inner (h3TraceZeroOff 9) (h3TraceZeroOff 12) : Module.End ℝ (H3Zorn ℝ))) = _
    rw [map_sub, h3zornToMatrix_f4_lie, h3zornToMatrix_f4RootVec, h3zornToMatrix_f4RootVec, h4in]
    have hcomm : (sparseToMat (f4RootSparse 33)).map (Int.cast : ℤ → ℝ) *
          (sparseToMat (f4RootSparse 36)).map Int.cast -
        (sparseToMat (f4RootSparse 36)).map Int.cast *
          (sparseToMat (f4RootSparse 33)).map Int.cast -
        (sparseToMat (sparseComm (twoLData 12) (twoLData 15))).map Int.cast =
        (sparseToMat e8H0Rhs).map Int.cast := by
      have h2 := e8SimpleH0_f4_mat
      have hsc : (sparseToMat (sparseComm (twoLData 12) (twoLData 15))).map (Int.cast : ℤ → ℝ) =
          (sparseToMat (twoLData 12)).map Int.cast * (sparseToMat (twoLData 15)).map Int.cast -
          (sparseToMat (twoLData 15)).map Int.cast * (sparseToMat (twoLData 12)).map Int.cast := by
        rw [sparseToMat_comm]; ext r c; simp [Matrix.mul_apply, Matrix.sub_apply]
      rw [hsc]
      exact h2
    rw [hcomm]
    change _ = h3zornToMatrix ((-4 : ℝ) • (f4CartanBasis 0 : Module.End ℝ (H3Zorn ℝ)) -
        (4 : ℝ) • (f4CartanBasis 1 : Module.End ℝ (H3Zorn ℝ)) -
        (2 : ℝ) • (f4CartanBasis 2 : Module.End ℝ (H3Zorn ℝ)) -
        (2 : ℝ) • (f4CartanBasis 3 : Module.End ℝ (H3Zorn ℝ)))
    simp only [map_sub, map_smul, h3zornToMatrix_f4CartanBasis, f4Perm,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ext a b
    simp only [e8H0Rhs, sparseToMat_add, sparseToMat_smul, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Int.cast_add,
      Int.cast_mul, Int.cast_ofNat, Int.cast_neg]
    ring
  rw [hbr, hf4, f4RootVec_33_apply_15, f4RootVec_36_apply_12]
  simp only [cartan8, map_sub, map_smul, map_add, smul_add, smul_sub, smul_smul]
  norm_num
  module

private theorem e8SimpleH_f4_eq (i : Fin 4) :
    e8SimpleH ⟨i.val + 1, by omega⟩ =
      match i.val with
      | 0 => -cartan8 2 - (2 : ℝ) • cartan8 3 - cartan8 4 - (2 : ℝ) • cartan8 5
      | 1 => cartan8 2 + (2 : ℝ) • cartan8 3 + cartan8 4 + cartan8 5
      | 2 => -cartan8 3
      | _ => cartan8 2 + (2 : ℝ) • cartan8 3 + cartan8 5 := by
  have hf4_sub : ∀ (a b : Fin 48) (sa sb : ℝ),
      ⁅embedF4 (sa • f4RootVec a), embedF4 (sb • f4RootVec b)⁆ =
        embedF4 ⁅sa • f4RootVec a, sb • f4RootVec b⁆ := fun _ _ _ _ =>
    bracket_f4_f4 _ _
  have hm_eq : ∀ (a b : Fin 48) (sa sb : ℝ) (rhs : SparseMat27),
      (sa * sb) •
          ((sparseToMat (f4RootSparse a)).map (Int.cast : ℤ → ℝ) *
            (sparseToMat (f4RootSparse b)).map Int.cast -
          (sparseToMat (f4RootSparse b)).map Int.cast *
            (sparseToMat (f4RootSparse a)).map Int.cast) =
        (sparseToMat rhs).map Int.cast →
      h3zornToMatrix ((⁅sa • f4RootVec a, sb • f4RootVec b⁆ : F4DerivationCarrier) :
        Module.End ℝ (H3Zorn ℝ)) = (sparseToMat rhs).map Int.cast := by
    intro a b sa sb rhs hs
    have hsm : ((⁅sa • f4RootVec a, sb • f4RootVec b⁆ : F4DerivationCarrier) :
        Module.End ℝ (H3Zorn ℝ)) =
        (sa * sb) • (⁅f4RootVec a, f4RootVec b⁆ : Module.End ℝ (H3Zorn ℝ)) := by
      rw [smul_lie, lie_smul, smul_smul]; rfl
    rw [hsm, map_smul, h3zornToMatrix_f4_lie, h3zornToMatrix_f4RootVec, h3zornToMatrix_f4RootVec,
      hs]
  fin_cases i
  · change ⁅e8SimpleE 1, e8SimpleF 1⁆ = _
    have hE : e8SimpleE 1 = embedF4 ((1 : ℝ) • f4RootVec 17) := by
      change embedF4 (f4RootVec 17) = _
      rw [one_smul]
    have hF : e8SimpleF 1 = embedF4 ((-1 : ℝ) • f4RootVec 5) := by
      change (-1 : ℝ) • embedF4 (f4RootVec 5) = _
      rw [← map_smul]
    rw [hE, hF, hf4_sub]
    have hmat := hm_eq 17 5 1 (-1) f4SimpleRhs0 (by simpa using f4Simple0_mat)
    have hf4 : ⁅(1 : ℝ) • f4RootVec 17, (-1 : ℝ) • f4RootVec 5⁆ =
        -f4CartanBasis 0 - (2 : ℝ) • f4CartanBasis 1 - f4CartanBasis 2 -
          (2 : ℝ) • f4CartanBasis 3 := by
      apply Subtype.ext; apply h3zornToMatrix.injective
      change h3zornToMatrix ((⁅(1 : ℝ) • f4RootVec 17, (-1 : ℝ) • f4RootVec 5⁆ :
        F4DerivationCarrier) : Module.End ℝ (H3Zorn ℝ)) =
        h3zornToMatrix (-(f4CartanBasis 0 : Module.End ℝ (H3Zorn ℝ)) -
          (2 : ℝ) • (f4CartanBasis 1 : Module.End ℝ (H3Zorn ℝ)) -
          (f4CartanBasis 2 : Module.End ℝ (H3Zorn ℝ)) -
          (2 : ℝ) • (f4CartanBasis 3 : Module.End ℝ (H3Zorn ℝ)))
      rw [hmat]
      simp only [map_sub, map_neg, map_smul, h3zornToMatrix_f4CartanBasis, f4Perm,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ext r c
      simp only [f4SimpleRhs0, sparseToMat_add, sparseToMat_smul, sparseToMat_neg,
        Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply,
        Matrix.map_apply, smul_eq_mul, Int.cast_add, Int.cast_neg, Int.cast_mul, Int.cast_ofNat]
      ring
    rw [hf4]
    simp only [cartan8]
    apply SplitE8Lie.ext <;> simp [embedF4_apply]; abel
  · change ⁅e8SimpleE 2, e8SimpleF 2⁆ = _
    have hE : e8SimpleE 2 = embedF4 ((1 : ℝ) • f4RootVec 2) := by
      change embedF4 (f4RootVec 2) = _
      rw [one_smul]
    have hF : e8SimpleF 2 = embedF4 ((-1 : ℝ) • f4RootVec 23) := by
      change (-1 : ℝ) • embedF4 (f4RootVec 23) = _
      rw [← map_smul]
    rw [hE, hF, hf4_sub]
    have hmat := hm_eq 2 23 1 (-1) f4SimpleRhs1 (by simpa using f4Simple1_mat)
    have hf4 : ⁅(1 : ℝ) • f4RootVec 2, (-1 : ℝ) • f4RootVec 23⁆ =
        f4CartanBasis 0 + (2 : ℝ) • f4CartanBasis 1 + f4CartanBasis 2 + f4CartanBasis 3 := by
      apply Subtype.ext; apply h3zornToMatrix.injective
      change h3zornToMatrix ((⁅(1 : ℝ) • f4RootVec 2, (-1 : ℝ) • f4RootVec 23⁆ :
        F4DerivationCarrier) : Module.End ℝ (H3Zorn ℝ)) =
        h3zornToMatrix ((f4CartanBasis 0 : Module.End ℝ (H3Zorn ℝ)) +
          (2 : ℝ) • (f4CartanBasis 1 : Module.End ℝ (H3Zorn ℝ)) +
          (f4CartanBasis 2 : Module.End ℝ (H3Zorn ℝ)) +
          (f4CartanBasis 3 : Module.End ℝ (H3Zorn ℝ)))
      rw [hmat]
      simp only [map_add, map_smul, h3zornToMatrix_f4CartanBasis, f4Perm,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ext r c
      simp only [f4SimpleRhs1, sparseToMat_add, sparseToMat_smul, Matrix.add_apply,
        Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Int.cast_add, Int.cast_mul,
        Int.cast_ofNat]
      ring
    rw [hf4]
    simp only [cartan8]
    apply SplitE8Lie.ext <;> simp [embedF4_apply]
  · change ⁅e8SimpleE 3, e8SimpleF 3⁆ = _
    have hE : e8SimpleE 3 = embedF4 ((1 : ℝ) • f4RootVec 13) := by
      change embedF4 (f4RootVec 13) = _
      rw [one_smul]
    have hF : e8SimpleF 3 = embedF4 ((1 : ℝ) • f4RootVec 16) := by
      change (1 : ℝ) • embedF4 (f4RootVec 16) = _
      rw [← map_smul]
    rw [hE, hF, hf4_sub]
    have hmat := hm_eq 13 16 1 1 f4SimpleRhs2 (by simpa using f4Simple2_mat)
    have hf4 : ⁅(1 : ℝ) • f4RootVec 13, (1 : ℝ) • f4RootVec 16⁆ =
        -f4CartanBasis 1 := by
      apply Subtype.ext; apply h3zornToMatrix.injective
      change h3zornToMatrix ((⁅(1 : ℝ) • f4RootVec 13, (1 : ℝ) • f4RootVec 16⁆ :
        F4DerivationCarrier) : Module.End ℝ (H3Zorn ℝ)) =
        h3zornToMatrix (-(f4CartanBasis 1 : Module.End ℝ (H3Zorn ℝ)))
      rw [hmat]
      simp only [map_neg, h3zornToMatrix_f4CartanBasis]
      rw [show f4Perm 1 = 1 from rfl]
      ext r c
      simp only [f4SimpleRhs2, sparseToMat_neg, Matrix.neg_apply, Matrix.map_apply, Int.cast_neg]
    rw [hf4]
    simp only [cartan8]
    apply SplitE8Lie.ext <;> simp [embedF4_apply]
  · change ⁅e8SimpleE 4, e8SimpleF 4⁆ = _
    have hE : e8SimpleE 4 = embedF4 ((1 : ℝ) • f4RootVec 18) := by
      change embedF4 (f4RootVec 18) = _
      rw [one_smul]
    have hF : e8SimpleF 4 = embedF4 ((-1 : ℝ) • f4RootVec 6) := by
      change (-1 : ℝ) • embedF4 (f4RootVec 6) = _
      rw [← map_smul]
    rw [hE, hF, hf4_sub]
    have hmat := hm_eq 18 6 1 (-1) f4SimpleRhs3 (by simpa using f4Simple3_mat)
    have hf4 : ⁅(1 : ℝ) • f4RootVec 18, (-1 : ℝ) • f4RootVec 6⁆ =
        f4CartanBasis 0 + (2 : ℝ) • f4CartanBasis 1 + f4CartanBasis 3 := by
      apply Subtype.ext; apply h3zornToMatrix.injective
      change h3zornToMatrix ((⁅(1 : ℝ) • f4RootVec 18, (-1 : ℝ) • f4RootVec 6⁆ :
        F4DerivationCarrier) : Module.End ℝ (H3Zorn ℝ)) =
        h3zornToMatrix ((f4CartanBasis 0 : Module.End ℝ (H3Zorn ℝ)) +
          (2 : ℝ) • (f4CartanBasis 1 : Module.End ℝ (H3Zorn ℝ)) +
          (f4CartanBasis 3 : Module.End ℝ (H3Zorn ℝ)))
      rw [hmat]
      simp only [map_add, map_smul, h3zornToMatrix_f4CartanBasis, f4Perm,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ext r c
      simp only [f4SimpleRhs3, sparseToMat_add, sparseToMat_smul, Matrix.add_apply,
        Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Int.cast_add, Int.cast_mul,
        Int.cast_ofNat]
      ring
    rw [hf4]
    simp only [cartan8]
    apply SplitE8Lie.ext <;> simp [embedF4_apply]

private theorem e8SimpleH5_eq :
    e8SimpleH 5 =
      (-2 / 3 : ℝ) • cartan8 0 + (1 / 3 : ℝ) • cartan8 1 -
        cartan8 2 - cartan8 3 - (1 / 2 : ℝ) • cartan8 5 +
        (1 / 6 : ℝ) • cartan8 6 + (1 / 3 : ℝ) • cartan8 7 := by
  have hE : e8SimpleE 5 = embedTensor (zornU 1) (h3TraceZeroOff 1) := rfl
  have hF : e8SimpleF 5 = (-1 : ℝ) • embedTensor (zornV 1) (h3TraceZeroOff 4) := rfl
  have hf4 : f4Inner (h3TraceZeroOff 1) (h3TraceZeroOff 4) =
      (1 / 2 : ℝ) • f4CartanBasis 0 + (1 / 2 : ℝ) • f4CartanBasis 1 +
        (1 / 4 : ℝ) • f4CartanBasis 3 := by
    have h4 : (4 : ℝ) • f4Inner (h3TraceZeroOff 1) (h3TraceZeroOff 4) =
        (2 : ℝ) • f4CartanBasis 0 + (2 : ℝ) • f4CartanBasis 1 + f4CartanBasis 3 := by
      apply Subtype.ext; apply h3zornToMatrix.injective
      have hm := h3zornToMatrix_four_f4Inner (h3TraceZeroOff 1) (h3TraceZeroOff 4) _ _
        (h3zornToMatrix_two_jordanLmul_basis 4) (h3zornToMatrix_two_jordanLmul_basis 7)
      change h3zornToMatrix ((4 : ℝ) • (f4Inner (h3TraceZeroOff 1) (h3TraceZeroOff 4) :
        Module.End ℝ (H3Zorn ℝ))) =
        h3zornToMatrix ((2 : ℝ) • (f4CartanBasis 0 : Module.End ℝ (H3Zorn ℝ)) +
          (2 : ℝ) • (f4CartanBasis 1 : Module.End ℝ (H3Zorn ℝ)) +
          (f4CartanBasis 3 : Module.End ℝ (H3Zorn ℝ)))
      have hm1 : (sparseToMat (sparseComm (twoLData 4) (twoLData 7))).map (Int.cast : ℤ → ℝ) =
          (sparseToMat e8H5Rhs).map Int.cast := by
        rw [sparseToMat_comm]
        have hm2 := e8SimpleH5_f4_mat
        have hcast : ((sparseToMat (twoLData 4) * sparseToMat (twoLData 7) -
            sparseToMat (twoLData 7) * sparseToMat (twoLData 4)).map (Int.cast : ℤ → ℝ)) =
            (sparseToMat (twoLData 4)).map Int.cast * (sparseToMat (twoLData 7)).map Int.cast -
            (sparseToMat (twoLData 7)).map Int.cast * (sparseToMat (twoLData 4)).map Int.cast := by
          ext a b; simp [Matrix.mul_apply, Matrix.sub_apply]
        rw [hcast]
        exact hm2
      rw [hm, hm1]
      simp only [map_add, map_smul, h3zornToMatrix_f4CartanBasis, f4Perm,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ext a b
      simp only [e8H5Rhs, sparseToMat_add, sparseToMat_smul, Matrix.add_apply, Matrix.smul_apply,
        Matrix.map_apply, smul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
      ring
    have h1 := congrArg (fun D : F4DerivationCarrier => (1 / 4 : ℝ) • D) h4
    simpa [smul_smul, smul_add] using h1.trans (by norm_num; module)
  change ⁅e8SimpleE 5, e8SimpleF 5⁆ = _
  rw [hE, hF, lie_smul, bracket_tensor_tensor, traceBilin_off1_off4, g2Inner_zornU1_zornV1,
    zornComm0_zornU1_zornV1, h3Mul0_off1_off4, zornBilin_zornU1_zornV1, hf4]
  simp only [cartan8, map_add, map_smul, smul_add, smul_smul]
  norm_num
  module

private theorem e8SimpleH6_eq : e8SimpleH 6 = cartan8 0 - cartan8 1 := by
  change ⁅e8SimpleE 6, e8SimpleF 6⁆ = _
  have hE : e8SimpleE 6 = embedG2 (g2Param 7) := by
    simp [e8SimpleE, e8ESimpleIdx, e8RootVec, g2LongIdx]
  have hF : e8SimpleF 6 = embedG2 (g2Param 12) := by
    simp [e8SimpleF, e8FSimpleScale, e8FSimpleIdx, e8RootVec, g2LongIdx]
  rw [hE, hF, bracket_g2_g2, g2Param_7_bracket_12]
  apply SplitE8Lie.ext <;> simp [cartan8, embedG2_apply]

private theorem e8SimpleH7_eq : e8SimpleH 7 = cartan8 1 := by
  change ⁅e8SimpleE 7, e8SimpleF 7⁆ = _
  have hE : e8SimpleE 7 = embedG2 (g2Param 11) := by
    simp [e8SimpleE, e8ESimpleIdx, e8RootVec, g2LongIdx]
  have hF : e8SimpleF 7 = embedG2 (g2Param 2) := by
    simp [e8SimpleF, e8FSimpleScale, e8FSimpleIdx, e8RootVec, g2LongIdx]
  rw [hE, hF, bracket_g2_g2, g2Param_11_bracket_2]
  rfl

theorem e8SimpleH_eq_linear_comb_cartan8 (i : Fin 8) :
    e8SimpleH i =
      match i.val with
      | 0 => -cartan8 2 - cartan8 3 - (1 / 2 : ℝ) • cartan8 4 -
          (1 / 2 : ℝ) • cartan8 5 - (1 / 2 : ℝ) • cartan8 7
      | 1 => -cartan8 2 - (2 : ℝ) • cartan8 3 - cartan8 4 - (2 : ℝ) • cartan8 5
      | 2 => cartan8 2 + (2 : ℝ) • cartan8 3 + cartan8 4 + cartan8 5
      | 3 => -cartan8 3
      | 4 => cartan8 2 + (2 : ℝ) • cartan8 3 + cartan8 5
      | 5 => (-2 / 3 : ℝ) • cartan8 0 + (1 / 3 : ℝ) • cartan8 1 -
          cartan8 2 - cartan8 3 - (1 / 2 : ℝ) • cartan8 5 +
          (1 / 6 : ℝ) • cartan8 6 + (1 / 3 : ℝ) • cartan8 7
      | 6 => cartan8 0 - cartan8 1
      | _ => cartan8 1 := by
  fin_cases i
  · exact e8SimpleH0_eq
  · exact e8SimpleH_f4_eq 0
  · exact e8SimpleH_f4_eq 1
  · exact e8SimpleH_f4_eq 2
  · exact e8SimpleH_f4_eq 3
  · exact e8SimpleH5_eq
  · exact e8SimpleH6_eq
  · exact e8SimpleH7_eq

theorem cartan8_eq_linear_comb_e8SimpleH (a : Fin 8) :
    cartan8 a =
      match a.val with
      | 0 => e8SimpleH 6 + e8SimpleH 7
      | 1 => e8SimpleH 7
      | 2 => e8SimpleH 1 + e8SimpleH 2 + (2 : ℝ) • e8SimpleH 3 + e8SimpleH 4
      | 3 => -e8SimpleH 3
      | 4 => e8SimpleH 2 - e8SimpleH 4
      | 5 => -e8SimpleH 1 - e8SimpleH 2
      | 6 => (4 : ℝ) • e8SimpleH 0 + (5 : ℝ) • e8SimpleH 1 + (7 : ℝ) • e8SimpleH 2 +
          (10 : ℝ) • e8SimpleH 3 + (8 : ℝ) • e8SimpleH 4 + (6 : ℝ) • e8SimpleH 5 +
          (4 : ℝ) • e8SimpleH 6 + (2 : ℝ) • e8SimpleH 7
      | _ => (-2 : ℝ) • e8SimpleH 0 - e8SimpleH 1 - (2 : ℝ) • e8SimpleH 2 -
          (2 : ℝ) • e8SimpleH 3 - e8SimpleH 4 := by
  have h0 := e8SimpleH0_eq
  have h1 : e8SimpleH 1 = -cartan8 2 - (2 : ℝ) • cartan8 3 - cartan8 4 - (2 : ℝ) • cartan8 5 :=
    e8SimpleH_f4_eq 0
  have h2 : e8SimpleH 2 = cartan8 2 + (2 : ℝ) • cartan8 3 + cartan8 4 + cartan8 5 :=
    e8SimpleH_f4_eq 1
  have h3 : e8SimpleH 3 = -cartan8 3 :=
    e8SimpleH_f4_eq 2
  have h4 : e8SimpleH 4 = cartan8 2 + (2 : ℝ) • cartan8 3 + cartan8 5 :=
    e8SimpleH_f4_eq 3
  have h5 := e8SimpleH5_eq
  have h6 := e8SimpleH6_eq
  have h7 := e8SimpleH7_eq
  fin_cases a <;> (dsimp; simp only [h0, h1, h2, h3, h4, h5, h6, h7]; try module)

theorem splitE8Cartan_eq_span_e8SimpleH :
    splitE8Cartan.toSubmodule = Submodule.span ℝ (Set.range e8SimpleH) := by
  apply le_antisymm
  · change Submodule.span ℝ (Set.range cartan8) ≤ _
    rw [Submodule.span_le]
    rintro x ⟨a, rfl⟩
    rw [cartan8_eq_linear_comb_e8SimpleH a]
    have hmem : ∀ i : Fin 8, e8SimpleH i ∈ Submodule.span ℝ (Set.range e8SimpleH) :=
      fun i => Submodule.subset_span ⟨i, rfl⟩
    fin_cases a <;>
      repeat' first
        | apply Submodule.add_mem
        | apply Submodule.sub_mem
        | apply Submodule.neg_mem
        | apply Submodule.smul_mem
        | exact hmem _
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    change e8SimpleH i ∈ Submodule.span ℝ (Set.range cartan8)
    rw [e8SimpleH_eq_linear_comb_cartan8 i]
    have hmem : ∀ a : Fin 8, cartan8 a ∈ Submodule.span ℝ (Set.range cartan8) :=
      fun a => Submodule.subset_span ⟨a, rfl⟩
    fin_cases i <;>
      repeat' first
        | apply Submodule.add_mem
        | apply Submodule.sub_mem
        | apply Submodule.neg_mem
        | apply Submodule.smul_mem
        | exact hmem _

@[simp] theorem e8SimpleH_mem_splitE8Cartan (i : Fin 8) : e8SimpleH i ∈ splitE8Cartan := by
  change e8SimpleH i ∈ splitE8Cartan.toSubmodule
  rw [splitE8Cartan_eq_span_e8SimpleH]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem e8SimpleH_comm (i j : Fin 8) : ⁅e8SimpleH i, e8SimpleH j⁆ = 0 := by
  have hc := (inferInstance : IsLieAbelian splitE8Cartan).trivial
    ⟨e8SimpleH i, e8SimpleH_mem_splitE8Cartan i⟩
    ⟨e8SimpleH j, e8SimpleH_mem_splitE8Cartan j⟩
  exact congrArg Subtype.val hc

theorem e8SimpleH_linearIndependent : LinearIndependent ℝ e8SimpleH := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let bH : Module.Basis (Fin 8) ℝ splitE8Cartan := by
    have hspan_top : Submodule.span ℝ (Set.range (fun i : Fin 8 =>
        (⟨e8SimpleH i, e8SimpleH_mem_splitE8Cartan i⟩ : splitE8Cartan))) = ⊤ := by
      rw [Submodule.eq_top_iff']
      rintro ⟨x, hx⟩
      have hx' : x ∈ Submodule.span ℝ (Set.range e8SimpleH) := by
        rwa [← splitE8Cartan_eq_span_e8SimpleH]
      have hmem : ∀ y, y ∈ Submodule.span ℝ (Set.range e8SimpleH) →
          ∀ hy : y ∈ splitE8Cartan,
          (⟨y, hy⟩ : splitE8Cartan) ∈ Submodule.span ℝ (Set.range (fun i : Fin 8 =>
            (⟨e8SimpleH i, e8SimpleH_mem_splitE8Cartan i⟩ : splitE8Cartan))) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | zero => intro _; exact Submodule.zero_mem _
        | add u v hu hv ihu ihv =>
          intro _
          have hu' : u ∈ splitE8Cartan := by
            change u ∈ splitE8Cartan.toSubmodule
            rw [splitE8Cartan_eq_span_e8SimpleH]
            exact hu
          have hv' : v ∈ splitE8Cartan := by
            change v ∈ splitE8Cartan.toSubmodule
            rw [splitE8Cartan_eq_span_e8SimpleH]
            exact hv
          exact Submodule.add_mem _ (ihu hu') (ihv hv')
        | smul r u hu ihu =>
          intro _
          have hu' : u ∈ splitE8Cartan := by
            change u ∈ splitE8Cartan.toSubmodule
            rw [splitE8Cartan_eq_span_e8SimpleH]
            exact hu
          exact Submodule.smul_mem _ r (ihu hu')
        | mem u hm =>
          intro _
          rcases hm with ⟨i, rfl⟩
          exact Submodule.subset_span ⟨i, rfl⟩
      exact hmem x hx' hx
    exact basisOfTopLeSpanOfCardEqFinrank
      (fun i : Fin 8 => (⟨e8SimpleH i, e8SimpleH_mem_splitE8Cartan i⟩ : splitE8Cartan))
      (le_of_eq hspan_top.symm)
      (by rw [Fintype.card_fin, finrank_splitE8Cartan])
  have hli := bH.linearIndependent
  have hc' : ∑ i : Fin 8, c i • bH i = 0 :=
    Subtype.ext (by simpa [bH] using hc)
  exact Fintype.linearIndependent_iff.mp hli c hc'

/-- The 248-element Chevalley basis `(e8SimpleH ⊕ e8RootVec)` of `SplitE8Lie`. -/
def e8ChevalleyBasis : Module.Basis (Fin 8 ⊕ Fin 240) ℝ SplitE8Lie :=
  let v : Fin 8 ⊕ Fin 240 → SplitE8Lie := Sum.elim e8SimpleH e8RootVec
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [v, Sum.elim_inl, Sum.elim_inr] at hg
    have hh_mem : (∑ i : Fin 8, g (Sum.inl i) • e8SimpleH i) ∈ splitE8Cartan :=
      Submodule.sum_mem _ fun i _ => splitE8Cartan.smul_mem _ (e8SimpleH_mem_splitE8Cartan i)
    have hkill := e8_cartan_weight_kill_mem ⊥
      (fun _ x hx => by rw [Submodule.mem_bot] at hx; subst hx; simp)
      Finset.univ (∑ i : Fin 8, g (Sum.inl i) • e8SimpleH i) hh_mem
      (fun r => g (Sum.inr r)) (by rw [hg]; exact Submodule.zero_mem _)
    have ha0 : ∀ i : Fin 8, g (Sum.inl i) = 0 := by
      have h0 : ∑ i : Fin 8, g (Sum.inl i) • e8SimpleH i = 0 := (Submodule.mem_bot ℝ).mp hkill.1
      exact Fintype.linearIndependent_iff.mp e8SimpleH_linearIndependent (fun i => g (Sum.inl i)) h0
    have hb0 : ∀ r : Fin 240, g (Sum.inr r) = 0 := by
      intro r
      have h0 : g (Sum.inr r) • e8RootVec r = 0 :=
        (Submodule.mem_bot ℝ).mp (hkill.2 r (Finset.mem_univ r))
      exact (smul_eq_zero.mp h0).resolve_right (e8RootVec_ne_zero r)
    rintro (i | r)
    · exact ha0 i
    · exact hb0 r
  basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, finrank_splitE8Lie])

@[simp] theorem e8ChevalleyBasis_inl (i : Fin 8) :
    e8ChevalleyBasis (Sum.inl i) = e8SimpleH i := by
  simp [e8ChevalleyBasis]

@[simp] theorem e8ChevalleyBasis_inr (r : Fin 240) :
    e8ChevalleyBasis (Sum.inr r) = e8RootVec r := by
  simp [e8ChevalleyBasis]

/-- Integer eigenvalue of `ad (e8SimpleH i)` on `e8RootVec r`. -/
def e8RootEigenvalue (i : Fin 8) (r : Fin 240) : ℤ :=
  ∑ j : Fin 8, Tag.cartan .E8 i j * e8RootCoord r j

private def e8EvCheckBlock (i : Fin 8) (offset : ℕ) (h : offset + 24 ≤ 240) : Bool :=
  (List.finRange 24).all fun k =>
    let r : Fin 240 := ⟨offset + k.val, by omega⟩
    let lhs := 6 * e8RootEigenvalue i r
    let rhs := match i.val with
      | 0 => -6 * cartan8Weight r 2 - 6 * cartan8Weight r 3 - 3 * cartan8Weight r 4 -
          3 * cartan8Weight r 5 - 3 * cartan8Weight r 7
      | 1 => -6 * cartan8Weight r 2 - 12 * cartan8Weight r 3 - 6 * cartan8Weight r 4 -
          12 * cartan8Weight r 5
      | 2 => 6 * cartan8Weight r 2 + 12 * cartan8Weight r 3 + 6 * cartan8Weight r 4 +
          6 * cartan8Weight r 5
      | 3 => -6 * cartan8Weight r 3
      | 4 => 6 * cartan8Weight r 2 + 12 * cartan8Weight r 3 + 6 * cartan8Weight r 5
      | 5 => -4 * cartan8Weight r 0 + 2 * cartan8Weight r 1 - 6 * cartan8Weight r 2 -
          6 * cartan8Weight r 3 - 3 * cartan8Weight r 5 + cartan8Weight r 6 +
          2 * cartan8Weight r 7
      | 6 => 6 * cartan8Weight r 0 - 6 * cartan8Weight r 1
      | _ => 6 * cartan8Weight r 1
    lhs == rhs

private theorem e8EvBlock_0 : (List.finRange 8).all (fun i => e8EvCheckBlock i 0 (by decide)) = true := by decide
private theorem e8EvBlock_1 : (List.finRange 8).all (fun i => e8EvCheckBlock i 24 (by decide)) = true := by decide
private theorem e8EvBlock_2 : (List.finRange 8).all (fun i => e8EvCheckBlock i 48 (by decide)) = true := by decide
private theorem e8EvBlock_3 : (List.finRange 8).all (fun i => e8EvCheckBlock i 72 (by decide)) = true := by decide
private theorem e8EvBlock_4 : (List.finRange 8).all (fun i => e8EvCheckBlock i 96 (by decide)) = true := by decide
private theorem e8EvBlock_5 : (List.finRange 8).all (fun i => e8EvCheckBlock i 120 (by decide)) = true := by decide
private theorem e8EvBlock_6 : (List.finRange 8).all (fun i => e8EvCheckBlock i 144 (by decide)) = true := by decide
private theorem e8EvBlock_7 : (List.finRange 8).all (fun i => e8EvCheckBlock i 168 (by decide)) = true := by decide
private theorem e8EvBlock_8 : (List.finRange 8).all (fun i => e8EvCheckBlock i 192 (by decide)) = true := by decide
private theorem e8EvBlock_9 : (List.finRange 8).all (fun i => e8EvCheckBlock i 216 (by decide)) = true := by decide

private theorem e8Ev_check_all (i : Fin 8) (r : Fin 240) :
    (6 : ℤ) * e8RootEigenvalue i r =
      match i.val with
      | 0 => -6 * cartan8Weight r 2 - 6 * cartan8Weight r 3 - 3 * cartan8Weight r 4 -
          3 * cartan8Weight r 5 - 3 * cartan8Weight r 7
      | 1 => -6 * cartan8Weight r 2 - 12 * cartan8Weight r 3 - 6 * cartan8Weight r 4 -
          12 * cartan8Weight r 5
      | 2 => 6 * cartan8Weight r 2 + 12 * cartan8Weight r 3 + 6 * cartan8Weight r 4 +
          6 * cartan8Weight r 5
      | 3 => -6 * cartan8Weight r 3
      | 4 => 6 * cartan8Weight r 2 + 12 * cartan8Weight r 3 + 6 * cartan8Weight r 5
      | 5 => -4 * cartan8Weight r 0 + 2 * cartan8Weight r 1 - 6 * cartan8Weight r 2 -
          6 * cartan8Weight r 3 - 3 * cartan8Weight r 5 + cartan8Weight r 6 +
          2 * cartan8Weight r 7
      | 6 => 6 * cartan8Weight r 0 - 6 * cartan8Weight r 1
      | _ => 6 * cartan8Weight r 1 := by
  have hb : ∀ (off : ℕ) (h : off + 24 ≤ 240),
      (List.finRange 8).all (fun i => e8EvCheckBlock i off h) = true →
      ∀ k : Fin 24,
        (6 : ℤ) * e8RootEigenvalue i ⟨off + k.val, by omega⟩ =
          match i.val with
          | 0 => -6 * cartan8Weight ⟨off + k.val, by omega⟩ 2 -
              6 * cartan8Weight ⟨off + k.val, by omega⟩ 3 -
              3 * cartan8Weight ⟨off + k.val, by omega⟩ 4 -
              3 * cartan8Weight ⟨off + k.val, by omega⟩ 5 -
              3 * cartan8Weight ⟨off + k.val, by omega⟩ 7
          | 1 => -6 * cartan8Weight ⟨off + k.val, by omega⟩ 2 -
              12 * cartan8Weight ⟨off + k.val, by omega⟩ 3 -
              6 * cartan8Weight ⟨off + k.val, by omega⟩ 4 -
              12 * cartan8Weight ⟨off + k.val, by omega⟩ 5
          | 2 => 6 * cartan8Weight ⟨off + k.val, by omega⟩ 2 +
              12 * cartan8Weight ⟨off + k.val, by omega⟩ 3 +
              6 * cartan8Weight ⟨off + k.val, by omega⟩ 4 +
              6 * cartan8Weight ⟨off + k.val, by omega⟩ 5
          | 3 => -6 * cartan8Weight ⟨off + k.val, by omega⟩ 3
          | 4 => 6 * cartan8Weight ⟨off + k.val, by omega⟩ 2 +
              12 * cartan8Weight ⟨off + k.val, by omega⟩ 3 +
              6 * cartan8Weight ⟨off + k.val, by omega⟩ 5
          | 5 => -4 * cartan8Weight ⟨off + k.val, by omega⟩ 0 +
              2 * cartan8Weight ⟨off + k.val, by omega⟩ 1 -
              6 * cartan8Weight ⟨off + k.val, by omega⟩ 2 -
              6 * cartan8Weight ⟨off + k.val, by omega⟩ 3 -
              3 * cartan8Weight ⟨off + k.val, by omega⟩ 5 +
              cartan8Weight ⟨off + k.val, by omega⟩ 6 +
              2 * cartan8Weight ⟨off + k.val, by omega⟩ 7
          | 6 => 6 * cartan8Weight ⟨off + k.val, by omega⟩ 0 -
              6 * cartan8Weight ⟨off + k.val, by omega⟩ 1
          | _ => 6 * cartan8Weight ⟨off + k.val, by omega⟩ 1 := by
    intro off h hchk k
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
    have hi := hchk i
    dsimp [e8EvCheckBlock] at hi
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hi
    exact hi k
  by_cases h0 : r.val < 24
  · have heq : (⟨0 + (⟨r.val, h0⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
    have hres := hb 0 (by decide) e8EvBlock_0 ⟨r.val, h0⟩
    rwa [heq] at hres
  · by_cases h1 : r.val < 48
    · have hk : r.val - 24 < 24 := by omega
      have heq : (⟨24 + (⟨r.val - 24, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
      have hres := hb 24 (by decide) e8EvBlock_1 ⟨r.val - 24, hk⟩
      rwa [heq] at hres
    · by_cases h2 : r.val < 72
      · have hk : r.val - 48 < 24 := by omega
        have heq : (⟨48 + (⟨r.val - 48, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
        have hres := hb 48 (by decide) e8EvBlock_2 ⟨r.val - 48, hk⟩
        rwa [heq] at hres
      · by_cases h3 : r.val < 96
        · have hk : r.val - 72 < 24 := by omega
          have heq : (⟨72 + (⟨r.val - 72, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
          have hres := hb 72 (by decide) e8EvBlock_3 ⟨r.val - 72, hk⟩
          rwa [heq] at hres
        · by_cases h4 : r.val < 120
          · have hk : r.val - 96 < 24 := by omega
            have heq : (⟨96 + (⟨r.val - 96, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
            have hres := hb 96 (by decide) e8EvBlock_4 ⟨r.val - 96, hk⟩
            rwa [heq] at hres
          · by_cases h5 : r.val < 144
            · have hk : r.val - 120 < 24 := by omega
              have heq : (⟨120 + (⟨r.val - 120, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
              have hres := hb 120 (by decide) e8EvBlock_5 ⟨r.val - 120, hk⟩
              rwa [heq] at hres
            · by_cases h6 : r.val < 168
              · have hk : r.val - 144 < 24 := by omega
                have heq : (⟨144 + (⟨r.val - 144, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
                have hres := hb 144 (by decide) e8EvBlock_6 ⟨r.val - 144, hk⟩
                rwa [heq] at hres
              · by_cases h7 : r.val < 192
                · have hk : r.val - 168 < 24 := by omega
                  have heq : (⟨168 + (⟨r.val - 168, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
                  have hres := hb 168 (by decide) e8EvBlock_7 ⟨r.val - 168, hk⟩
                  rwa [heq] at hres
                · by_cases h8 : r.val < 216
                  · have hk : r.val - 192 < 24 := by omega
                    have heq : (⟨192 + (⟨r.val - 192, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
                    have hres := hb 192 (by decide) e8EvBlock_8 ⟨r.val - 192, hk⟩
                    rwa [heq] at hres
                  · have hk : r.val - 216 < 24 := by omega
                    have heq : (⟨216 + (⟨r.val - 216, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
                    have hres := hb 216 (by decide) e8EvBlock_9 ⟨r.val - 216, hk⟩
                    rwa [heq] at hres

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
  · have heq : (⟨0 + (⟨r.val, c0⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
    simpa [heq] using hb 0 (by decide) h0 ⟨r.val, c0⟩
  · by_cases c1 : r.val < 48
    · have hk : r.val - 24 < 24 := by omega
      have heq : (⟨24 + (⟨r.val - 24, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
      simpa [heq] using hb 24 (by decide) h1 ⟨r.val - 24, hk⟩
    · by_cases c2 : r.val < 72
      · have hk : r.val - 48 < 24 := by omega
        have heq : (⟨48 + (⟨r.val - 48, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
        simpa [heq] using hb 48 (by decide) h2 ⟨r.val - 48, hk⟩
      · by_cases c3 : r.val < 96
        · have hk : r.val - 72 < 24 := by omega
          have heq : (⟨72 + (⟨r.val - 72, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
          simpa [heq] using hb 72 (by decide) h3 ⟨r.val - 72, hk⟩
        · by_cases c4 : r.val < 120
          · have hk : r.val - 96 < 24 := by omega
            have heq : (⟨96 + (⟨r.val - 96, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
            simpa [heq] using hb 96 (by decide) h4 ⟨r.val - 96, hk⟩
          · by_cases c5 : r.val < 144
            · have hk : r.val - 120 < 24 := by omega
              have heq : (⟨120 + (⟨r.val - 120, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
              simpa [heq] using hb 120 (by decide) h5 ⟨r.val - 120, hk⟩
            · by_cases c6 : r.val < 168
              · have hk : r.val - 144 < 24 := by omega
                have heq : (⟨144 + (⟨r.val - 144, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
                simpa [heq] using hb 144 (by decide) h6 ⟨r.val - 144, hk⟩
              · by_cases c7 : r.val < 192
                · have hk : r.val - 168 < 24 := by omega
                  have heq : (⟨168 + (⟨r.val - 168, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
                  simpa [heq] using hb 168 (by decide) h7 ⟨r.val - 168, hk⟩
                · by_cases c8 : r.val < 216
                  · have hk : r.val - 192 < 24 := by omega
                    have heq : (⟨192 + (⟨r.val - 192, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
                    simpa [heq] using hb 192 (by decide) h8 ⟨r.val - 192, hk⟩
                  · have hk : r.val - 216 < 24 := by omega
                    have heq : (⟨216 + (⟨r.val - 216, hk⟩ : Fin 24).val, by omega⟩ : Fin 240) = r := Fin.ext (by dsimp; omega)
                    simpa [heq] using hb 216 (by decide) h9 ⟨r.val - 216, hk⟩

theorem e8RootVec_bracket_H (i : Fin 8) (r : Fin 240) :
    ⁅e8SimpleH i, e8RootVec r⁆ = (e8RootEigenvalue i r : ℝ) • e8RootVec r := by
  rw [e8SimpleH_eq_linear_comb_cartan8 i]
  fin_cases i
  · have hev : (6 : ℤ) * e8RootEigenvalue 0 r = -6 * cartan8Weight r 2 - 6 * cartan8Weight r 3 -
        3 * cartan8Weight r 4 - 3 * cartan8Weight r 5 - 3 * cartan8Weight r 7 := e8Ev_check_all 0 r
    have hevR := congrArg (Int.cast : ℤ → ℝ) hev; push_cast at hevR
    dsimp; simp only [neg_lie, sub_lie, smul_lie, e8RootVec_bracket_cartan8, smul_smul,
      ← sub_smul, ← neg_smul]; congr 1; linarith
  · have hev : (6 : ℤ) * e8RootEigenvalue 1 r = -6 * cartan8Weight r 2 - 12 * cartan8Weight r 3 -
        6 * cartan8Weight r 4 - 12 * cartan8Weight r 5 := e8Ev_check_all 1 r
    have hevR := congrArg (Int.cast : ℤ → ℝ) hev; push_cast at hevR
    dsimp; simp only [neg_lie, sub_lie, smul_lie, e8RootVec_bracket_cartan8, smul_smul,
      ← sub_smul, ← neg_smul]; congr 1; linarith
  · have hev : (6 : ℤ) * e8RootEigenvalue 2 r = 6 * cartan8Weight r 2 + 12 * cartan8Weight r 3 +
        6 * cartan8Weight r 4 + 6 * cartan8Weight r 5 := e8Ev_check_all 2 r
    have hevR := congrArg (Int.cast : ℤ → ℝ) hev; push_cast at hevR
    dsimp; simp only [add_lie, smul_lie, e8RootVec_bracket_cartan8, smul_smul,
      ← add_smul]; congr 1; linarith
  · have hev : (6 : ℤ) * e8RootEigenvalue 3 r = -6 * cartan8Weight r 3 := e8Ev_check_all 3 r
    have hevR := congrArg (Int.cast : ℤ → ℝ) hev; push_cast at hevR
    dsimp; simp only [neg_lie, e8RootVec_bracket_cartan8,
      ← neg_smul]; congr 1; linarith
  · have hev : (6 : ℤ) * e8RootEigenvalue 4 r = 6 * cartan8Weight r 2 + 12 * cartan8Weight r 3 +
        6 * cartan8Weight r 5 := e8Ev_check_all 4 r
    have hevR := congrArg (Int.cast : ℤ → ℝ) hev; push_cast at hevR
    dsimp; simp only [add_lie, smul_lie, e8RootVec_bracket_cartan8, smul_smul,
      ← add_smul]; congr 1; linarith
  · have hev : (6 : ℤ) * e8RootEigenvalue 5 r = -4 * cartan8Weight r 0 + 2 * cartan8Weight r 1 -
        6 * cartan8Weight r 2 - 6 * cartan8Weight r 3 - 3 * cartan8Weight r 5 +
        cartan8Weight r 6 + 2 * cartan8Weight r 7 := e8Ev_check_all 5 r
    have hevR := congrArg (Int.cast : ℤ → ℝ) hev; push_cast at hevR
    dsimp; simp only [sub_lie, add_lie, smul_lie, e8RootVec_bracket_cartan8, smul_smul,
      ← add_smul, ← sub_smul]; congr 1; linarith
  · have hev : (6 : ℤ) * e8RootEigenvalue 6 r =
        6 * cartan8Weight r 0 - 6 * cartan8Weight r 1 := e8Ev_check_all 6 r
    have hevR := congrArg (Int.cast : ℤ → ℝ) hev; push_cast at hevR
    dsimp; simp only [sub_lie, e8RootVec_bracket_cartan8,
      ← sub_smul]; congr 1; linarith
  · have hev : (6 : ℤ) * e8RootEigenvalue 7 r = 6 * cartan8Weight r 1 := e8Ev_check_all 7 r
    have hevR := congrArg (Int.cast : ℤ → ℝ) hev; push_cast at hevR
    dsimp; simp only [e8RootVec_bracket_cartan8]; congr 1; linarith

theorem e8RootEigenvalue_ne_zero (r : Fin 240) : ∃ i : Fin 8, e8RootEigenvalue i r ≠ 0 := by
  have hchk := forall_fin240_of_blocks
    (fun r => (List.finRange 8).any (fun i => e8RootEigenvalue i r != 0))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) r
  simp only [List.any_eq_true, List.mem_finRange, true_and, bne_iff_ne, ne_eq] at hchk
  exact hchk

private theorem cartan_E8_mulVec_inj : Function.Injective (Tag.cartan .E8).mulVec := by
  intro v₁ v₂ hv
  let d : Fin 8 → ℤ := v₁ - v₂
  have hd : (Tag.cartan .E8).mulVec d = 0 := by
    rw [Matrix.mulVec_sub, hv, sub_self]
  have hrow : ∀ i : Fin 8, ∑ j : Fin 8, Tag.cartan .E8 i j * d j = 0 :=
    fun i => congrFun hd i
  have hM : Tag.cartan .E8 = !![
      2,  0, -1,  0,  0,  0,  0,  0;
      0,  2,  0, -1,  0,  0,  0,  0;
     -1,  0,  2, -1,  0,  0,  0,  0;
      0, -1, -1,  2, -1,  0,  0,  0;
      0,  0,  0, -1,  2, -1,  0,  0;
      0,  0,  0,  0, -1,  2, -1,  0;
      0,  0,  0,  0,  0, -1,  2, -1;
      0,  0,  0,  0,  0,  0, -1,  2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have hr0 := hrow 0; have hr1 := hrow 1; have hr2 := hrow 2; have hr3 := hrow 3
  have hr4 := hrow 4; have hr5 := hrow 5; have hr6 := hrow 6; have hr7 := hrow 7
  simp [hM, Fin.sum_univ_eight] at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  have h0 : d 0 = 0 := by omega
  have h1 : d 1 = 0 := by omega
  have h2 : d 2 = 0 := by omega
  have h3 : d 3 = 0 := by omega
  have h4 : d 4 = 0 := by omega
  have h5 : d 5 = 0 := by omega
  have h6 : d 6 = 0 := by omega
  have h7 : d 7 = 0 := by omega
  have hd0 : ∀ i : Fin 8, d i = 0 := by
    intro i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
  ext i
  exact sub_eq_zero.mp (hd0 i)

theorem e8RootEigenvalue_eq_imp {r₁ r₂ : Fin 240}
    (h : ∀ i : Fin 8, e8RootEigenvalue i r₁ = e8RootEigenvalue i r₂) : r₁ = r₂ := by
  apply e8RootCoord_injective
  apply cartan_E8_mulVec_inj
  ext i
  exact h i

/-- Opposite-root involution `e8RootNeg : Fin 240 → Fin 240` sending `α ↦ -α`. -/
def e8RootNeg (r : Fin 240) : Fin 240 :=
  match r.val with
  | 0 => ⟨2, by decide⟩ | 1 => ⟨4, by decide⟩ | 2 => ⟨0, by decide⟩ | 3 => ⟨5, by decide⟩ | 4 => ⟨1, by decide⟩ | 5 => ⟨3, by decide⟩ | 6 => ⟨15, by decide⟩ | 7 => ⟨16, by decide⟩
  | 8 => ⟨17, by decide⟩ | 9 => ⟨18, by decide⟩ | 10 => ⟨19, by decide⟩ | 11 => ⟨20, by decide⟩ | 12 => ⟨21, by decide⟩ | 13 => ⟨22, by decide⟩ | 14 => ⟨23, by decide⟩ | 15 => ⟨6, by decide⟩
  | 16 => ⟨7, by decide⟩ | 17 => ⟨8, by decide⟩ | 18 => ⟨9, by decide⟩ | 19 => ⟨10, by decide⟩ | 20 => ⟨11, by decide⟩ | 21 => ⟨12, by decide⟩ | 22 => ⟨13, by decide⟩ | 23 => ⟨14, by decide⟩
  | 24 => ⟨44, by decide⟩ | 25 => ⟨46, by decide⟩ | 26 => ⟨47, by decide⟩ | 27 => ⟨34, by decide⟩ | 28 => ⟨38, by decide⟩ | 29 => ⟨41, by decide⟩ | 30 => ⟨42, by decide⟩ | 31 => ⟨43, by decide⟩
  | 32 => ⟨36, by decide⟩ | 33 => ⟨39, by decide⟩ | 34 => ⟨27, by decide⟩ | 35 => ⟨45, by decide⟩ | 36 => ⟨32, by decide⟩ | 37 => ⟨40, by decide⟩ | 38 => ⟨28, by decide⟩ | 39 => ⟨33, by decide⟩
  | 40 => ⟨37, by decide⟩ | 41 => ⟨29, by decide⟩ | 42 => ⟨30, by decide⟩ | 43 => ⟨31, by decide⟩ | 44 => ⟨24, by decide⟩ | 45 => ⟨35, by decide⟩ | 46 => ⟨25, by decide⟩ | 47 => ⟨26, by decide⟩
  | 48 => ⟨63, by decide⟩ | 49 => ⟨62, by decide⟩ | 50 => ⟨57, by decide⟩ | 51 => ⟨56, by decide⟩ | 52 => ⟨59, by decide⟩ | 53 => ⟨58, by decide⟩ | 54 => ⟨61, by decide⟩ | 55 => ⟨60, by decide⟩
  | 56 => ⟨51, by decide⟩ | 57 => ⟨50, by decide⟩ | 58 => ⟨53, by decide⟩ | 59 => ⟨52, by decide⟩ | 60 => ⟨55, by decide⟩ | 61 => ⟨54, by decide⟩ | 62 => ⟨49, by decide⟩ | 63 => ⟨48, by decide⟩
  | 64 => ⟨79, by decide⟩ | 65 => ⟨78, by decide⟩ | 66 => ⟨73, by decide⟩ | 67 => ⟨72, by decide⟩ | 68 => ⟨75, by decide⟩ | 69 => ⟨74, by decide⟩ | 70 => ⟨77, by decide⟩ | 71 => ⟨76, by decide⟩
  | 72 => ⟨67, by decide⟩ | 73 => ⟨66, by decide⟩ | 74 => ⟨69, by decide⟩ | 75 => ⟨68, by decide⟩ | 76 => ⟨71, by decide⟩ | 77 => ⟨70, by decide⟩ | 78 => ⟨65, by decide⟩ | 79 => ⟨64, by decide⟩
  | 80 => ⟨95, by decide⟩ | 81 => ⟨94, by decide⟩ | 82 => ⟨89, by decide⟩ | 83 => ⟨88, by decide⟩ | 84 => ⟨91, by decide⟩ | 85 => ⟨90, by decide⟩ | 86 => ⟨93, by decide⟩ | 87 => ⟨92, by decide⟩
  | 88 => ⟨83, by decide⟩ | 89 => ⟨82, by decide⟩ | 90 => ⟨85, by decide⟩ | 91 => ⟨84, by decide⟩ | 92 => ⟨87, by decide⟩ | 93 => ⟨86, by decide⟩ | 94 => ⟨81, by decide⟩ | 95 => ⟨80, by decide⟩
  | 96 => ⟨175, by decide⟩ | 97 => ⟨172, by decide⟩ | 98 => ⟨173, by decide⟩ | 99 => ⟨174, by decide⟩ | 100 => ⟨169, by decide⟩ | 101 => ⟨170, by decide⟩ | 102 => ⟨171, by decide⟩ | 103 => ⟨168, by decide⟩
  | 104 => ⟨183, by decide⟩ | 105 => ⟨180, by decide⟩ | 106 => ⟨181, by decide⟩ | 107 => ⟨182, by decide⟩ | 108 => ⟨177, by decide⟩ | 109 => ⟨178, by decide⟩ | 110 => ⟨179, by decide⟩ | 111 => ⟨176, by decide⟩
  | 112 => ⟨191, by decide⟩ | 113 => ⟨188, by decide⟩ | 114 => ⟨189, by decide⟩ | 115 => ⟨190, by decide⟩ | 116 => ⟨185, by decide⟩ | 117 => ⟨186, by decide⟩ | 118 => ⟨187, by decide⟩ | 119 => ⟨184, by decide⟩
  | 120 => ⟨199, by decide⟩ | 121 => ⟨196, by decide⟩ | 122 => ⟨197, by decide⟩ | 123 => ⟨198, by decide⟩ | 124 => ⟨193, by decide⟩ | 125 => ⟨194, by decide⟩ | 126 => ⟨195, by decide⟩ | 127 => ⟨192, by decide⟩
  | 128 => ⟨207, by decide⟩ | 129 => ⟨204, by decide⟩ | 130 => ⟨205, by decide⟩ | 131 => ⟨206, by decide⟩ | 132 => ⟨201, by decide⟩ | 133 => ⟨202, by decide⟩ | 134 => ⟨203, by decide⟩ | 135 => ⟨200, by decide⟩
  | 136 => ⟨215, by decide⟩ | 137 => ⟨212, by decide⟩ | 138 => ⟨213, by decide⟩ | 139 => ⟨214, by decide⟩ | 140 => ⟨209, by decide⟩ | 141 => ⟨210, by decide⟩ | 142 => ⟨211, by decide⟩ | 143 => ⟨208, by decide⟩
  | 144 => ⟨223, by decide⟩ | 145 => ⟨220, by decide⟩ | 146 => ⟨221, by decide⟩ | 147 => ⟨222, by decide⟩ | 148 => ⟨217, by decide⟩ | 149 => ⟨218, by decide⟩ | 150 => ⟨219, by decide⟩ | 151 => ⟨216, by decide⟩
  | 152 => ⟨231, by decide⟩ | 153 => ⟨228, by decide⟩ | 154 => ⟨229, by decide⟩ | 155 => ⟨230, by decide⟩ | 156 => ⟨225, by decide⟩ | 157 => ⟨226, by decide⟩ | 158 => ⟨227, by decide⟩ | 159 => ⟨224, by decide⟩
  | 160 => ⟨239, by decide⟩ | 161 => ⟨236, by decide⟩ | 162 => ⟨237, by decide⟩ | 163 => ⟨238, by decide⟩ | 164 => ⟨233, by decide⟩ | 165 => ⟨234, by decide⟩ | 166 => ⟨235, by decide⟩ | 167 => ⟨232, by decide⟩
  | 168 => ⟨103, by decide⟩ | 169 => ⟨100, by decide⟩ | 170 => ⟨101, by decide⟩ | 171 => ⟨102, by decide⟩ | 172 => ⟨97, by decide⟩ | 173 => ⟨98, by decide⟩ | 174 => ⟨99, by decide⟩ | 175 => ⟨96, by decide⟩
  | 176 => ⟨111, by decide⟩ | 177 => ⟨108, by decide⟩ | 178 => ⟨109, by decide⟩ | 179 => ⟨110, by decide⟩ | 180 => ⟨105, by decide⟩ | 181 => ⟨106, by decide⟩ | 182 => ⟨107, by decide⟩ | 183 => ⟨104, by decide⟩
  | 184 => ⟨119, by decide⟩ | 185 => ⟨116, by decide⟩ | 186 => ⟨117, by decide⟩ | 187 => ⟨118, by decide⟩ | 188 => ⟨113, by decide⟩ | 189 => ⟨114, by decide⟩ | 190 => ⟨115, by decide⟩ | 191 => ⟨112, by decide⟩
  | 192 => ⟨127, by decide⟩ | 193 => ⟨124, by decide⟩ | 194 => ⟨125, by decide⟩ | 195 => ⟨126, by decide⟩ | 196 => ⟨121, by decide⟩ | 197 => ⟨122, by decide⟩ | 198 => ⟨123, by decide⟩ | 199 => ⟨120, by decide⟩
  | 200 => ⟨135, by decide⟩ | 201 => ⟨132, by decide⟩ | 202 => ⟨133, by decide⟩ | 203 => ⟨134, by decide⟩ | 204 => ⟨129, by decide⟩ | 205 => ⟨130, by decide⟩ | 206 => ⟨131, by decide⟩ | 207 => ⟨128, by decide⟩
  | 208 => ⟨143, by decide⟩ | 209 => ⟨140, by decide⟩ | 210 => ⟨141, by decide⟩ | 211 => ⟨142, by decide⟩ | 212 => ⟨137, by decide⟩ | 213 => ⟨138, by decide⟩ | 214 => ⟨139, by decide⟩ | 215 => ⟨136, by decide⟩
  | 216 => ⟨151, by decide⟩ | 217 => ⟨148, by decide⟩ | 218 => ⟨149, by decide⟩ | 219 => ⟨150, by decide⟩ | 220 => ⟨145, by decide⟩ | 221 => ⟨146, by decide⟩ | 222 => ⟨147, by decide⟩ | 223 => ⟨144, by decide⟩
  | 224 => ⟨159, by decide⟩ | 225 => ⟨156, by decide⟩ | 226 => ⟨157, by decide⟩ | 227 => ⟨158, by decide⟩ | 228 => ⟨153, by decide⟩ | 229 => ⟨154, by decide⟩ | 230 => ⟨155, by decide⟩ | 231 => ⟨152, by decide⟩
  | 232 => ⟨167, by decide⟩ | 233 => ⟨164, by decide⟩ | 234 => ⟨165, by decide⟩ | 235 => ⟨166, by decide⟩ | 236 => ⟨161, by decide⟩ | 237 => ⟨162, by decide⟩ | 238 => ⟨163, by decide⟩ | _ => ⟨160, by decide⟩

@[simp] theorem e8RootNeg_involutive (r : Fin 240) : e8RootNeg (e8RootNeg r) = r := by
  have h := forall_fin240_of_blocks (fun r => e8RootNeg (e8RootNeg r) == r)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) r
  simpa [beq_iff_eq] using h

theorem cartan8Weight_neg (r : Fin 240) :
    cartan8Weight (e8RootNeg r) = -cartan8Weight r := by
  have h := forall_fin240_of_blocks
    (fun r => List.ofFn (cartan8Weight (e8RootNeg r)) == List.ofFn (-cartan8Weight r))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) r
  simp only [beq_iff_eq] at h
  exact List.ofFn_injective h

theorem e8RootCoord_neg (r : Fin 240) :
    e8RootCoord (e8RootNeg r) = -e8RootCoord r := by
  have h := forall_fin240_of_blocks
    (fun r => List.ofFn (e8RootCoord (e8RootNeg r)) == List.ofFn (-e8RootCoord r))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) r
  simp only [beq_iff_eq] at h
  exact List.ofFn_injective h

theorem e8RootWeight_neg (r : Fin 240) :
    e8RootWeight (e8RootNeg r) = -e8RootWeight r := by
  apply splitE8CartanBasis.ext
  intro a
  have ha : (splitE8CartanBasis a : splitE8Cartan) = ⟨cartan8 a, cartan8_mem_splitE8Cartan a⟩ :=
    Subtype.ext (splitE8CartanBasis_apply a)
  rw [ha, LinearMap.neg_apply, e8RootWeight_cartan8, e8RootWeight_cartan8, cartan8Weight_neg]
  simp

theorem e8SimpleE_eq_rootVec (i : Fin 8) : e8SimpleE i = e8RootVec (e8ESimpleIdx i) := rfl

theorem e8SimpleF_eq_rootVec (i : Fin 8) :
    e8SimpleF i = e8FSimpleScale i • e8RootVec (e8FSimpleIdx i) := rfl

theorem e8Simple_bracket_EF_same (i : Fin 8) : ⁅e8SimpleE i, e8SimpleF i⁆ = e8SimpleH i := rfl

private theorem e8ESimpleIdx_weight_diff_not_mem_range {i j : Fin 8} (hij : i ≠ j) :
    ∀ r : Fin 240, ∃ a : Fin 8,
      cartan8Weight (e8ESimpleIdx i) a + cartan8Weight (e8FSimpleIdx j) a ≠ cartan8Weight r a := by
  intro r
  have hchk := forall_fin240_of_blocks
    (fun r => (List.finRange 8).all fun i => (List.finRange 8).all fun j =>
      if i == j then true
      else (List.finRange 8).any fun a =>
        cartan8Weight (e8ESimpleIdx i) a + cartan8Weight (e8FSimpleIdx j) a !=
          cartan8Weight r a)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) r
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hij' := hchk i j
  have hne : (i == j) = false := beq_false_of_ne hij
  simp only [hne, Bool.false_eq_true, ↓reduceIte, List.any_eq_true, List.mem_finRange,
    true_and, bne_iff_ne, ne_eq] at hij'
  exact hij'

private theorem e8ESimpleIdx_weight_diff_ne_zero {i j : Fin 8} (hij : i ≠ j) :
    ∃ a : Fin 8, cartan8Weight (e8ESimpleIdx i) a + cartan8Weight (e8FSimpleIdx j) a ≠ 0 := by
  have hchk : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      if i == j then true
      else (List.finRange 8).any (fun a =>
        cartan8Weight (e8ESimpleIdx i) a + cartan8Weight (e8FSimpleIdx j) a != 0))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have hij' := hchk i j
  have hne : (i == j) = false := beq_false_of_ne hij
  simp only [hne, Bool.false_eq_true, ↓reduceIte, List.any_eq_true, List.mem_finRange,
    true_and, bne_iff_ne, ne_eq] at hij'
  exact hij'

theorem e8Simple_bracket_EF_ne {i j : Fin 8} (hij : i ≠ j) :
    ⁅e8SimpleE i, e8SimpleF j⁆ = 0 := by
  rw [e8SimpleE_eq_rootVec, e8SimpleF_eq_rootVec, lie_smul]
  suffices h0 : ⁅e8RootVec (e8ESimpleIdx i), e8RootVec (e8FSimpleIdx j)⁆ = 0 by
    rw [h0, smul_zero]
  set x := ⁅e8RootVec (e8ESimpleIdx i), e8RootVec (e8FSimpleIdx j)⁆
  have hrep := splitE8Cartan8Basis.sum_repr x
  rw [Fintype.sum_sum_type] at hrep
  simp only [splitE8Cartan8Basis_inl, splitE8Cartan8Basis_inr] at hrep
  let hpart := ∑ a : Fin 8, (splitE8Cartan8Basis.repr x) (Sum.inl a) • cartan8 a
  have hh_mem : hpart ∈ splitE8Cartan :=
    Submodule.sum_mem _ fun a _ => splitE8Cartan.smul_mem _ (cartan8_mem_splitE8Cartan a)
  have h_eig : ∀ a : Fin 8, ⁅cartan8 a, x⁆ =
      ((cartan8Weight (e8ESimpleIdx i) a + cartan8Weight (e8FSimpleIdx j) a : ℤ) : ℝ) • x := by
    intro a
    dsimp [x]
    rw [leibniz_lie, e8RootVec_bracket_cartan8, e8RootVec_bracket_cartan8, smul_lie, lie_smul,
      ← add_smul]
    norm_cast
  have hc0 : ∀ a : Fin 8,
      ⁅cartan8 a, x⁆ = ∑ r : Fin 240, ((splitE8Cartan8Basis.repr x) (Sum.inr r) *
        (cartan8Weight r a : ℝ)) • e8RootVec r := by
    intro a
    conv_lhs => rw [← hrep]
    have hk : ⁅cartan8 a, hpart⁆ = 0 := by
      have hc := (inferInstance : IsLieAbelian splitE8Cartan).trivial
        ⟨cartan8 a, cartan8_mem_splitE8Cartan a⟩ ⟨hpart, hh_mem⟩
      exact congrArg Subtype.val hc
    rw [lie_add, hk, zero_add, lie_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [lie_smul, e8RootVec_bracket_cartan8, smul_smul]
  have hr_zero : ∀ r : Fin 240, (splitE8Cartan8Basis.repr x) (Sum.inr r) = 0 := by
    intro r
    obtain ⟨a, ha⟩ := e8ESimpleIdx_weight_diff_not_mem_range hij r
    let lam : ℝ := (cartan8Weight (e8ESimpleIdx i) a + cartan8Weight (e8FSimpleIdx j) a : ℤ)
    have hdiff : lam • hpart + ∑ q : Fin 240, (splitE8Cartan8Basis.repr x (Sum.inr q) *
        (lam - (cartan8Weight q a : ℝ))) • e8RootVec q = 0 := by
      have heq : lam • x - ⁅cartan8 a, x⁆ = 0 := by
        rw [h_eig a, sub_self]
      have h1 : lam • x = lam • hpart + ∑ q : Fin 240,
          lam • ((splitE8Cartan8Basis.repr x) (Sum.inr q) • e8RootVec q) := by
        conv_lhs => rw [← hrep]
        rw [smul_add]
        congr 1
        rw [Finset.smul_sum]
      rw [h1, hc0 a] at heq
      have hsub : lam • hpart + ∑ q : Fin 240, lam • (splitE8Cartan8Basis.repr x (Sum.inr q) •
          e8RootVec q) - ∑ q : Fin 240, (splitE8Cartan8Basis.repr x (Sum.inr q) *
          (cartan8Weight q a : ℝ)) • e8RootVec q =
        lam • hpart + ∑ q : Fin 240, (splitE8Cartan8Basis.repr x (Sum.inr q) *
          (lam - (cartan8Weight q a : ℝ))) • e8RootVec q := by
        rw [add_sub_assoc, ← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [smul_smul, ← sub_smul]
        congr 1; ring
      rw [← heq]
      exact hsub.symm
    have hkill := e8_cartan_weight_kill_mem ⊥
      (fun _ y hy => by rw [Submodule.mem_bot] at hy; subst hy; simp)
      Finset.univ (lam • hpart) (splitE8Cartan.smul_mem lam hh_mem)
      (fun q => splitE8Cartan8Basis.repr x (Sum.inr q) * (lam - (cartan8Weight q a : ℝ)))
      (by rw [hdiff]; exact Submodule.zero_mem _)
    have hr' := (Submodule.mem_bot ℝ).mp (hkill.2 r (Finset.mem_univ r))
    have hmul := (smul_eq_zero.mp hr').resolve_right (e8RootVec_ne_zero r)
    have hlam_ne : lam - (cartan8Weight r a : ℝ) ≠ 0 := by
      intro h0
      apply ha
      exact Int.cast_injective (sub_eq_zero.mp h0)
    exact (mul_eq_zero.mp hmul).resolve_right hlam_ne
  have hs0 : ∑ r : Fin 240, splitE8Cartan8Basis.repr x (Sum.inr r) • e8RootVec r = 0 :=
    Finset.sum_eq_zero fun r _ => by rw [hr_zero r, zero_smul]
  have hx_cartan : x = hpart := by rw [← hrep, hs0, add_zero]
  obtain ⟨a₀, ha₀⟩ := e8ESimpleIdx_weight_diff_ne_zero hij
  have hbr0 : ⁅cartan8 a₀, x⁆ = 0 := by
    rw [hx_cartan]
    have hc := (inferInstance : IsLieAbelian splitE8Cartan).trivial
      ⟨cartan8 a₀, cartan8_mem_splitE8Cartan a₀⟩ ⟨hpart, hh_mem⟩
    exact congrArg Subtype.val hc
  rw [h_eig a₀] at hbr0
  exact (smul_eq_zero.mp hbr0).resolve_left (Int.cast_ne_zero.mpr ha₀)

theorem e8RootEigenvalue_simpleE (i j : Fin 8) :
    e8RootEigenvalue i (e8ESimpleIdx j) = Tag.cartan .E8 i j := by
  have hchk : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      e8RootEigenvalue i (e8ESimpleIdx j) == Tag.cartan .E8 i j)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
  exact hchk i j

theorem e8RootEigenvalue_simpleF (i j : Fin 8) :
    e8RootEigenvalue i (e8FSimpleIdx j) = -Tag.cartan .E8 i j := by
  have hchk : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      e8RootEigenvalue i (e8FSimpleIdx j) == -Tag.cartan .E8 i j)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
  exact hchk i j

theorem e8Simple_bracket_HE (i j : Fin 8) :
    ⁅e8SimpleH i, e8SimpleE j⁆ = ((Tag.cartan .E8 i j : ℤ) : ℝ) • e8SimpleE j := by
  rw [e8SimpleE_eq_rootVec, e8RootVec_bracket_H, e8RootEigenvalue_simpleE]

theorem e8Simple_bracket_HF (i j : Fin 8) :
    ⁅e8SimpleH i, e8SimpleF j⁆ = (-(Tag.cartan .E8 i j : ℤ) : ℝ) • e8SimpleF j := by
  rw [e8SimpleF_eq_rootVec, lie_smul, e8RootVec_bracket_H, e8RootEigenvalue_simpleF]
  simp only [Int.cast_neg, smul_smul, mul_comm]

theorem e8Simple_isSl2Triple (i : Fin 8) :
    IsSl2Triple (e8SimpleH i) (e8SimpleE i) (e8SimpleF i) where
  h_ne_zero := by
    intro h0
    have hc := Fintype.linearIndependent_iff.mp e8SimpleH_linearIndependent
      (fun j => if j = i then 1 else 0) (by simp [h0]) i
    norm_num at hc
  lie_e_f := e8Simple_bracket_EF_same i
  lie_h_e_nsmul := by
    rw [e8Simple_bracket_HE]
    have hc : Tag.cartan .E8 i i = 2 := by fin_cases i <;> decide
    rw [hc, ← Nat.cast_smul_eq_nsmul ℝ]
    norm_num
  lie_h_f_nsmul := by
    rw [e8Simple_bracket_HF]
    have hc : Tag.cartan .E8 i i = 2 := by fin_cases i <;> decide
    rw [hc, ← Nat.cast_smul_eq_nsmul ℝ, ← neg_smul]
    norm_num

theorem e8RootVec_opposite_bracket_mem_cartan {r₁ r₂ : Fin 240}
    (hopp : e8RootCoord r₁ + e8RootCoord r₂ = 0) :
    ⁅e8RootVec r₁, e8RootVec r₂⁆ ∈ splitE8Cartan := by
  rw [← splitE8Cartan_isCartanSubalgebra.self_normalizing, LieSubalgebra.mem_normalizer_iff]
  intro H hH
  have hH' : H ∈ Submodule.span ℝ (Set.range e8SimpleH) := by
    change H ∈ splitE8Cartan.toSubmodule at hH
    rwa [← splitE8Cartan_eq_span_e8SimpleH]
  clear hH
  have hcomm : ∀ i : Fin 8, ⁅e8SimpleH i, ⁅e8RootVec r₁, e8RootVec r₂⁆⁆ = 0 := by
    intro i
    rw [leibniz_lie, e8RootVec_bracket_H, e8RootVec_bracket_H, smul_lie, lie_smul, ← add_smul]
    have hsum : e8RootEigenvalue i r₁ + e8RootEigenvalue i r₂ = 0 := by
      simp only [e8RootEigenvalue, ← Finset.sum_add_distrib, ← mul_add]
      have h0 : ∀ j : Fin 8, e8RootCoord r₁ j + e8RootCoord r₂ j = 0 :=
        fun j => congrFun hopp j
      simp [h0]
    have hsumR : (e8RootEigenvalue i r₁ : ℝ) + (e8RootEigenvalue i r₂ : ℝ) = 0 := by
      exact_mod_cast hsum
    rw [hsumR, zero_smul]
  induction hH' using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ ih₁ ih₂ => rw [lie_add]; exact splitE8Cartan.add_mem ih₁ ih₂
  | smul c _ _ ih => rw [lie_smul]; exact splitE8Cartan.smul_mem c ih
  | mem _ h =>
    rcases h with ⟨i, rfl⟩
    rw [← lie_skew, hcomm i, neg_zero]
    exact splitE8Cartan.zero_mem

theorem splitE8_cartan_eq_mathlib :
    Tag.cartan .E8 = CartanMatrix.E 8 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem e8_noncomm_witness : ⁅e8SimpleH 0, e8SimpleE 0⁆ ≠ 0 := by
  rw [e8Simple_bracket_HE]
  have hc : Tag.cartan .E8 (0 : Fin 8) (0 : Fin 8) = 2 := by decide
  rw [hc, e8SimpleE_eq_rootVec]
  intro h0
  have hsm := smul_eq_zero.mp h0
  norm_num at hsm
  exact e8RootVec_ne_zero (e8ESimpleIdx 0) hsm

end BourbakiE8SimpleSystem

end InfoGeometry.Algebra

end noncomputable section

