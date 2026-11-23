/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import InfoGeometry.Lie.SplitOctonionEllStabilizer

/-!
# Global Stabilizer Classification `Stab_{Aut(O_s)}(ℓ) ≃* SL₃(ℝ)`

This module closes `R2-Gap3` at the global group level on the canonical Zorn
split-octonion automorphism carrier `realZornCompositionAut`:
1. Defines the 3D cofactor matrix `cofactor3` and proves its polynomial
   multiplicativity, dot-pairing, and cross-product covariance identities.
2. Classifies the Peirce idempotent stabilizer `realZornPeirceStabilizer`
   (automorphisms fixing `OP1` and `OP2`) globally as `Matrix.SpecialLinearGroup (Fin 3) ℝ`
   via the fundamental `3` action on `x` and contragredient cofactor `3̄` action on `y`.
3. Constructs an explicit rational Hadamard split-octonion involution `hadamardSwapAut`
   exchanging `(ellChiralPlus, ellChiralMinus)` with `(OP1, OP2)` and `lUnit` with `kUnit`.
4. Conjugates `realZornEllStabilizer = realZornOrderedChiralPairStabilizer` by
   `hadamardSwapAut` to construct `realZornEllStabilizerMulEquivSL3 :
   realZornEllStabilizer ≃* Matrix.SpecialLinearGroup (Fin 3) ℝ`.

Native split-Clifford equivalence `Cl_split 3 ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ`
(`R2-Gap1` contract reconciliation) is owned separately in
`InfoGeometry.Clifford.SplitCliffordMatrixEquiv.splitSpinorAlgEquiv`.
Physical Daviau (2013) interpretation claims and full 14D `Aut(O_s) ≃ G_{2(2)}`
remain explicitly out of scope here.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionGlobalEllStabilizerSL3

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Lie.SplitOctonionEllStabilizer

abbrev SL3Group := Matrix.SpecialLinearGroup (Fin 3) ℝ
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev ZornC := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev ZDot := InfoGeometry.Canonical.ZornMatrix.dot (R := ℝ)
abbrev ZCross := InfoGeometry.Canonical.ZornMatrix.cross (R := ℝ)

/-! ## Trap T16 Non-Commutativity Witness & 3D Cofactor Identities -/

/-- Non-commutativity witness for `3 × 3` real matrix multiplication (Trap T16). -/
theorem mat3_mul_noncommutative :
    ∃ A B : Matrix (Fin 3) (Fin 3) ℝ, A * B ≠ B * A := by
  refine ⟨!![0, 1, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 1, 0, 0; 0, 0, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_three] at h00

/-- Classical cofactor matrix of a `3 × 3` real matrix, whose column `j` is the
cross product of the other two cyclic columns of `A`. -/
def cofactor3 (A : Mat3) : Mat3 :=
  ![![A 1 1 * A 2 2 - A 2 1 * A 1 2,
      A 1 2 * A 2 0 - A 2 2 * A 1 0,
      A 1 0 * A 2 1 - A 2 0 * A 1 1],
    ![A 2 1 * A 0 2 - A 0 1 * A 2 2,
      A 2 2 * A 0 0 - A 0 2 * A 2 0,
      A 2 0 * A 0 1 - A 0 0 * A 2 1],
    ![A 0 1 * A 1 2 - A 1 1 * A 0 2,
      A 0 2 * A 1 0 - A 1 2 * A 0 0,
      A 0 0 * A 1 1 - A 0 1 * A 1 0]]

theorem cofactor3_one : cofactor3 (1 : Mat3) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cofactor3]

theorem cofactor3_mul (A B : Mat3) :
    cofactor3 (A * B) = cofactor3 A * cofactor3 B := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [cofactor3, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

theorem cross_mulVec (A : Mat3) (x y : Fin 3 → ℝ) :
    ZCross (A.mulVec x) (A.mulVec y) = (cofactor3 A).mulVec (ZCross x y) := by
  funext i
  fin_cases i <;>
    simp [ZCross, InfoGeometry.Canonical.ZornMatrix.cross, cofactor3,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring

theorem cross_cofactor3_mulVec (A : Mat3) (x y : Fin 3 → ℝ) :
    ZCross ((cofactor3 A).mulVec x) ((cofactor3 A).mulVec y) =
      Matrix.det A • A.mulVec (ZCross x y) := by
  funext i
  fin_cases i <;>
    simp [ZCross, InfoGeometry.Canonical.ZornMatrix.cross, cofactor3,
      Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring

theorem dot_mulVec_cofactor3 (A : Mat3) (x y : Fin 3 → ℝ) :
    ZDot (A.mulVec x) ((cofactor3 A).mulVec y) = Matrix.det A * ZDot x y := by
  simp [ZDot, InfoGeometry.Canonical.ZornMatrix.dot, cofactor3,
    Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem dot_cofactor3_mulVec (A : Mat3) (x y : Fin 3 → ℝ) :
    ZDot ((cofactor3 A).mulVec x) (A.mulVec y) = Matrix.det A * ZDot x y := by
  simp [ZDot, InfoGeometry.Canonical.ZornMatrix.dot, cofactor3,
    Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-! ## Peirce Idempotent Stabilizer & Global Equivalence to `SL₃(ℝ)` -/

/-- Subgroup of canonical split-octonion automorphisms fixing the diagonal
Peirce idempotents `OP1` and `OP2`. -/
def realZornPeirceStabilizer : Subgroup realZornCompositionAut where
  carrier :=
    {φ |
      (φ : CanonicalLinearAut) (OP1 : ZornC) = (OP1 : ZornC) ∧
      (φ : CanonicalLinearAut) (OP2 : ZornC) = (OP2 : ZornC)}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := by
    intro φ ψ hφ hψ
    constructor
    · change (φ : CanonicalLinearAut) ((ψ : CanonicalLinearAut) (OP1 : ZornC)) = OP1
      rw [hψ.1, hφ.1]
    · change (φ : CanonicalLinearAut) ((ψ : CanonicalLinearAut) (OP2 : ZornC)) = OP2
      rw [hψ.2, hφ.2]
  inv_mem' := by
    intro φ hφ
    constructor
    · apply (φ : CanonicalLinearAut).injective
      change (φ : CanonicalLinearAut)
          ((φ : CanonicalLinearAut).symm (OP1 : ZornC)) =
        (φ : CanonicalLinearAut) (OP1 : ZornC)
      rw [LinearEquiv.apply_symm_apply, hφ.1]
    · apply (φ : CanonicalLinearAut).injective
      change (φ : CanonicalLinearAut)
          ((φ : CanonicalLinearAut).symm (OP2 : ZornC)) =
        (φ : CanonicalLinearAut) (OP2 : ZornC)
      rw [LinearEquiv.apply_symm_apply, hφ.2]

private abbrev peirceLin (φ : realZornPeirceStabilizer) : CanonicalLinearAut :=
  (φ.1 : CanonicalLinearAut)

/-- Linear automorphism of `ZornC` induced by `g ∈ SL₃(ℝ)` via `3` on `x` and
contragredient `cofactor3 g = (g⁻¹)ᵀ` on `y`. -/
noncomputable def sl3ToPeirceLinearEquiv (g : SL3Group) : CanonicalLinearAut where
  toFun X :=
    { a := X.a
      b := X.b
      x := (g : Mat3).mulVec X.x
      y := (cofactor3 (g : Mat3)).mulVec X.y }
  invFun X :=
    { a := X.a
      b := X.b
      x := ((g⁻¹ : SL3Group) : Mat3).mulVec X.x
      y := (cofactor3 ((g⁻¹ : SL3Group) : Mat3)).mulVec X.y }
  left_inv X := by
    have hmul : ((g⁻¹ : SL3Group) : Mat3) * (g : Mat3) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hcmul : cofactor3 ((g⁻¹ : SL3Group) : Mat3) * cofactor3 (g : Mat3) = 1 := by
      rw [← cofactor3_mul, hmul, cofactor3_one]
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · rfl
    · rfl
    · change ((g⁻¹ : SL3Group) : Mat3).mulVec ((g : Mat3).mulVec X.x) = X.x
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
    · change (cofactor3 ((g⁻¹ : SL3Group) : Mat3)).mulVec
          ((cofactor3 (g : Mat3)).mulVec X.y) = X.y
      rw [Matrix.mulVec_mulVec, hcmul, Matrix.one_mulVec]
  right_inv X := by
    have hmul : (g : Mat3) * ((g⁻¹ : SL3Group) : Mat3) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hcmul : cofactor3 (g : Mat3) * cofactor3 ((g⁻¹ : SL3Group) : Mat3) = 1 := by
      rw [← cofactor3_mul, hmul, cofactor3_one]
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · rfl
    · rfl
    · change (g : Mat3).mulVec (((g⁻¹ : SL3Group) : Mat3).mulVec X.x) = X.x
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
    · change (cofactor3 (g : Mat3)).mulVec
          ((cofactor3 ((g⁻¹ : SL3Group) : Mat3)).mulVec X.y) = X.y
      rw [Matrix.mulVec_mulVec, hcmul, Matrix.one_mulVec]
  map_add' X Y := by
    apply InfoGeometry.Canonical.ZornMatrix.ext <;>
      simp [Matrix.mulVec_add]
  map_smul' r X := by
    apply InfoGeometry.Canonical.ZornMatrix.ext <;>
      simp [Matrix.mulVec_smul]

theorem sl3ToPeirceLinearEquiv_mem_aut (g : SL3Group) :
    sl3ToPeirceLinearEquiv g ∈ realZornCompositionAut := by
  intro X Y
  have hdet : Matrix.det (g : Mat3) = 1 := Matrix.SpecialLinearGroup.det_coe g
  apply InfoGeometry.Canonical.ZornMatrix.ext <;>
    dsimp [sl3ToPeirceLinearEquiv, zMul]
  · rw [show InfoGeometry.Canonical.ZornMatrix.dot ((g : Mat3).mulVec X.x)
        ((cofactor3 (g : Mat3)).mulVec Y.y) =
      ZDot ((g : Mat3).mulVec X.x) ((cofactor3 (g : Mat3)).mulVec Y.y) from rfl]
    rw [dot_mulVec_cofactor3, hdet, one_mul]
  · rw [show InfoGeometry.Canonical.ZornMatrix.dot ((cofactor3 (g : Mat3)).mulVec X.y)
        ((g : Mat3).mulVec Y.x) =
      ZDot ((cofactor3 (g : Mat3)).mulVec X.y) ((g : Mat3).mulVec Y.x) from rfl]
    rw [dot_cofactor3_mulVec, hdet, one_mul]
  · rw [show InfoGeometry.Canonical.ZornMatrix.cross ((cofactor3 (g : Mat3)).mulVec X.y)
        ((cofactor3 (g : Mat3)).mulVec Y.y) =
      ZCross ((cofactor3 (g : Mat3)).mulVec X.y) ((cofactor3 (g : Mat3)).mulVec Y.y) from rfl]
    rw [cross_cofactor3_mulVec, hdet, one_smul]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul]
  · rw [show InfoGeometry.Canonical.ZornMatrix.cross ((g : Mat3).mulVec X.x)
        ((g : Mat3).mulVec Y.x) =
      ZCross ((g : Mat3).mulVec X.x) ((g : Mat3).mulVec Y.x) from rfl]
    rw [cross_mulVec]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul]

noncomputable def sl3ToPeirceAut (g : SL3Group) : realZornPeirceStabilizer :=
  ⟨⟨sl3ToPeirceLinearEquiv g, sl3ToPeirceLinearEquiv_mem_aut g⟩,
    ⟨by
      apply InfoGeometry.Canonical.ZornMatrix.ext <;>
        simp [sl3ToPeirceLinearEquiv, OP1]
    , by
      apply InfoGeometry.Canonical.ZornMatrix.ext <;>
        simp [sl3ToPeirceLinearEquiv, OP2]⟩⟩

private def upperEmbed (v : Fin 3 → ℝ) : ZornC :=
  { a := 0, b := 0, x := v, y := 0 }

private def lowerEmbed (w : Fin 3 → ℝ) : ZornC :=
  { a := 0, b := 0, x := 0, y := w }

private theorem zorn_decompose (X : ZornC) :
    X = X.a • (OP1 : ZornC) + X.b • (OP2 : ZornC) + upperEmbed X.x + lowerEmbed X.y := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [OP1, OP2, upperEmbed, lowerEmbed]
  · simp [OP1, OP2, upperEmbed, lowerEmbed]
  · funext i; fin_cases i <;> simp [OP1, OP2, upperEmbed, lowerEmbed]
  · funext i; fin_cases i <;> simp [OP1, OP2, upperEmbed, lowerEmbed]

private theorem upperEmbed_colorPart (v : Fin 3 → ℝ) :
    colorPart (upperEmbed v) = upperEmbed v := by
  rw [colorPart_shape]
  rfl

private theorem lowerEmbed_anticolorPart (w : Fin 3 → ℝ) :
    anticolorPart (lowerEmbed w) = lowerEmbed w := by
  rw [anticolorPart_shape]
  rfl

private theorem peirceLin_upperEmbed (φ : realZornPeirceStabilizer) (v : Fin 3 → ℝ) :
    peirceLin φ (upperEmbed v) = upperEmbed ((peirceLin φ (upperEmbed v)).x) := by
  have h1 := congrArg (peirceLin φ) (upperEmbed_colorPart v)
  dsimp [colorPart] at h1
  rw [realZornCompositionAut_preserves_mul, realZornCompositionAut_preserves_mul,
    φ.2.1, φ.2.2] at h1
  change colorPart (peirceLin φ (upperEmbed v)) = peirceLin φ (upperEmbed v) at h1
  rw [colorPart_shape] at h1
  exact h1.symm

private theorem peirceLin_lowerEmbed (φ : realZornPeirceStabilizer) (w : Fin 3 → ℝ) :
    peirceLin φ (lowerEmbed w) = lowerEmbed ((peirceLin φ (lowerEmbed w)).y) := by
  have h1 := congrArg (peirceLin φ) (lowerEmbed_anticolorPart w)
  dsimp [anticolorPart] at h1
  rw [realZornCompositionAut_preserves_mul, realZornCompositionAut_preserves_mul,
    φ.2.2, φ.2.1] at h1
  change anticolorPart (peirceLin φ (lowerEmbed w)) = peirceLin φ (lowerEmbed w) at h1
  rw [anticolorPart_shape] at h1
  exact h1.symm

private noncomputable def upperMat (φ : realZornPeirceStabilizer) : Mat3 :=
  fun i j => (peirceLin φ (upperEmbed (Pi.single j 1))).x i

private noncomputable def lowerMat (φ : realZornPeirceStabilizer) : Mat3 :=
  fun i j => (peirceLin φ (lowerEmbed (Pi.single j 1))).y i

private theorem upperEmbed_lin_expand (φ : realZornPeirceStabilizer) (v : Fin 3 → ℝ) :
    (peirceLin φ (upperEmbed v)).x = (upperMat φ).mulVec v := by
  have hv :
      upperEmbed v =
        v 0 • upperEmbed (Pi.single 0 1) +
        v 1 • upperEmbed (Pi.single 1 1) +
        v 2 • upperEmbed (Pi.single 2 1) := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp [upperEmbed]
    · simp [upperEmbed]
    · funext i; fin_cases i <;> simp [upperEmbed]
    · simp [upperEmbed]
  rw [hv, map_add, map_add, map_smul, map_smul, map_smul]
  funext i
  simp [upperMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

private theorem lowerEmbed_lin_expand (φ : realZornPeirceStabilizer) (w : Fin 3 → ℝ) :
    (peirceLin φ (lowerEmbed w)).y = (lowerMat φ).mulVec w := by
  have hw :
      lowerEmbed w =
        w 0 • lowerEmbed (Pi.single 0 1) +
        w 1 • lowerEmbed (Pi.single 1 1) +
        w 2 • lowerEmbed (Pi.single 2 1) := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp [lowerEmbed]
    · simp [lowerEmbed]
    · simp [lowerEmbed]
    · funext i; fin_cases i <;> simp [lowerEmbed]
  rw [hw, map_add, map_add, map_smul, map_smul, map_smul]
  funext i
  simp [lowerMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

private theorem peirceLin_action (φ : realZornPeirceStabilizer) (X : ZornC) :
    peirceLin φ X =
      { a := X.a
        b := X.b
        x := (upperMat φ).mulVec X.x
        y := (lowerMat φ).mulVec X.y } := by
  conv_lhs => rw [zorn_decompose X]
  rw [map_add, map_add, map_add, map_smul, map_smul, φ.2.1, φ.2.2,
    peirceLin_upperEmbed, peirceLin_lowerEmbed,
    upperEmbed_lin_expand, lowerEmbed_lin_expand]
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [OP1, OP2, upperEmbed, lowerEmbed]
  · simp [OP1, OP2, upperEmbed, lowerEmbed]
  · funext i; fin_cases i <;> simp [OP1, OP2, upperEmbed, lowerEmbed]
  · funext i; fin_cases i <;> simp [OP1, OP2, upperEmbed, lowerEmbed]

private theorem upperEmbed_mul_upperEmbed_pair (j1 j2 : Fin 3) :
    zMul (upperEmbed (Pi.single j1 1)) (upperEmbed (Pi.single j2 1)) =
      lowerEmbed (ZCross (Pi.single j1 1) (Pi.single j2 1)) := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [zMul, upperEmbed, lowerEmbed, InfoGeometry.Canonical.ZornMatrix.dot]
  · simp [zMul, upperEmbed, lowerEmbed, InfoGeometry.Canonical.ZornMatrix.dot]
  · funext i; fin_cases i <;> simp [zMul, upperEmbed, lowerEmbed,
      InfoGeometry.Canonical.ZornMatrix.cross]
  · funext i; fin_cases i <;> simp [zMul, upperEmbed, lowerEmbed, ZCross,
      InfoGeometry.Canonical.ZornMatrix.cross]

private theorem lowerMat_eq_cofactor3_upperMat (φ : realZornPeirceStabilizer) :
    lowerMat φ = cofactor3 (upperMat φ) := by
  have hpair : ∀ j1 j2 : Fin 3,
      (peirceLin φ (lowerEmbed (ZCross (Pi.single j1 1) (Pi.single j2 1)))).y =
        ZCross ((upperMat φ).mulVec (Pi.single j1 1))
          ((upperMat φ).mulVec (Pi.single j2 1)) := by
    intro j1 j2
    have hmul := realZornCompositionAut_preserves_mul φ.1
      (upperEmbed (Pi.single j1 1)) (upperEmbed (Pi.single j2 1))
    rw [upperEmbed_mul_upperEmbed_pair] at hmul
    have hy := congrArg (fun Z : ZornC => Z.y) hmul
    rw [peirceLin_action φ (upperEmbed (Pi.single j1 1)),
      peirceLin_action φ (upperEmbed (Pi.single j2 1))] at hy
    simpa [zMul, upperEmbed, ZCross] using hy
  have h01 := hpair 1 2
  have h12 := hpair 2 0
  have h20 := hpair 0 1
  have c0 : ZCross (Pi.single (1 : Fin 3) (1 : ℝ)) (Pi.single 2 1) = Pi.single 0 1 := by
    funext i; fin_cases i <;> simp [ZCross, InfoGeometry.Canonical.ZornMatrix.cross]
  have c1 : ZCross (Pi.single (2 : Fin 3) (1 : ℝ)) (Pi.single 0 1) = Pi.single 1 1 := by
    funext i; fin_cases i <;> simp [ZCross, InfoGeometry.Canonical.ZornMatrix.cross]
  have c2 : ZCross (Pi.single (0 : Fin 3) (1 : ℝ)) (Pi.single 1 1) = Pi.single 2 1 := by
    funext i; fin_cases i <;> simp [ZCross, InfoGeometry.Canonical.ZornMatrix.cross]
  rw [c0] at h01
  rw [c1] at h12
  rw [c2] at h20
  ext i j
  fin_cases j
  · have h := congrFun h01 i
    fin_cases i <;>
      simp [lowerMat, upperMat, cofactor3, ZCross, InfoGeometry.Canonical.ZornMatrix.cross,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h ⊢ <;>
      linarith
  · have h := congrFun h12 i
    fin_cases i <;>
      simp [lowerMat, upperMat, cofactor3, ZCross, InfoGeometry.Canonical.ZornMatrix.cross,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h ⊢ <;>
      linarith
  · have h := congrFun h20 i
    fin_cases i <;>
      simp [lowerMat, upperMat, cofactor3, ZCross, InfoGeometry.Canonical.ZornMatrix.cross,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h ⊢ <;>
      linarith

private theorem upperMat_det_one (φ : realZornPeirceStabilizer) :
    Matrix.det (upperMat φ) = 1 := by
  have he : zMul (upperEmbed (Pi.single 0 1)) (lowerEmbed (Pi.single 0 1)) = (OP1 : ZornC) := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp [zMul, upperEmbed, lowerEmbed, OP1, InfoGeometry.Canonical.ZornMatrix.dot]
    · simp [zMul, upperEmbed, lowerEmbed, OP1, InfoGeometry.Canonical.ZornMatrix.dot]
    · funext i; fin_cases i <;> simp [zMul, upperEmbed, lowerEmbed, OP1,
        InfoGeometry.Canonical.ZornMatrix.cross]
    · funext i; fin_cases i <;> simp [zMul, upperEmbed, lowerEmbed, OP1,
        InfoGeometry.Canonical.ZornMatrix.cross]
  have hmul := realZornCompositionAut_preserves_mul φ.1
    (upperEmbed (Pi.single 0 1)) (lowerEmbed (Pi.single 0 1))
  rw [he, show (φ.1 : CanonicalLinearAut) (OP1 : ZornC) = (OP1 : ZornC) from φ.2.1] at hmul
  have ha := congrArg (fun Z : ZornC => Z.a) hmul
  rw [peirceLin_action φ (upperEmbed (Pi.single 0 1)),
    peirceLin_action φ (lowerEmbed (Pi.single 0 1)),
    lowerMat_eq_cofactor3_upperMat φ] at ha
  dsimp [zMul, upperEmbed, lowerEmbed, OP1] at ha
  rw [show (0 : ℝ) * 0 + InfoGeometry.Canonical.ZornMatrix.dot
      ((upperMat φ).mulVec (Pi.single 0 1))
      ((cofactor3 (upperMat φ)).mulVec (Pi.single 0 1)) =
    ZDot ((upperMat φ).mulVec (Pi.single 0 1))
      ((cofactor3 (upperMat φ)).mulVec (Pi.single 0 1)) by ring] at ha
  rw [dot_mulVec_cofactor3] at ha
  have hdot1 : ZDot (Pi.single (0 : Fin 3) (1 : ℝ)) (Pi.single 0 1) = 1 := by
    simp [ZDot, InfoGeometry.Canonical.ZornMatrix.dot]
  rw [hdot1, mul_one] at ha
  exact ha.symm

private noncomputable def peirceAutToSL3 (φ : realZornPeirceStabilizer) : SL3Group :=
  ⟨upperMat φ, upperMat_det_one φ⟩

/-- Global group isomorphism `realZornPeirceStabilizer ≃* SL₃(ℝ)` acting via the
fundamental `3` representation on `x` and contragredient `cofactor3 = (·⁻¹)ᵀ` on `y`. -/
noncomputable def realZornPeirceStabilizerMulEquivSL3 :
    realZornPeirceStabilizer ≃* SL3Group where
  toFun := peirceAutToSL3
  invFun := sl3ToPeirceAut
  left_inv φ := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    change peirceLin (sl3ToPeirceAut (peirceAutToSL3 φ)) X = peirceLin φ X
    rw [peirceLin_action φ X]
    simp [peirceLin, sl3ToPeirceAut, sl3ToPeirceLinearEquiv, peirceAutToSL3,
      lowerMat_eq_cofactor3_upperMat]
  right_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change upperMat (sl3ToPeirceAut g) i j = (g : Mat3) i j
    fin_cases i <;> fin_cases j <;>
      simp [upperMat, peirceLin, sl3ToPeirceAut, sl3ToPeirceLinearEquiv, upperEmbed]
  map_mul' φ ψ := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change upperMat (φ * ψ) i j = (upperMat φ * upperMat ψ) i j
    have hcomp : peirceLin (φ * ψ) (upperEmbed (Pi.single j 1)) =
        peirceLin φ (peirceLin ψ (upperEmbed (Pi.single j 1))) := rfl
    rw [upperMat, hcomp, peirceLin_action ψ, peirceLin_action φ]
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;>
      simp [upperEmbed, upperMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-! ## Hadamard Involution Conjugating `ℓ`-Stabilizer to Peirce Stabilizer (`R2-Gap3`) -/

/-- Explicit rational Hadamard linear automorphism of `ZornC` exchanging
`(ellChiralPlus, ellChiralMinus)` with `(OP1, OP2)` and `lUnit` with `kUnit`. -/
noncomputable def hadamardSwapLinearEquiv : CanonicalLinearAut where
  toFun X :=
    { a := (1 / 2 : ℝ) * (X.a + X.b + X.x 0 + X.y 0)
      b := (1 / 2 : ℝ) * (X.a + X.b - X.x 0 - X.y 0)
      x := ![(1 / 2 : ℝ) * (X.a - X.b - X.x 0 + X.y 0),
             (1 / 2 : ℝ) * (X.x 1 + X.x 2 - X.y 1 + X.y 2),
             (1 / 2 : ℝ) * (X.x 1 - X.x 2 + X.y 1 + X.y 2)]
      y := ![(1 / 2 : ℝ) * (X.a - X.b + X.x 0 - X.y 0),
             (1 / 2 : ℝ) * (-X.x 1 + X.x 2 + X.y 1 + X.y 2),
             (1 / 2 : ℝ) * (X.x 1 + X.x 2 + X.y 1 - X.y 2)] }
  invFun X :=
    { a := (1 / 2 : ℝ) * (X.a + X.b + X.x 0 + X.y 0)
      b := (1 / 2 : ℝ) * (X.a + X.b - X.x 0 - X.y 0)
      x := ![(1 / 2 : ℝ) * (X.a - X.b - X.x 0 + X.y 0),
             (1 / 2 : ℝ) * (X.x 1 + X.x 2 - X.y 1 + X.y 2),
             (1 / 2 : ℝ) * (X.x 1 - X.x 2 + X.y 1 + X.y 2)]
      y := ![(1 / 2 : ℝ) * (X.a - X.b + X.x 0 - X.y 0),
             (1 / 2 : ℝ) * (-X.x 1 + X.x 2 + X.y 1 + X.y 2),
             (1 / 2 : ℝ) * (X.x 1 + X.x 2 + X.y 1 - X.y 2)] }
  left_inv X := by
    apply InfoGeometry.Canonical.ZornMatrix.ext <;> dsimp
    · ring
    · ring
    · funext i; fin_cases i <;> simp <;> ring
    · funext i; fin_cases i <;> simp <;> ring
  right_inv X := by
    apply InfoGeometry.Canonical.ZornMatrix.ext <;> dsimp
    · ring
    · ring
    · funext i; fin_cases i <;> simp <;> ring
    · funext i; fin_cases i <;> simp <;> ring
  map_add' X Y := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp; ring
    · simp; ring
    · funext i; fin_cases i <;> simp <;> ring
    · funext i; fin_cases i <;> simp <;> ring
  map_smul' r X := by
    apply InfoGeometry.Canonical.ZornMatrix.ext
    · simp; ring
    · simp; ring
    · funext i; fin_cases i <;> simp <;> ring
    · funext i; fin_cases i <;> simp <;> ring

theorem hadamardSwapLinearEquiv_mem_aut :
    hadamardSwapLinearEquiv ∈ realZornCompositionAut := by
  intro X Y
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [hadamardSwapLinearEquiv, zMul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
    ring
  · simp [hadamardSwapLinearEquiv, zMul, InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
    ring
  · funext i
    fin_cases i <;>
      simp [hadamardSwapLinearEquiv, zMul, InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross] <;>
      ring
  · funext i
    fin_cases i <;>
      simp [hadamardSwapLinearEquiv, zMul, InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross] <;>
      ring

noncomputable def hadamardSwapAut : realZornCompositionAut :=
  ⟨hadamardSwapLinearEquiv, hadamardSwapLinearEquiv_mem_aut⟩

@[simp] theorem hadamardSwapAut_mul_self : hadamardSwapAut * hadamardSwapAut = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  exact hadamardSwapLinearEquiv.left_inv X

@[simp] theorem hadamardSwapAut_inv : hadamardSwapAut⁻¹ = hadamardSwapAut :=
  inv_eq_iff_mul_eq_one.mpr hadamardSwapAut_mul_self

theorem hadamardSwap_ellChiralPlus :
    (hadamardSwapAut : CanonicalLinearAut) ellChiralPlus = (OP1 : ZornC) := by
  rw [ellChiralPlus,
    InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.scalar_chiralNull_plus_idempotent]
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [hadamardSwapAut, hadamardSwapLinearEquiv, OP1,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit]; norm_num
  · simp [hadamardSwapAut, hadamardSwapLinearEquiv, OP1,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit]
  · funext i; fin_cases i <;>
      simp [hadamardSwapAut, hadamardSwapLinearEquiv, OP1,
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit]
  · funext i; fin_cases i <;>
      simp [hadamardSwapAut, hadamardSwapLinearEquiv, OP1,
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit]

theorem hadamardSwap_ellChiralMinus :
    (hadamardSwapAut : CanonicalLinearAut) ellChiralMinus = (OP2 : ZornC) := by
  rw [ellChiralMinus,
    InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes.scalar_chiralNull_minus_idempotent]
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [hadamardSwapAut, hadamardSwapLinearEquiv, OP2,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit]
  · simp [hadamardSwapAut, hadamardSwapLinearEquiv, OP2,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit]; norm_num
  · funext i; fin_cases i <;>
      simp [hadamardSwapAut, hadamardSwapLinearEquiv, OP2,
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit]
  · funext i; fin_cases i <;>
      simp [hadamardSwapAut, hadamardSwapLinearEquiv, OP2,
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit]

theorem hadamardSwap_OP1 :
    (hadamardSwapAut : CanonicalLinearAut) (OP1 : ZornC) = ellChiralPlus := by
  rw [← hadamardSwap_ellChiralPlus]
  exact hadamardSwapLinearEquiv.left_inv ellChiralPlus

theorem hadamardSwap_OP2 :
    (hadamardSwapAut : CanonicalLinearAut) (OP2 : ZornC) = ellChiralMinus := by
  rw [← hadamardSwap_ellChiralMinus]
  exact hadamardSwapLinearEquiv.left_inv ellChiralMinus

theorem hadamardSwap_lUnit :
    (hadamardSwapAut : CanonicalLinearAut)
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit =
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.kUnit := by
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [hadamardSwapAut, hadamardSwapLinearEquiv,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.kUnit_def]; norm_num
  · simp [hadamardSwapAut, hadamardSwapLinearEquiv,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit,
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.kUnit_def]; norm_num
  · funext i; fin_cases i <;>
      simp [hadamardSwapAut, hadamardSwapLinearEquiv,
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit,
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.kUnit_def]
  · funext i; fin_cases i <;>
      simp [hadamardSwapAut, hadamardSwapLinearEquiv,
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit,
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.kUnit_def]

theorem hadamardSwap_kUnit :
    (hadamardSwapAut : CanonicalLinearAut)
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.kUnit =
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit := by
  rw [← hadamardSwap_lUnit]
  exact hadamardSwapLinearEquiv.left_inv
    InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit

private theorem hadamardSwap_conj_ell_to_peirce (φ : realZornEllStabilizer) :
    hadamardSwapAut * φ.1 * hadamardSwapAut ∈ realZornPeirceStabilizer := by
  have hpair : φ.1 ∈ realZornOrderedChiralPairStabilizer := by
    rw [← realZornEllStabilizer_eq_orderedChiralPairStabilizer]
    exact φ.2
  constructor
  · change (hadamardSwapAut : CanonicalLinearAut)
        ((φ.1 : CanonicalLinearAut)
          ((hadamardSwapAut : CanonicalLinearAut) (OP1 : ZornC))) = OP1
    rw [hadamardSwap_OP1, hpair.1, hadamardSwap_ellChiralPlus]
  · change (hadamardSwapAut : CanonicalLinearAut)
        ((φ.1 : CanonicalLinearAut)
          ((hadamardSwapAut : CanonicalLinearAut) (OP2 : ZornC))) = OP2
    rw [hadamardSwap_OP2, hpair.2, hadamardSwap_ellChiralMinus]

private theorem hadamardSwap_conj_peirce_to_ell (ψ : realZornPeirceStabilizer) :
    hadamardSwapAut * ψ.1 * hadamardSwapAut ∈ realZornEllStabilizer := by
  rw [realZornEllStabilizer_eq_orderedChiralPairStabilizer]
  constructor
  · change (hadamardSwapAut : CanonicalLinearAut)
        ((ψ.1 : CanonicalLinearAut)
          ((hadamardSwapAut : CanonicalLinearAut) ellChiralPlus)) = ellChiralPlus
    rw [hadamardSwap_ellChiralPlus, ψ.2.1, hadamardSwap_OP1]
  · change (hadamardSwapAut : CanonicalLinearAut)
        ((ψ.1 : CanonicalLinearAut)
          ((hadamardSwapAut : CanonicalLinearAut) ellChiralMinus)) = ellChiralMinus
    rw [hadamardSwap_ellChiralMinus, ψ.2.2, hadamardSwap_OP2]

/-- Conjugation by the split-octonion involution `hadamardSwapAut` identifies the
global `ℓ`-stabilizer subgroup with the global Peirce idempotent stabilizer. -/
noncomputable def realZornEllStabilizerMulEquivPeirceStabilizer :
    realZornEllStabilizer ≃* realZornPeirceStabilizer where
  toFun φ := ⟨hadamardSwapAut * φ.1 * hadamardSwapAut, hadamardSwap_conj_ell_to_peirce φ⟩
  invFun ψ := ⟨hadamardSwapAut * ψ.1 * hadamardSwapAut, hadamardSwap_conj_peirce_to_ell ψ⟩
  left_inv φ := by
    apply Subtype.ext
    change hadamardSwapAut * (hadamardSwapAut * φ.1 * hadamardSwapAut) * hadamardSwapAut = φ.1
    calc
      hadamardSwapAut * (hadamardSwapAut * φ.1 * hadamardSwapAut) * hadamardSwapAut
          = (hadamardSwapAut * hadamardSwapAut) * φ.1 * (hadamardSwapAut * hadamardSwapAut) := by
            simp only [mul_assoc]
      _ = φ.1 := by simp [hadamardSwapAut_mul_self]
  right_inv ψ := by
    apply Subtype.ext
    change hadamardSwapAut * (hadamardSwapAut * ψ.1 * hadamardSwapAut) * hadamardSwapAut = ψ.1
    calc
      hadamardSwapAut * (hadamardSwapAut * ψ.1 * hadamardSwapAut) * hadamardSwapAut
          = (hadamardSwapAut * hadamardSwapAut) * ψ.1 * (hadamardSwapAut * hadamardSwapAut) := by
            simp only [mul_assoc]
      _ = ψ.1 := by simp [hadamardSwapAut_mul_self]
  map_mul' φ₁ φ₂ := by
    apply Subtype.ext
    change hadamardSwapAut * (φ₁.1 * φ₂.1) * hadamardSwapAut =
      (hadamardSwapAut * φ₁.1 * hadamardSwapAut) * (hadamardSwapAut * φ₂.1 * hadamardSwapAut)
    calc
      hadamardSwapAut * (φ₁.1 * φ₂.1) * hadamardSwapAut
          = hadamardSwapAut * φ₁.1 * 1 * φ₂.1 * hadamardSwapAut := by
            simp only [mul_one, mul_assoc]
      _ = hadamardSwapAut * φ₁.1 * (hadamardSwapAut * hadamardSwapAut) *
            φ₂.1 * hadamardSwapAut := by
          rw [hadamardSwapAut_mul_self]
      _ = (hadamardSwapAut * φ₁.1 * hadamardSwapAut) *
            (hadamardSwapAut * φ₂.1 * hadamardSwapAut) := by
          simp only [mul_assoc]

/-- **`R2-Gap3` Closure**: Global Lie-group classification of the stabilizer of `ℓ`
inside `realZornCompositionAut` as `SL₃(ℝ)`. -/
noncomputable def realZornEllStabilizerMulEquivSL3 :
    realZornEllStabilizer ≃* SL3Group :=
  realZornEllStabilizerMulEquivPeirceStabilizer.trans realZornPeirceStabilizerMulEquivSL3

theorem realZornEllStabilizer_global_rank_and_sl3_action (φ : realZornEllStabilizer) :
    ∃ g : SL3Group, realZornEllStabilizerMulEquivSL3 φ = g :=
  ⟨realZornEllStabilizerMulEquivSL3 φ, rfl⟩

end InfoGeometry.Lie.SplitOctonionGlobalEllStabilizerSL3
