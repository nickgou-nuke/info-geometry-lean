/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KleinianWittBornNullIncidence
import InfoGeometry.Canonical.ZornCl44Triality

/-!
# Canonical Isomorphism Between Split-Octonion Left Multiplication and Zorn's `Cl(4,4)` Triality Carrier

Constructs the explicit `ℝ`-linear and algebra isomorphism `octSToZorn : OctS ≃ₐ/≃ₗ ZornMatrix ℝ`
identifying:
1. Cayley–Dickson split-octonion multiplication `octMul` on `Fin 8 → ℝ` with Zorn vector-matrix
   multiplication on `ZornMatrix ℝ` (`octSToZorn_mul`, `octSToZorn_one`, `octSToZorn_conj`),
2. The `(4, 4)` split norm and bilinear pairing (`zornNormFun_octSToZorn`, `zornBilin_octSToZorn`),
3. The `16 × 16` block `Cl(4,4)` generators `gammaMat` and chiral volume `volumeCl44` with
   `ZornCl44Triality.diracGamma` and `-ZornCl44Triality.chiralGrading` via the explicit intertwiner
   `spinor16Equiv : (Fin 8 ⊕ Fin 8 → ℝ) ≃ₗ[ℝ] DiracSpinor16 (R := ℝ)`,
4. Universal Kleinian null-plane incidence (`range (leftMulLinear (zornConj z)) = ker (leftMulLinear z)`
   with `finrank (ker (leftMulLinear z)) = 4`) transported directly onto `ZornMatrix ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open InfoGeometry.Canonical.KleinianWittBornNullIncidence
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornCl44Triality
open InfoGeometry.Canonical.ZornClifford

namespace InfoGeometry.Canonical.KleinianZornCl44Bridge

/-- Basis-aligned algebra isomorphism `OctS → ZornMatrix ℝ` sending
`u ↦ ((u₀ + u₄, u₀ - u₄), (u₁ - u₅, u₃ - u₇, u₂ - u₆), -(u₁ + u₅, u₃ + u₇, u₂ + u₆))`. -/
def octSToZorn (u : OctS) : ZornMatrix ℝ where
  a := u 0 + u 4
  b := u 0 - u 4
  x := ![u 1 - u 5, u 3 - u 7, u 2 - u 6]
  y := ![-(u 1 + u 5), -(u 3 + u 7), -(u 2 + u 6)]

/-- Inverse linear isomorphism `ZornMatrix ℝ → OctS`. -/
def zornToOctS (z : ZornMatrix ℝ) : OctS :=
  ![ (z.a + z.b) / 2,
     (z.x 0 - z.y 0) / 2,
     (z.x 2 - z.y 2) / 2,
     (z.x 1 - z.y 1) / 2,
     (z.a - z.b) / 2,
     -(z.x 0 + z.y 0) / 2,
     -(z.x 2 + z.y 2) / 2,
     -(z.x 1 + z.y 1) / 2 ]

lemma zornToOctS_octSToZorn (u : OctS) : zornToOctS (octSToZorn u) = u := by
  ext i
  fin_cases i <;> simp [zornToOctS, octSToZorn] <;> ring

lemma octSToZorn_zornToOctS (z : ZornMatrix ℝ) : octSToZorn (zornToOctS z) = z := by
  apply ZornMatrix.ext
  · simp [octSToZorn, zornToOctS]; ring
  · simp [octSToZorn, zornToOctS]; ring
  · funext i; fin_cases i <;> simp [octSToZorn, zornToOctS] <;> ring
  · funext i; fin_cases i <;> simp [octSToZorn, zornToOctS] <;> ring

/-- Canonical `ℝ`-linear equivalence between `OctS = Fin 8 → ℝ` and `ZornMatrix ℝ`. -/
def octSToZornLinearEquiv : OctS ≃ₗ[ℝ] ZornMatrix ℝ where
  toFun := octSToZorn
  invFun := zornToOctS
  left_inv := zornToOctS_octSToZorn
  right_inv := octSToZorn_zornToOctS
  map_add' u v := by
    apply ZornMatrix.ext
    · simp [octSToZorn]; ring
    · simp [octSToZorn]; ring
    · funext i; fin_cases i <;> simp [octSToZorn] <;> ring
    · funext i; fin_cases i <;> simp [octSToZorn] <;> ring
  map_smul' c u := by
    apply ZornMatrix.ext
    · simp [octSToZorn]; ring
    · simp [octSToZorn]; ring
    · funext i; fin_cases i <;> simp [octSToZorn] <;> ring
    · funext i; fin_cases i <;> simp [octSToZorn] <;> ring

private lemma octSToZorn_zero : octSToZorn 0 = 0 :=
  octSToZornLinearEquiv.map_zero

/-- `octSToZorn` is a multiplicative split-octonion algebra isomorphism onto `ZornMatrix ℝ`. -/
theorem octSToZorn_mul (u v : OctS) :
    octSToZorn (octMul u v) = octSToZorn u * octSToZorn v := by
  apply ZornMatrix.ext
  · simp [octSToZorn, octMul, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot]; ring
  · simp [octSToZorn, octMul, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.dot]; ring
  · funext i
    fin_cases i <;>
      simp [octSToZorn, octMul, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.cross] <;> ring
  · funext i
    fin_cases i <;>
      simp [octSToZorn, octMul, ZornMatrix.mul_def, ZornMatrix.mul, ZornMatrix.cross] <;> ring

/-- `octSToZorn` preserves the multiplicative identity `e₀ ↦ 1`. -/
theorem octSToZorn_one : octSToZorn (Pi.single 0 1) = (1 : ZornMatrix ℝ) := by
  apply ZornMatrix.ext
  · simp [octSToZorn]
  · simp [octSToZorn]
  · funext i; fin_cases i <;> simp [octSToZorn]
  · funext i; fin_cases i <;> simp [octSToZorn]

/-- `octSToZorn` intertwines `octConj` with `zornConj`. -/
theorem octSToZorn_conj (u : OctS) :
    octSToZorn (octConj u) = zornConj (octSToZorn u) := by
  apply ZornMatrix.ext
  · simp [octSToZorn, octConj, zornConj]; ring
  · simp [octSToZorn, octConj, zornConj]
  · funext i; fin_cases i <;> simp [octSToZorn, octConj, zornConj] <;> ring
  · funext i; fin_cases i <;> simp [octSToZorn, octConj, zornConj] <;> ring

/-- `octSToZorn` is an isometry for the split `(4, 4)` quadratic norms `octNorm` and `zornNormFun`. -/
theorem zornNormFun_octSToZorn (u : OctS) :
    zornNormFun (octSToZorn u) = octNorm u := by
  simp [zornNormFun, octSToZorn, octNorm, ZornMatrix.dot]
  ring

/-- `octSToZorn` intertwines the polarized bilinear forms `octPolar` and `zornBilin`. -/
theorem zornBilin_octSToZorn (u v : OctS) :
    zornBilin (octSToZorn u) (octSToZorn v) = octPolar u v := by
  simp [zornBilin_apply, octSToZorn, octPolar, ZornMatrix.dot]
  ring

/-- Left multiplication by `x` in `M₈(ℝ)` intertwines with `ZornMatrix.leftMulLinear (octSToZorn x)`. -/
theorem leftMulLinear_intertwine (u v : OctS) :
    octSToZorn ((leftMulMat u).mulVec v) = leftMulLinear (octSToZorn u) (octSToZorn v) := by
  rw [leftMulMat_mulVec, octSToZorn_mul]
  rfl

/-- Canonical `ℝ`-linear equivalence between the `16`-dimensional `Fin 8 ⊕ Fin 8 → ℝ` spinor carrier
of `KleinianWittBornNullIncidence` and `ZornClifford.DiracSpinor16 (R := ℝ)`. -/
def spinor16Equiv : (Fin 8 ⊕ Fin 8 → ℝ) ≃ₗ[ℝ] DiracSpinor16 (R := ℝ) where
  toFun w := (octSToZorn (w ∘ Sum.inl), octSToZorn (w ∘ Sum.inr))
  invFun s := Sum.elim (zornToOctS s.1) (zornToOctS s.2)
  left_inv w := by
    ext (i | i) <;> simp [zornToOctS_octSToZorn]
  right_inv s := by
    rcases s with ⟨s₁, s₂⟩
    ext <;> simp [octSToZorn_zornToOctS]
  map_add' w₁ w₂ := by
    apply Prod.ext
    · change octSToZorn (w₁ ∘ Sum.inl + w₂ ∘ Sum.inl) =
        octSToZorn (w₁ ∘ Sum.inl) + octSToZorn (w₂ ∘ Sum.inl)
      exact octSToZornLinearEquiv.map_add (w₁ ∘ Sum.inl) (w₂ ∘ Sum.inl)
    · change octSToZorn (w₁ ∘ Sum.inr + w₂ ∘ Sum.inr) =
        octSToZorn (w₁ ∘ Sum.inr) + octSToZorn (w₂ ∘ Sum.inr)
      exact octSToZornLinearEquiv.map_add (w₁ ∘ Sum.inr) (w₂ ∘ Sum.inr)
  map_smul' c w := by
    apply Prod.ext
    · change octSToZorn (c • (w ∘ Sum.inl)) = c • octSToZorn (w ∘ Sum.inl)
      exact octSToZornLinearEquiv.map_smul c (w ∘ Sum.inl)
    · change octSToZorn (c • (w ∘ Sum.inr)) = c • octSToZorn (w ∘ Sum.inr)
      exact octSToZornLinearEquiv.map_smul c (w ∘ Sum.inr)

private lemma fromBlocks_antidiag_mulVec (M₁ M₂ : Matrix (Fin 8) (Fin 8) ℝ)
    (w : Fin 8 ⊕ Fin 8 → ℝ) :
    ((Matrix.fromBlocks 0 M₁ M₂ 0).mulVec w ∘ Sum.inl) = M₁.mulVec (w ∘ Sum.inr) ∧
    ((Matrix.fromBlocks 0 M₁ M₂ 0).mulVec w ∘ Sum.inr) = M₂.mulVec (w ∘ Sum.inl) := by
  constructor <;> ext i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

private lemma fromBlocks_diag_neg_one_mulVec (w : Fin 8 ⊕ Fin 8 → ℝ) :
    ((Matrix.fromBlocks (-1 : Matrix (Fin 8) (Fin 8) ℝ) 0 0 (1 : Matrix (Fin 8) (Fin 8) ℝ)).mulVec w
        ∘ Sum.inl) = -(w ∘ Sum.inl) ∧
    ((Matrix.fromBlocks (-1 : Matrix (Fin 8) (Fin 8) ℝ) 0 0 (1 : Matrix (Fin 8) (Fin 8) ℝ)).mulVec w
        ∘ Sum.inr) = (w ∘ Sum.inr) := by
  constructor <;> ext i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

private lemma spinor16Equiv_apply (w : Fin 8 ⊕ Fin 8 → ℝ) :
    spinor16Equiv w = (octSToZorn (w ∘ Sum.inl), octSToZorn (w ∘ Sum.inr)) := rfl

/-- `spinor16Equiv` intertwines every `16 × 16` Clifford generator `gammaMat A` with
`ZornCl44Triality.diracGamma` evaluated at the corresponding basis Zorn matrix. -/
theorem spinor16Equiv_gammaMat_intertwine (A : Fin 8) (w : Fin 8 ⊕ Fin 8 → ℝ) :
    spinor16Equiv ((gammaMat A).mulVec w) =
      diracGamma (octSToZorn (Pi.single A 1)) (spinor16Equiv w) := by
  have hblk := fromBlocks_antidiag_mulVec
    (leftMulMat (Pi.single A 1)) (leftMulMat (octConj (Pi.single A 1))) w
  simp only [spinor16Equiv_apply, diracGamma_apply]
  unfold gammaMat
  rw [hblk.1, hblk.2, leftMulLinear_intertwine, leftMulLinear_intertwine, octSToZorn_conj]
  rfl

/-- `spinor16Equiv` intertwines the chiral volume element `volumeCl44` with `-chiralGrading`
on `DiracSpinor16`. -/
theorem spinor16Equiv_volumeCl44_intertwine (w : Fin 8 ⊕ Fin 8 → ℝ) :
    spinor16Equiv (volumeCl44.mulVec w) = -(chiralGrading (spinor16Equiv w)) := by
  rw [volumeCl44_eq_chiral_diag]
  have hblk := fromBlocks_diag_neg_one_mulVec w
  simp only [spinor16Equiv_apply, chiralGrading_apply]
  rw [hblk.1, hblk.2]
  have hneg : octSToZorn (-(w ∘ Sum.inl)) = -octSToZorn (w ∘ Sum.inl) :=
    octSToZornLinearEquiv.map_neg (w ∘ Sum.inl)
  rw [hneg]
  apply Prod.ext <;> simp

private lemma mem_range_leftMulLinear_iff (z v : ZornMatrix ℝ) :
    v ∈ LinearMap.range (leftMulLinear z) ↔
      zornToOctS v ∈ LinearMap.range (Matrix.toLin' (leftMulMat (zornToOctS z))) := by
  simp only [LinearMap.mem_range, Matrix.toLin'_apply]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨zornToOctS w, ?_⟩
    apply octSToZornLinearEquiv.injective
    change octSToZorn ((leftMulMat (zornToOctS z)).mulVec (zornToOctS w)) =
      octSToZorn (zornToOctS (leftMulLinear z w))
    rw [octSToZorn_zornToOctS, leftMulLinear_intertwine, octSToZorn_zornToOctS,
      octSToZorn_zornToOctS]
  · rintro ⟨x, hx⟩
    refine ⟨octSToZorn x, ?_⟩
    have hzx : octSToZorn ((leftMulMat (zornToOctS z)).mulVec x) = octSToZorn (zornToOctS v) :=
      congrArg octSToZorn hx
    rw [leftMulLinear_intertwine, octSToZorn_zornToOctS, octSToZorn_zornToOctS] at hzx
    exact hzx

private lemma mem_ker_leftMulLinear_iff (z v : ZornMatrix ℝ) :
    v ∈ LinearMap.ker (leftMulLinear z) ↔
      zornToOctS v ∈ LinearMap.ker (Matrix.toLin' (leftMulMat (zornToOctS z))) := by
  simp only [LinearMap.mem_ker, Matrix.toLin'_apply]
  constructor
  · intro hv
    apply octSToZornLinearEquiv.injective
    change octSToZorn ((leftMulMat (zornToOctS z)).mulVec (zornToOctS v)) = octSToZorn 0
    rw [octSToZorn_zero, leftMulLinear_intertwine, octSToZorn_zornToOctS, octSToZorn_zornToOctS]
    exact hv
  · intro hx
    have hzx : octSToZorn ((leftMulMat (zornToOctS z)).mulVec (zornToOctS v)) = 0 := by
      rw [hx, octSToZorn_zero]
    rw [leftMulLinear_intertwine, octSToZorn_zornToOctS, octSToZorn_zornToOctS] at hzx
    exact hzx

private lemma zornConj_zornToOctS (z : ZornMatrix ℝ) :
    zornToOctS (zornConj z) = octConj (zornToOctS z) := by
  apply octSToZornLinearEquiv.injective
  change octSToZorn (zornToOctS (zornConj z)) = octSToZorn (octConj (zornToOctS z))
  rw [octSToZorn_conj, octSToZorn_zornToOctS, octSToZorn_zornToOctS]

/-- **Universal Kleinian Null-Plane Incidence on `ZornMatrix ℝ`**:
for every nonzero null Zorn split octonion `z ≠ 0` (`zornNormFun z = 0`),
`range (leftMulLinear (zornConj z)) = ker (leftMulLinear z)`. -/
theorem zorn_null_range_eq_ker (z : ZornMatrix ℝ) (hz : z ≠ 0) (hnull : zornNormFun z = 0) :
    LinearMap.range (leftMulLinear (zornConj z)) = LinearMap.ker (leftMulLinear z) := by
  have hu_ne : zornToOctS z ≠ 0 := fun h0 => by
    apply hz
    have h := congrArg octSToZorn h0
    rwa [octSToZorn_zornToOctS, octSToZorn_zero] at h
  have hu_null : octNorm (zornToOctS z) = 0 := by
    rw [← zornNormFun_octSToZorn, octSToZorn_zornToOctS]
    exact hnull
  have hOct := null_octonion_range_eq_ker (zornToOctS z) hu_ne hu_null
  ext v
  rw [mem_range_leftMulLinear_iff, mem_ker_leftMulLinear_iff, zornConj_zornToOctS, hOct]

/-- **Universal Kleinian Null-Plane Dimension 4 on `ZornMatrix ℝ`**:
for every nonzero null Zorn split octonion `z ≠ 0` (`zornNormFun z = 0`),
`finrank (ker (leftMulLinear z)) = 4`. -/
theorem zorn_null_ker_finrank_four (z : ZornMatrix ℝ) (hz : z ≠ 0) (hnull : zornNormFun z = 0) :
    Module.finrank ℝ (LinearMap.ker (leftMulLinear z)) = 4 := by
  have hu_ne : zornToOctS z ≠ 0 := fun h0 => by
    apply hz
    have h := congrArg octSToZorn h0
    rwa [octSToZorn_zornToOctS, octSToZorn_zero] at h
  have hu_null : octNorm (zornToOctS z) = 0 := by
    rw [← zornNormFun_octSToZorn, octSToZorn_zornToOctS]
    exact hnull
  let e : LinearMap.ker (Matrix.toLin' (leftMulMat (zornToOctS z))) ≃ₗ[ℝ]
      LinearMap.ker (leftMulLinear z) :=
    { toFun := fun x => ⟨octSToZorn x.1, by
        rw [mem_ker_leftMulLinear_iff, zornToOctS_octSToZorn]
        exact x.2⟩
      invFun := fun y => ⟨zornToOctS y.1, (mem_ker_leftMulLinear_iff z y.1).mp y.2⟩
      left_inv := fun x => Subtype.ext (zornToOctS_octSToZorn x.1)
      right_inv := fun y => Subtype.ext (octSToZorn_zornToOctS y.1)
      map_add' := fun x₁ x₂ => Subtype.ext (octSToZornLinearEquiv.map_add x₁.1 x₂.1)
      map_smul' := fun c x => Subtype.ext (octSToZornLinearEquiv.map_smul c x.1) }
  rw [← e.finrank_eq]
  exact null_octonion_ker_finrank_four (zornToOctS z) hu_ne hu_null

end InfoGeometry.Canonical.KleinianZornCl44Bridge
