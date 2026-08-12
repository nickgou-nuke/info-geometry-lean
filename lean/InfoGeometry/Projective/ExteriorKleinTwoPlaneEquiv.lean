import InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient

/-!
# Real two-planes and the projective Klein locus

This owner proves the set-level Plücker correspondence.  A nondegenerate
ordered two-frame determines the same projective exterior ray exactly when it
spans the same real two-plane.  Consequently the existing change-of-frame
quotient, the native carrier of real two-planes in `Vec4`, and the projective
Klein locus are equivalent.

This is a set-level equivalence.  It does not identify `RealTwoPlane` with
Mathlib's scheme-oriented `Module.Grassmannian`.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorKleinProjective
open InfoGeometry.Projective.ExteriorKleinFrameSurjection
open InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient

abbrev ExteriorCube := ⋀[ℝ]^3 Vec4

/-- Left exterior multiplication by a vector, restricted to exterior
two-vectors. -/
noncomputable def leftWedgeExteriorMap (x : Vec4) :
    ExteriorSquare →ₗ[ℝ] ExteriorCube :=
  exteriorPower.alternatingMapLinearEquiv
    ((exteriorPower.ιMulti ℝ 3).curryLeft x)

theorem leftWedgeExteriorMap_ιMulti (x : Vec4) (uv : Fin 2 → Vec4) :
    leftWedgeExteriorMap x (exteriorPower.ιMulti ℝ 2 uv) =
      exteriorPower.ιMulti ℝ 3 (Matrix.vecCons x uv) := by
  rw [leftWedgeExteriorMap,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.curryLeft_apply_apply]

/-- A vector belongs to a nondegenerate frame's plane exactly when its left
wedge with the frame bivector vanishes. -/
theorem mem_frameSpan_iff_leftWedge_eq_zero
    (uv : NondegenerateExteriorFrame) (x : Vec4) :
    x ∈ (frameSpan uv).1 ↔
      leftWedgeExteriorMap x (exteriorPower.ιMulti ℝ 2 uv.1) = 0 := by
  rw [leftWedgeExteriorMap_ιMulti]
  constructor
  · intro hx
    exact (exteriorPower.ιMulti ℝ 3).map_linearDependent _
      (fun hli => ((linearIndependent_fin_cons).1 hli).2 hx)
  · intro hzero
    by_contra hx
    have hli : LinearIndependent ℝ (Matrix.vecCons x uv.1) :=
      (linearIndependent_fin_cons).2
        ⟨nondegenerateExteriorFrame_linearIndependent uv, hx⟩
    exact (exterior_ιMulti_ne_zero_of_linearIndependent _ hli) hzero

/-- Equal projective Plücker rays have the same wedge kernel and therefore
the same underlying two-plane. -/
theorem frameSpan_eq_of_frameToKleinLocus_eq
    (uv₁ uv₂ : NondegenerateExteriorFrame)
    (h : frameToKleinLocus uv₁ = frameToKleinLocus uv₂) :
    frameSpan uv₁ = frameSpan uv₂ := by
  apply Subtype.ext
  apply le_antisymm
  · intro x hx
    have hproj :
        Projectivization.mk ℝ (exteriorPower.ιMulti ℝ 2 uv₁.1) uv₁.2 =
          Projectivization.mk ℝ (exteriorPower.ιMulti ℝ 2 uv₂.1) uv₂.2 :=
      congrArg Subtype.val h
    obtain ⟨c, hc⟩ :=
      (Projectivization.mk_eq_mk_iff ℝ _ _ uv₁.2 uv₂.2).1 hproj
    rw [Units.smul_def] at hc
    have hx0 :
        leftWedgeExteriorMap x (exteriorPower.ιMulti ℝ 2 uv₁.1) = 0 :=
      (mem_frameSpan_iff_leftWedge_eq_zero uv₁ x).1 hx
    have hmap := congrArg (leftWedgeExteriorMap x) hc
    rw [map_smul] at hmap
    change (c : ℝ) •
        leftWedgeExteriorMap x (exteriorPower.ιMulti ℝ 2 uv₂.1) =
          leftWedgeExteriorMap x
            (exteriorPower.ιMulti ℝ 2 uv₁.1) at hmap
    rw [hx0] at hmap
    have : leftWedgeExteriorMap x
        (exteriorPower.ιMulti ℝ 2 uv₂.1) = 0 :=
      (smul_eq_zero.mp hmap).resolve_left c.ne_zero
    exact (mem_frameSpan_iff_leftWedge_eq_zero uv₂ x).2 this
  · intro x hx
    have hproj :
        Projectivization.mk ℝ (exteriorPower.ιMulti ℝ 2 uv₂.1) uv₂.2 =
          Projectivization.mk ℝ (exteriorPower.ιMulti ℝ 2 uv₁.1) uv₁.2 :=
      (congrArg Subtype.val h).symm
    obtain ⟨c, hc⟩ :=
      (Projectivization.mk_eq_mk_iff ℝ _ _ uv₂.2 uv₁.2).1 hproj
    rw [Units.smul_def] at hc
    have hx0 :
        leftWedgeExteriorMap x (exteriorPower.ιMulti ℝ 2 uv₂.1) = 0 :=
      (mem_frameSpan_iff_leftWedge_eq_zero uv₂ x).1 hx
    have hmap := congrArg (leftWedgeExteriorMap x) hc
    rw [map_smul] at hmap
    change (c : ℝ) •
        leftWedgeExteriorMap x (exteriorPower.ιMulti ℝ 2 uv₁.1) =
          leftWedgeExteriorMap x
            (exteriorPower.ιMulti ℝ 2 uv₂.1) at hmap
    rw [hx0] at hmap
    have : leftWedgeExteriorMap x
        (exteriorPower.ιMulti ℝ 2 uv₁.1) = 0 :=
      (smul_eq_zero.mp hmap).resolve_left c.ne_zero
    exact (mem_frameSpan_iff_leftWedge_eq_zero uv₁ x).2 this

/-- The explicit determinant law for changing an ordered two-frame. -/
theorem exterior_ιMulti_fin_two_change (u v : Vec4) (a b c d : ℝ) :
    exteriorPower.ιMulti ℝ 2 ![a • u + b • v, c • u + d • v] =
      (a * d - b * c) • exteriorPower.ιMulti ℝ 2 ![u, v] := by
  simp only [show ![a • u + b • v, c • u + d • v] =
      Matrix.vecCons (a • u + b • v) ![c • u + d • v] from rfl,
    AlternatingMap.map_vecCons_add, AlternatingMap.map_vecCons_smul]
  simp only [show ![u, c • u + d • v] =
      Matrix.vecCons u ![c • u + d • v] from rfl,
    show ![v, c • u + d • v] =
      Matrix.vecCons v ![c • u + d • v] from rfl,
    ← AlternatingMap.curryLeft_apply_apply]
  simp only [map_add, map_smul]
  simp [AlternatingMap.curryLeft_same]
  have hswap := AlternatingMap.map_swap
    (exteriorPower.ιMulti ℝ 2) ![u, v]
      (show (0 : Fin 2) ≠ 1 by decide)
  have hswapVec : (![u, v] ∘ (Equiv.swap (0 : Fin 2) 1)) = ![v, u] := by
    funext i
    fin_cases i <;> rfl
  rw [hswapVec] at hswap
  rw [hswap]
  module

/-- Two frames spanning the same plane differ by an invertible determinant,
so they determine the same projective Plücker ray. -/
theorem frameToKleinLocus_eq_of_frameSpan_eq
    (uv₁ uv₂ : NondegenerateExteriorFrame)
    (h : frameSpan uv₁ = frameSpan uv₂) :
    frameToKleinLocus uv₁ = frameToKleinLocus uv₂ := by
  let b : Module.Basis (Fin 2) ℝ (frameSpan uv₁).1 :=
    Module.Basis.span (nondegenerateExteriorFrame_linearIndependent uv₁)
  let coords : Fin 2 → Fin 2 → ℝ := fun i j =>
    b.coord j ⟨uv₂.1 i, by
      have : uv₂.1 i ∈ (frameSpan uv₂).1 :=
        Submodule.subset_span (Set.mem_range_self i)
      simpa [h] using this⟩
  have hcoords (i : Fin 2) :
      uv₂.1 i = ∑ j, coords i j • uv₁.1 j := by
    have hb := b.sum_repr
      ⟨uv₂.1 i, by
        have : uv₂.1 i ∈ (frameSpan uv₂).1 :=
          Submodule.subset_span (Set.mem_range_self i)
        simpa [h] using this⟩
    change uv₂.1 i = _
    simpa [coords, b, Module.Basis.span_apply] using
      congrArg Subtype.val hb.symm
  have hwedge :
      exteriorPower.ιMulti ℝ 2 uv₂.1 =
        (coords 0 0 * coords 1 1 - coords 0 1 * coords 1 0) •
          exteriorPower.ιMulti ℝ 2 uv₁.1 := by
    have huv₁ : uv₁.1 = ![uv₁.1 0, uv₁.1 1] := by
      funext i
      fin_cases i <;> rfl
    have huv₂ : uv₂.1 =
        ![coords 0 0 • uv₁.1 0 + coords 0 1 • uv₁.1 1,
          coords 1 0 • uv₁.1 0 + coords 1 1 • uv₁.1 1] := by
      funext i
      fin_cases i
      · simpa only [Matrix.cons_val_zero, Fin.sum_univ_two] using hcoords 0
      · simpa only [Matrix.cons_val_one, Matrix.head_cons, Fin.sum_univ_two] using
          hcoords 1
    rw [huv₂, huv₁]
    exact exterior_ιMulti_fin_two_change _ _ _ _ _ _
  let d : ℝ := coords 0 0 * coords 1 1 - coords 0 1 * coords 1 0
  have hd : d ≠ 0 := by
    intro hd0
    have : exteriorPower.ιMulti ℝ 2 uv₂.1 = 0 := by
      rw [hwedge]
      simp [d] at hd0
      simp [hd0]
    exact uv₂.2 this
  apply Subtype.ext
  change Projectivization.mk ℝ _ uv₁.2 =
    Projectivization.mk ℝ _ uv₂.2
  symm
  apply (Projectivization.mk_eq_mk_iff ℝ _ _ uv₂.2 uv₁.2).2
  refine ⟨Units.mk0 d hd, ?_⟩
  rw [Units.smul_def]
  simpa [d] using hwedge.symm

theorem frameToKleinLocus_eq_iff_frameSpan_eq
    (uv₁ uv₂ : NondegenerateExteriorFrame) :
    frameToKleinLocus uv₁ = frameToKleinLocus uv₂ ↔
      frameSpan uv₁ = frameSpan uv₂ :=
  ⟨frameSpan_eq_of_frameToKleinLocus_eq uv₁ uv₂,
    frameToKleinLocus_eq_of_frameSpan_eq uv₁ uv₂⟩

/-- The Plücker map descended through change of ordered frame. -/
def framePlaneQuotientToKleinLocus : FramePlaneQuotient → KleinLocus :=
  Quotient.lift frameToKleinLocus
    (fun _ _ h => frameToKleinLocus_eq_of_frameSpan_eq _ _ h)

@[simp] theorem framePlaneQuotientToKleinLocus_mk
    (uv : NondegenerateExteriorFrame) :
    framePlaneQuotientToKleinLocus (Quotient.mk framePlaneSetoid uv) =
      frameToKleinLocus uv :=
  rfl

theorem framePlaneQuotientToKleinLocus_injective :
    Function.Injective framePlaneQuotientToKleinLocus := by
  intro q₁ q₂ h
  revert h
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro uv₁ uv₂ h
  exact Quotient.sound
    ((frameToKleinLocus_eq_iff_frameSpan_eq uv₁ uv₂).1 h)

theorem framePlaneQuotientToKleinLocus_surjective :
    Function.Surjective framePlaneQuotientToKleinLocus := by
  intro p
  obtain ⟨uv, huv⟩ := frameToKleinLocus_surjective p
  exact ⟨Quotient.mk framePlaneSetoid uv, huv⟩

/-- The change-of-frame quotient is exactly the projective Klein locus. -/
noncomputable def framePlaneQuotientEquivKleinLocus :
    FramePlaneQuotient ≃ KleinLocus :=
  Equiv.ofBijective framePlaneQuotientToKleinLocus
    ⟨framePlaneQuotientToKleinLocus_injective,
      framePlaneQuotientToKleinLocus_surjective⟩

@[simp] theorem framePlaneQuotientEquivKleinLocus_apply_mk
    (uv : NondegenerateExteriorFrame) :
    framePlaneQuotientEquivKleinLocus
        (Quotient.mk framePlaneSetoid uv) = frameToKleinLocus uv :=
  rfl

/-- Set-level real two-planes in `Vec4` are exactly projective decomposable
nonzero exterior two-vectors. -/
noncomputable def realTwoPlaneEquivKleinLocus : RealTwoPlane ≃ KleinLocus :=
  framePlaneQuotientEquivTwoPlane.symm.trans
    framePlaneQuotientEquivKleinLocus

end InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv
