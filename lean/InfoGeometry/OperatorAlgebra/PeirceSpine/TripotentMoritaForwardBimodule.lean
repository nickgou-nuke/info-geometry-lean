/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentMoritaTensorComparison
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
The forward Morita functor is tensoring with the right `End(V)`-module `V*`.
Since `End(V)` is generally noncommutative, its balanced tensor is represented
as a quotient of a real tensor product by the explicit balancing relations.
The quotient identifies with the rank-one corner selected by a basis vector.
-/

noncomputable section
open TensorProduct
namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {V : Type} [AddCommGroup V] [Module ℝ V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance : AddCommGroup (Module.Dual ℝ V) := inferInstance

section Forward
variable [Module.Finite ℝ V]
variable (b : Module.Basis ι ℝ V) (i : ι)
variable (M : Type) [AddCommGroup M] [Module (Module.End ℝ V) M]
  [Module ℝ M] [IsScalarTower ℝ (Module.End ℝ V) M]
  [SMulCommClass ℝ (Module.End ℝ V) M]

local instance : AddCommGroup (Module.Dual ℝ V ⊗[ℝ] M) := inferInstance

/-- Rank-one operator with image along the selected basis vector. -/
def basisRankOne (φ : Module.Dual ℝ V) : Module.End ℝ V :=
  φ.smulRight (b i)

/-- The idempotent rank-one projection associated to a basis vector. -/
def basisCornerIdem : Module.End ℝ V :=
  (b.coord i).smulRight (b i)

theorem basisCornerIdem_apply (v : V) :
    basisCornerIdem b i v = (b.repr v i) • b i := by
  simp [basisCornerIdem, LinearMap.smulRight_apply]

theorem basisCornerIdem_idem : basisCornerIdem b i * basisCornerIdem b i =
    basisCornerIdem b i := by
  ext v
  simp [basisCornerIdem_apply]

/-- The selected simple corner of an `End(V)`-module. -/
def basisCorner : Submodule ℝ M where
  carrier := {m | basisCornerIdem b i • m = m}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change basisCornerIdem b i • (x + y) = x + y
    rw [smul_add, hx, hy]
  smul_mem' := by
    intro r x hx
    change basisCornerIdem b i • (r • x) = r • x
    calc
      basisCornerIdem b i • (r • x) = r • (basisCornerIdem b i • x) :=
        (smul_comm r (basisCornerIdem b i) x).symm
      _ = r • x := congrArg (fun z => r • z) hx

/-- Balancing relations for the right `End(V)`-action on `V*` and left action
on `M`. -/
def forwardMoritaRelations : Submodule ℝ (Module.Dual ℝ V ⊗[ℝ] M) :=
  Submodule.span ℝ (Set.range (fun t : Module.Dual ℝ V × Module.End ℝ V × M =>
    (t.1.comp t.2.1) ⊗ₜ[ℝ] t.2.2 - t.1 ⊗ₜ[ℝ] (t.2.1 • t.2.2)))

/-- The algebraic balanced tensor `V* ⊗_{End(V)} M`. -/
abbrev forwardMoritaTensor (M : Type) [AddCommGroup M]
    [Module (Module.End ℝ V) M] [Module ℝ M]
    [IsScalarTower ℝ (Module.End ℝ V) M]
    [SMulCommClass ℝ (Module.End ℝ V) M] : Type _ :=
  (Module.Dual ℝ V ⊗[ℝ] M) ⧸ forwardMoritaRelations M

private def forwardBilinear : Module.Dual ℝ V →ₗ[ℝ] M →ₗ[ℝ] M :=
  LinearMap.mk₂ ℝ (fun φ m => basisRankOne b i φ • m)
    (by
      intro φ ψ m
      have h : basisRankOne b i (φ + ψ) = basisRankOne b i φ + basisRankOne b i ψ := by
        ext v
        change (φ v + ψ v) • b i = φ v • b i + ψ v • b i
        exact add_smul _ _ _
      rw [h, add_smul])
    (by
      intro r φ m
      have h : basisRankOne b i (r • φ) = r • basisRankOne b i φ := by
        ext v
        change (r * φ v) • b i = r • (φ v • b i)
        simpa only [smul_eq_mul] using (smul_assoc r (φ v) (b i))
      rw [h, smul_assoc])
    (by intro φ m n; exact smul_add _ _ _)
    (by
      intro r φ m
      exact (smul_comm r (basisRankOne b i φ) m).symm)

private def forwardRawMap : Module.Dual ℝ V ⊗[ℝ] M →ₗ[ℝ] M :=
  TensorProduct.lift (forwardBilinear (M := M) (b := b) (i := i))

private theorem forwardMoritaRelations_le_ker :
    forwardMoritaRelations M ≤
      LinearMap.ker (forwardRawMap (M := M) (b := b) (i := i)) := by
  change Submodule.span ℝ (Set.range (fun t : Module.Dual ℝ V × Module.End ℝ V × M =>
    (t.1.comp t.2.1) ⊗ₜ[ℝ] t.2.2 - t.1 ⊗ₜ[ℝ] (t.2.1 • t.2.2))) ≤ _
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨φ, a, m⟩, rfl⟩
  change forwardRawMap (M := M) (b := b) (i := i)
      ((φ.comp a) ⊗ₜ[ℝ] m - φ ⊗ₜ[ℝ] (a • m)) = 0
  rw [map_sub, forwardRawMap, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
  change basisRankOne b i (φ.comp a) • m -
    basisRankOne b i φ • (a • m) = 0
  have hcomp : basisRankOne b i (φ.comp a) = basisRankOne b i φ * a := by
    ext v
    rfl
  rw [hcomp, mul_smul, sub_self]

private def forwardRawMapToCorner : Module.Dual ℝ V ⊗[ℝ] M →ₗ[ℝ] basisCorner b i M where
  toFun x := ⟨forwardRawMap (M := M) (b := b) (i := i) x, by
    change basisCornerIdem b i • forwardRawMap (M := M) (b := b) (i := i) x = _
    induction x using TensorProduct.induction_on with
    | zero => simp [forwardRawMap]
    | add x y hx hy =>
      rw [map_add, smul_add, hx, hy]
    | tmul φ m =>
      change basisCornerIdem b i • (basisRankOne b i φ • m) = _
      rw [← mul_smul]
      have hcomp : basisCornerIdem b i * basisRankOne b i φ = basisRankOne b i φ := by
        ext v
        simp [basisCornerIdem, basisRankOne, LinearMap.smulRight_apply,
          LinearMap.comp_apply, Module.Dual.eval_apply]
      rw [hcomp]
      rfl⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' r x := Subtype.ext (map_smul _ _ _)

/-- The induced map from the balanced tensor to the chosen corner. -/
def forwardMoritaMap : forwardMoritaTensor (V := V) M →ₗ[ℝ] basisCorner b i M :=
  (forwardMoritaRelations M).liftQ
    (forwardRawMapToCorner (M := M) (b := b) (i := i)) (by
    change Submodule.span ℝ (Set.range (fun t : Module.Dual ℝ V × Module.End ℝ V × M =>
      (t.1.comp t.2.1) ⊗ₜ[ℝ] t.2.2 - t.1 ⊗ₜ[ℝ] (t.2.1 • t.2.2))) ≤ _
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨φ, a, m⟩, rfl⟩
    change forwardRawMapToCorner (M := M) (b := b) (i := i)
      ((φ.comp a) ⊗ₜ[ℝ] m - φ ⊗ₜ[ℝ] (a • m)) = 0
    apply Subtype.ext
    change forwardRawMap (M := M) (b := b) (i := i)
      ((φ.comp a) ⊗ₜ[ℝ] m - φ ⊗ₜ[ℝ] (a • m)) = 0
    exact forwardMoritaRelations_le_ker (b := b) (i := i) (M := M)
      (Submodule.subset_span ⟨(φ, a, m), rfl⟩))

private def cornerToForwardTensor : basisCorner b i M →ₗ[ℝ] forwardMoritaTensor (V := V) M where
  toFun y := (forwardMoritaRelations M).mkQ
    ((b.coord i) ⊗ₜ[ℝ] (y : M))
  map_add' x y := by
    change (forwardMoritaRelations M).mkQ
      ((b.coord i) ⊗ₜ[ℝ] ((x : M) + (y : M))) = _
    rw [TensorProduct.tmul_add, map_add]
  map_smul' r x := by
    change (forwardMoritaRelations M).mkQ
      ((b.coord i) ⊗ₜ[ℝ] (r • (x : M))) = _
    rw [TensorProduct.tmul_smul, map_smul]
    rfl

private theorem basisDual_comp_rankOne (φ : Module.Dual ℝ V) :
    (b.coord i).comp (basisRankOne b i φ) = φ := by
  ext v
  simp [basisRankOne, LinearMap.smulRight_apply]

private theorem rankOne_map_corner (φ : Module.Dual ℝ V) (m : M) :
    forwardMoritaMap b i M
      ((forwardMoritaRelations M).mkQ
        (φ ⊗ₜ[ℝ] m)) =
    ⟨basisRankOne b i φ • m, by
      change basisCornerIdem b i • (basisRankOne b i φ • m) = _
      rw [← mul_smul]
      have hcomp : basisCornerIdem b i * basisRankOne b i φ = basisRankOne b i φ := by
        ext v
        simp [basisCornerIdem, basisRankOne, LinearMap.smulRight_apply,
          LinearMap.comp_apply]
      rw [hcomp]⟩ := by
  apply Subtype.ext
  rfl

/-- The forward tensor functor is the selected operator corner, with inverse
given by the dual basis vector. -/
def forwardMoritaTensorEquiv : forwardMoritaTensor (V := V) M ≃ₗ[ℝ] basisCorner b i M where
  toFun := forwardMoritaMap b i M
  invFun := cornerToForwardTensor b i M
  left_inv := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      induction x using TensorProduct.induction_on with
      | zero =>
        change cornerToForwardTensor b i M
          (forwardMoritaMap (V := V) b i M ((forwardMoritaRelations M).mkQ 0)) = _
        rw [map_zero]
        simp only [cornerToForwardTensor, LinearMap.zero_apply, map_zero,
          Submodule.Quotient.mk_zero]
      | add x y hx hy =>
        change cornerToForwardTensor b i M
          (forwardMoritaMap (V := V) b i M
            ((forwardMoritaRelations M).mkQ x + (forwardMoritaRelations M).mkQ y)) = _
        rw [map_add (forwardMoritaMap (V := V) b i M)]
        rw [map_add (cornerToForwardTensor b i M)]
        have hx' : cornerToForwardTensor b i M
            (forwardMoritaMap (V := V) b i M ((forwardMoritaRelations M).mkQ x)) =
            (forwardMoritaRelations M).mkQ x := by simpa using hx
        have hy' : cornerToForwardTensor b i M
            (forwardMoritaMap (V := V) b i M ((forwardMoritaRelations M).mkQ y)) =
            (forwardMoritaRelations M).mkQ y := by simpa using hy
        rw [hx', hy']
        exact (map_add (forwardMoritaRelations M).mkQ x y).symm
      | tmul φ m =>
        change cornerToForwardTensor b i M
          (forwardMoritaMap (V := V) b i M
            ((forwardMoritaRelations M).mkQ (φ ⊗ₜ[ℝ] m))) = _
        rw [rankOne_map_corner]
        change (forwardMoritaRelations M).mkQ
          ((b.coord i) ⊗ₜ[ℝ] (basisRankOne b i φ • m)) = _
        change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
        apply (Submodule.Quotient.eq (forwardMoritaRelations M)).mpr
        have hgen : φ ⊗ₜ[ℝ] m -
            (b.coord i) ⊗ₜ[ℝ] (basisRankOne b i φ • m) ∈
              forwardMoritaRelations M := by
          change φ ⊗ₜ[ℝ] m -
              (b.coord i) ⊗ₜ[ℝ] (basisRankOne b i φ • m) ∈
            Submodule.span ℝ (Set.range (fun t :
              Module.Dual ℝ V × Module.End ℝ V × M =>
                (t.1.comp t.2.1) ⊗ₜ[ℝ] t.2.2 -
                  t.1 ⊗ₜ[ℝ] (t.2.1 • t.2.2)))
          exact Submodule.subset_span ⟨(b.coord i, basisRankOne b i φ, m), by
            change ((b.coord i).comp (basisRankOne b i φ)) ⊗ₜ[ℝ] m -
              (b.coord i) ⊗ₜ[ℝ] (basisRankOne b i φ • m) = _
            rw [basisDual_comp_rankOne b i φ]⟩
        have hneg : -(φ ⊗ₜ[ℝ] m -
            (b.coord i) ⊗ₜ[ℝ] (basisRankOne b i φ • m)) =
              (b.coord i) ⊗ₜ[ℝ] (basisRankOne b i φ • m) - φ ⊗ₜ[ℝ] m := by
          abel
        rw [← hneg]
        exact (forwardMoritaRelations M).neg_mem hgen
  right_inv := by
    intro y
    apply Subtype.ext
    change basisRankOne b i (b.coord i) • (y : M) = y
    change basisCornerIdem b i • (y : M) = y
    exact y.property
  map_add' x y := by
    change forwardMoritaMap b i M (x + y) = _
    exact map_add (forwardMoritaMap b i M) x y
  map_smul' r x := by
    change forwardMoritaMap b i M (r • x) = _
    exact map_smul (forwardMoritaMap b i M) r x

section Natural
variable {N : Type} [AddCommGroup N] [Module (Module.End ℝ V) N]
  [Module ℝ N] [IsScalarTower ℝ (Module.End ℝ V) N]
  [SMulCommClass ℝ (Module.End ℝ V) N]

local instance : AddCommGroup (Module.Dual ℝ V ⊗[ℝ] N) := inferInstance

/-- The map induced on balanced tensors by an equivariant map of modules. -/
def forwardMoritaTensorMap (f : M →ₗ[ℝ] N)
    (hf : ∀ (a : Module.End ℝ V) (m : M), f (a • m) = a • f m) :
    forwardMoritaTensor (V := V) M →ₗ[ℝ] forwardMoritaTensor (V := V) N :=
  (forwardMoritaRelations M).liftQ
    ((forwardMoritaRelations N).mkQ.comp (TensorProduct.map LinearMap.id f)) (by
      change forwardMoritaRelations M ≤
        LinearMap.ker ((forwardMoritaRelations N).mkQ.comp
          (TensorProduct.map LinearMap.id f))
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨φ, a, m⟩, rfl⟩
      change (forwardMoritaRelations N).mkQ
        ((φ.comp a) ⊗ₜ[ℝ] f m - φ ⊗ₜ[ℝ] f (a • m)) = 0
      apply (Submodule.Quotient.mk_eq_zero (forwardMoritaRelations N)).mpr
      rw [hf a m]
      exact Submodule.subset_span ⟨(φ, a, f m), rfl⟩)

/-- An equivariant linear map restricts to the selected rank-one corners. -/
def basisCornerMap (f : M →ₗ[ℝ] N)
    (hf : ∀ (a : Module.End ℝ V) (m : M), f (a • m) = a • f m) :
    basisCorner b i M →ₗ[ℝ] basisCorner b i N where
  toFun y := ⟨f y, by
    change basisCornerIdem b i • f y = f y
    rw [← hf (basisCornerIdem b i) y, y.property]⟩
  map_add' x y := Subtype.ext (f.map_add x y)
  map_smul' r x := Subtype.ext (f.map_smul r x)

/-- The forward tensor-to-corner identification commutes with every map of
`End(V)`-modules on pure tensors. -/
theorem forwardMoritaMap_natural_tmul (f : M →ₗ[ℝ] N)
    (hf : ∀ (a : Module.End ℝ V) (m : M), f (a • m) = a • f m)
    (φ : Module.Dual ℝ V) (m : M) :
    basisCornerMap (V := V) (ι := ι) (b := b) (i := i)
      (M := M) (N := N) (f := f) (hf := hf)
      (forwardMoritaMap b i M ((forwardMoritaRelations M).mkQ
        (φ ⊗ₜ[ℝ] m))) =
    forwardMoritaMap b i N
      ((forwardMoritaRelations N).mkQ (φ ⊗ₜ[ℝ] f m)) := by
  apply Subtype.ext
  change f (basisRankOne b i φ • m) = basisRankOne b i φ • f m
  exact hf (basisRankOne b i φ) m

/-- Naturality of the balanced tensor-to-corner map, on the full quotient. -/
theorem forwardMoritaMap_natural (f : M →ₗ[ℝ] N)
    (hf : ∀ (a : Module.End ℝ V) (m : M), f (a • m) = a • f m)
    (q : forwardMoritaTensor (V := V) M) :
    basisCornerMap (V := V) (ι := ι) (b := b) (i := i)
      (M := M) (N := N) (f := f) (hf := hf)
        (forwardMoritaMap b i M q) =
      forwardMoritaMap b i N
        (forwardMoritaTensorMap (V := V) (M := M) (N := N)
          (f := f) (hf := hf) q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
    induction x using TensorProduct.induction_on with
    | zero => simp [forwardMoritaTensorMap]
    | add x y hx hy =>
      change basisCornerMap (V := V) (ι := ι) (b := b) (i := i)
          (M := M) (N := N) (f := f) (hf := hf)
          (forwardMoritaMap b i M
            ((forwardMoritaRelations M).mkQ x + (forwardMoritaRelations M).mkQ y)) =
        forwardMoritaMap b i N
          (forwardMoritaTensorMap (V := V) (M := M) (N := N)
            (f := f) (hf := hf)
            ((forwardMoritaRelations M).mkQ x + (forwardMoritaRelations M).mkQ y))
      rw [map_add (forwardMoritaMap b i M),
        map_add (forwardMoritaTensorMap (V := V) (M := M) (N := N)
          (f := f) (hf := hf)), map_add,
        map_add (forwardMoritaMap b i N)]
      exact congrArg₂ (· + ·) hx hy
    | tmul φ m =>
      simpa [forwardMoritaTensorMap] using
        forwardMoritaMap_natural_tmul (V := V) (ι := ι) (b := b) (i := i)
          (M := M) (N := N) (f := f) (hf := hf) φ m

end Natural

end Forward
end InfoGeometry.OperatorAlgebra.PeirceSpine
