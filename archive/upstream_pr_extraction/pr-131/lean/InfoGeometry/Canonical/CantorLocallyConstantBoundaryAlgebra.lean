import InfoGeometry.Canonical.CantorCylinderFunctionStages

/-!
# Locally constant boundary functions

This owner bundles the finite cylinder lifts already constructed by
`CantorCylinderFunctionStages`.  The algebra is the unital subalgebra generated
by all finite-stage lifts.  We deliberately do not identify this adjoin with
the raw existential union without first constructing a common-stage theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorLocallyConstantBoundaryAlgebra

open InfoGeometry.Canonical.CantorCylinderFunctionStages
open InfoGeometry.Canonical.CantorCliffordFunctionModel

def IsLocallyConstantBoundaryFunction
    (f : (InfoGeometry.Canonical.CantorCliffordFunctionModel.ContinuousBoundaryFunction ℝ)) : Prop :=
  ∃ (n : ℕ) (g : CylinderFunction n), liftCylinder g = f

@[simp] theorem isLocallyConstantBoundaryFunction_liftCylinder
    {n : ℕ} (g : CylinderFunction n) :
    IsLocallyConstantBoundaryFunction (liftCylinder g) := by
  exact ⟨n, g, rfl⟩

theorem isLocallyConstantBoundaryFunction_zero :
    IsLocallyConstantBoundaryFunction (0 : (InfoGeometry.Canonical.CantorCliffordFunctionModel.ContinuousBoundaryFunction ℝ)) := by
  refine ⟨0, 0, ?_⟩
  simpa using (map_zero (liftCylinderAlgHom 0))

theorem isLocallyConstantBoundaryFunction_one :
    IsLocallyConstantBoundaryFunction (1 : (InfoGeometry.Canonical.CantorCliffordFunctionModel.ContinuousBoundaryFunction ℝ)) := by
  refine ⟨0, 1, ?_⟩
  simpa using (map_one (liftCylinderAlgHom 0))

theorem isLocallyConstantBoundaryFunction_algebraMap (r : ℝ) :
    IsLocallyConstantBoundaryFunction (algebraMap ℝ (InfoGeometry.Canonical.CantorCliffordFunctionModel.ContinuousBoundaryFunction ℝ) r) := by
  refine ⟨0, algebraMap ℝ (CylinderFunction 0) r, ?_⟩
  exact (liftCylinderAlgHom 0).commutes r

theorem isLocallyConstantBoundaryFunction_neg
    {f : (InfoGeometry.Canonical.CantorCliffordFunctionModel.ContinuousBoundaryFunction ℝ)}
    (hf : IsLocallyConstantBoundaryFunction f) :
    IsLocallyConstantBoundaryFunction (-f) := by
  rcases hf with ⟨n, f, rfl⟩
  refine ⟨n, -f, ?_⟩
  simpa using (map_neg (liftCylinderAlgHom n) f)

theorem isLocallyConstantBoundaryFunction_smul
    (r : ℝ)
    {f : (InfoGeometry.Canonical.CantorCliffordFunctionModel.ContinuousBoundaryFunction ℝ)}
    (hf : IsLocallyConstantBoundaryFunction f) :
    IsLocallyConstantBoundaryFunction (r • f) := by
  rcases hf with ⟨n, f, rfl⟩
  refine ⟨n, r • f, ?_⟩
  change (liftCylinderAlgHom n) (r • f) = r • (liftCylinderAlgHom n) f
  exact (liftCylinderAlgHom n).toLinearMap.map_smul r f

noncomputable def locallyConstantBoundaryAlgebra :
    Subalgebra ℝ (InfoGeometry.Canonical.CantorCliffordFunctionModel.ContinuousBoundaryFunction ℝ) :=
  Algebra.adjoin ℝ
    (Set.range fun p : Σ n : ℕ, CylinderFunction n => liftCylinder p.2)

theorem liftCylinder_mem_locallyConstantBoundaryAlgebra
    {n : ℕ} (g : CylinderFunction n) :
    liftCylinder g ∈ locallyConstantBoundaryAlgebra := by
  exact Algebra.subset_adjoin ⟨⟨n, g⟩, rfl⟩

theorem liftCylinderAlgHom_mem_locallyConstantBoundaryAlgebra
    (n : ℕ) (g : CylinderFunction n) :
    liftCylinderAlgHom n g ∈ locallyConstantBoundaryAlgebra := by
  simpa using liftCylinder_mem_locallyConstantBoundaryAlgebra g

theorem isLocallyConstantBoundaryFunction_liftCylinder_add
    {n : ℕ} (f g : CylinderFunction n) :
    IsLocallyConstantBoundaryFunction
      (liftCylinder f + liftCylinder g) := by
  refine ⟨n, f + g, ?_⟩
  simpa using (map_add (liftCylinderAlgHom n) f g)

theorem isLocallyConstantBoundaryFunction_liftCylinder_mul
    {n : ℕ} (f g : CylinderFunction n) :
    IsLocallyConstantBoundaryFunction
      (liftCylinder f * liftCylinder g) := by
  refine ⟨n, f * g, ?_⟩
  simpa using (map_mul (liftCylinderAlgHom n) f g)

theorem isLocallyConstantBoundaryFunction_add
    {f g : (InfoGeometry.Canonical.CantorCliffordFunctionModel.ContinuousBoundaryFunction ℝ)}
    (hf : IsLocallyConstantBoundaryFunction f)
    (hg : IsLocallyConstantBoundaryFunction g) :
    IsLocallyConstantBoundaryFunction (f + g) := by
  rcases hf with ⟨n, f, rfl⟩
  rcases hg with ⟨m, g, rfl⟩
  let k := max n m
  refine ⟨k, cylinderStageEmbedOfLe (Nat.le_max_left n m) f +
        cylinderStageEmbedOfLe (Nat.le_max_right n m) g, ?_⟩
  calc
    liftCylinder ((cylinderStageEmbedOfLe (Nat.le_max_left n m) f) +
        cylinderStageEmbedOfLe (Nat.le_max_right n m) g)
        = liftCylinder (cylinderStageEmbedOfLe (Nat.le_max_left n m) f) +
      liftCylinder (cylinderStageEmbedOfLe (Nat.le_max_right n m) g) := by
      have h := (map_add (liftCylinderAlgHom k)
          (cylinderStageEmbedOfLe (Nat.le_max_left n m) f)
          (cylinderStageEmbedOfLe (Nat.le_max_right n m) g))
      exact h
    _ = liftCylinder f + liftCylinder g := by
          simp [liftCylinder_stageEmbedOfLe]

theorem isLocallyConstantBoundaryFunction_mul
    {f g : (InfoGeometry.Canonical.CantorCliffordFunctionModel.ContinuousBoundaryFunction ℝ)}
    (hf : IsLocallyConstantBoundaryFunction f)
    (hg : IsLocallyConstantBoundaryFunction g) :
    IsLocallyConstantBoundaryFunction (f * g) := by
  rcases hf with ⟨n, f, rfl⟩
  rcases hg with ⟨m, g, rfl⟩
  let k := max n m
  refine ⟨k, cylinderStageEmbedOfLe (Nat.le_max_left n m) f *
        cylinderStageEmbedOfLe (Nat.le_max_right n m) g, ?_⟩
  calc
    liftCylinder ((cylinderStageEmbedOfLe (Nat.le_max_left n m) f) *
        cylinderStageEmbedOfLe (Nat.le_max_right n m) g)
        = liftCylinder (cylinderStageEmbedOfLe (Nat.le_max_left n m) f) *
          liftCylinder (cylinderStageEmbedOfLe (Nat.le_max_right n m) g) := by
          have h := (map_mul (liftCylinderAlgHom k)
              (cylinderStageEmbedOfLe (Nat.le_max_left n m) f)
              (cylinderStageEmbedOfLe (Nat.le_max_right n m) g))
          exact h
    _ = liftCylinder f * liftCylinder g := by
      simp [liftCylinder_stageEmbedOfLe]

theorem isLocallyConstantBoundaryFunction_sub
    {f g : (InfoGeometry.Canonical.CantorCliffordFunctionModel.ContinuousBoundaryFunction ℝ)}
    (hf : IsLocallyConstantBoundaryFunction f)
    (hg : IsLocallyConstantBoundaryFunction g) :
    IsLocallyConstantBoundaryFunction (f - g) := by
  simpa [sub_eq_add_neg] using
    isLocallyConstantBoundaryFunction_add hf
      (isLocallyConstantBoundaryFunction_neg hg)

theorem mem_locallyConstantBoundaryAlgebra_iff
    {f : (InfoGeometry.Canonical.CantorCliffordFunctionModel.ContinuousBoundaryFunction ℝ)} :
    f ∈ locallyConstantBoundaryAlgebra ↔
      IsLocallyConstantBoundaryFunction f := by
  constructor
  · intro hf
    refine Algebra.adjoin_induction
      (p := fun x _ => IsLocallyConstantBoundaryFunction x) ?_ ?_ ?_ ?_ hf
    · intro x hx
      rcases hx with ⟨⟨n, g⟩, rfl⟩
      exact isLocallyConstantBoundaryFunction_liftCylinder g
    · intro r
      exact isLocallyConstantBoundaryFunction_algebraMap r
    · intro x y hx hy h₁ h₂
      exact isLocallyConstantBoundaryFunction_add h₁ h₂
    · intro x y hx hy h₁ h₂
      exact isLocallyConstantBoundaryFunction_mul h₁ h₂
  · intro hf
    rcases hf with ⟨n, g, rfl⟩
    exact liftCylinder_mem_locallyConstantBoundaryAlgebra g

theorem isLocallyConstantBoundaryFunction_boundaryMirrorPullback
    {f : (InfoGeometry.Canonical.CantorCliffordFunctionModel.ContinuousBoundaryFunction ℝ)}
    (hf : IsLocallyConstantBoundaryFunction f) :
    IsLocallyConstantBoundaryFunction (boundaryMirrorPullback f) := by
  rcases hf with ⟨n, g, rfl⟩
  exact ⟨n, mirrorCylinderFunction g, boundaryMirrorPullback_liftCylinder g⟩

theorem boundaryMirrorPullback_mem_locallyConstantBoundaryAlgebra
    {f : (InfoGeometry.Canonical.CantorCliffordFunctionModel.ContinuousBoundaryFunction ℝ)}
    (hf : f ∈ locallyConstantBoundaryAlgebra) :
    boundaryMirrorPullback f ∈ locallyConstantBoundaryAlgebra := by
  rw [mem_locallyConstantBoundaryAlgebra_iff] at hf ⊢
  exact isLocallyConstantBoundaryFunction_boundaryMirrorPullback hf

end InfoGeometry.Canonical.CantorLocallyConstantBoundaryAlgebra
