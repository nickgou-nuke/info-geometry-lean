import InfoGeometry.Canonical.RealBoundaryHomologyQuotient
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.RealHomologyCohomologyDictionary

variable {C₁ C₂ : Type*}
variable [AddCommGroup C₁] [Module ℝ C₁]
variable [AddCommGroup C₂] [Module ℝ C₂]

namespace RealBoundaryOperator

variable (B₁ : RealBoundaryOperator C₁)
variable (B₂ : RealBoundaryOperator C₂)

/-! A chain map is a linear map satisfying the native commuting-square law. -/

def IsChainMap (f : C₁ →ₗ[ℝ] C₂) : Prop :=
  f.comp B₁.d = B₂.d.comp f

theorem isChainMap_id : B₁.IsChainMap B₁ (LinearMap.id : C₁ →ₗ[ℝ] C₁) := by
  ext x
  rfl

theorem isChainMap_comp
    {C₃ : Type*} [AddCommGroup C₃] [Module ℝ C₃]
    (B₃ : RealBoundaryOperator C₃)
    (f : C₁ →ₗ[ℝ] C₂) (g : C₂ →ₗ[ℝ] C₃)
    (hf : B₁.IsChainMap B₂ f)
    (hg : B₂.IsChainMap B₃ g) :
    B₁.IsChainMap B₃ (g.comp f) := by
  dsimp [IsChainMap] at hf hg ⊢
  rw [LinearMap.comp_assoc, hf, ← LinearMap.comp_assoc, hg,
    LinearMap.comp_assoc]

theorem maps_cycles
    (f : C₁ →ₗ[ℝ] C₂)
    (hf : B₁.IsChainMap B₂ f)
    (x : B₁.cycles) :
    f x ∈ B₂.cycles := by
  change B₂.d (f x) = 0
  have h := congrArg (fun g : C₁ →ₗ[ℝ] C₂ => g x) hf
  simpa [LinearMap.comp_apply, x.property] using h.symm

def cycleMap
    (f : C₁ →ₗ[ℝ] C₂)
    (hf : B₁.IsChainMap B₂ f) :
    B₁.cycles →ₗ[ℝ] B₂.cycles :=
  { toFun := fun x => ⟨f x, maps_cycles B₁ B₂ f hf x⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      exact f.map_add x y
    map_smul' := by
      intro a x
      apply Subtype.ext
      exact f.map_smul a x }

theorem maps_boundaries
    (f : C₁ →ₗ[ℝ] C₂)
    (hf : B₁.IsChainMap B₂ f)
    {x : C₁}
    (hx : x ∈ B₁.boundaries) :
    f x ∈ B₂.boundaries := by
  change x ∈ LinearMap.range B₁.d at hx
  change f x ∈ LinearMap.range B₂.d
  rcases LinearMap.mem_range.mp hx with ⟨y, hy⟩
  refine LinearMap.mem_range.mpr ⟨f y, ?_⟩
  have h := congrArg (fun g : C₁ →ₗ[ℝ] C₂ => g y) hf
  calc
    B₂.d (f y) = f (B₁.d y) := by simpa [LinearMap.comp_apply] using h.symm
    _ = f x := by rw [hy]

theorem boundariesInCycles_map
    (f : C₁ →ₗ[ℝ] C₂)
    (hf : B₁.IsChainMap B₂ f) :
    B₁.boundariesInCycles ≤
      Submodule.comap (B₁.cycleMap B₂ f hf) B₂.boundariesInCycles := by
  intro x hx
  change (x : C₁) ∈ LinearMap.range B₁.d at hx
  change (B₁.cycleMap B₂ f hf x : C₂) ∈ LinearMap.range B₂.d
  exact maps_boundaries B₁ B₂ f hf hx

def inducedHomologyMap
    (f : C₁ →ₗ[ℝ] C₂)
    (hf : B₁.IsChainMap B₂ f) :
    B₁.Homology →ₗ[ℝ] B₂.Homology :=
  Submodule.mapQ B₁.boundariesInCycles B₂.boundariesInCycles
    (B₁.cycleMap B₂ f hf)
    (B₁.boundariesInCycles_map B₂ f hf)

@[simp] theorem inducedHomologyMap_cycleClass
    (f : C₁ →ₗ[ℝ] C₂)
    (hf : B₁.IsChainMap B₂ f)
    (x : B₁.cycles) :
    B₁.inducedHomologyMap B₂ f hf (B₁.cycleClass x) =
      B₂.cycleClass (B₁.cycleMap B₂ f hf x) := by
  rfl

@[simp] theorem inducedHomologyMap_id :
    B₁.inducedHomologyMap B₁
        (LinearMap.id : C₁ →ₗ[ℝ] C₁)
        B₁.isChainMap_id = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := B₁.boundariesInCycles.mkQ_surjective q
  simp [inducedHomologyMap, cycleMap]

theorem inducedHomologyMap_comp
    {C₃ : Type*} [AddCommGroup C₃] [Module ℝ C₃]
    (B₃ : RealBoundaryOperator C₃)
    (f : C₁ →ₗ[ℝ] C₂) (g : C₂ →ₗ[ℝ] C₃)
    (hf : B₁.IsChainMap B₂ f)
    (hg : B₂.IsChainMap B₃ g) :
    B₁.inducedHomologyMap B₃ (g.comp f)
        (isChainMap_comp (B₁ := B₁) (B₂ := B₂) (B₃ := B₃)
          (f := f) (g := g) hf hg) =
      (B₂.inducedHomologyMap B₃ g hg).comp
        (B₁.inducedHomologyMap B₂ f hf) := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := B₁.boundariesInCycles.mkQ_surjective q
  simp [inducedHomologyMap, Submodule.mapQ_apply]
  have hcycle :
      B₁.cycleMap B₃ (g.comp f)
          (isChainMap_comp (B₁ := B₁) (B₂ := B₂) (B₃ := B₃)
            (f := f) (g := g) hf hg) x =
        (B₂.cycleMap B₃ g hg) (B₁.cycleMap B₂ f hf x) := by
    apply Subtype.ext
    change g (f (x : C₁)) = g (f (x : C₁))
    rfl
  rw [hcycle]

end RealBoundaryOperator

end InfoGeometry.Canonical.RealHomologyCohomologyDictionary
