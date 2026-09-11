import InfoGeometry.Canonical.GradedRationalCohomologyShadow
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

variable {V W : ℕ → Type*}
  [∀ p, AddCommGroup (V p)]
  [∀ p, Module ℚ (V p)]
  [∀ p, AddCommGroup (W p)]
  [∀ p, Module ℚ (W p)]

/-- A degree-preserving linear map commuting with two graded differentials. -/
structure GradedRationalChainMap
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W) where
  map : ∀ p, V p →ₗ[ℚ] W p
  commutes : ∀ p (x : V p),
    map (p + 1) (D.d p x) = E.d p (map p x)

def gradedChainMapId
    (D : GradedRationalDifferential V) :
    GradedRationalChainMap D D where
  map := fun _ => LinearMap.id
  commutes := by simp

def gradedChainMapComp
    {U : ℕ → Type*}
    [∀ p, AddCommGroup (U p)]
    [∀ p, Module ℚ (U p)]
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {F : GradedRationalDifferential U}
    (f : GradedRationalChainMap D E)
    (g : GradedRationalChainMap E F) :
    GradedRationalChainMap D F where
  map := fun p => (g.map p).comp (f.map p)
  commutes := by
    intro p x
    rw [LinearMap.comp_apply, f.commutes, g.commutes, LinearMap.comp_apply]

theorem chainMap_preserves_cycles
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (F : GradedRationalChainMap D E)
    (p : ℕ) {x : V p}
    (hx : x ∈ gradedCycleSubmodule D p) :
    F.map p x ∈ gradedCycleSubmodule E p := by
  change E.d p (F.map p x) = 0
  rw [← F.commutes p x]
  simpa using congrArg (F.map (p + 1)) hx

theorem chainMap_preserves_boundaries
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (F : GradedRationalChainMap D E)
    (p : ℕ) {x : V (p + 1)}
    (hx : x ∈ gradedBoundarySubmodule D p) :
    F.map (p + 1) x ∈ gradedBoundarySubmodule E p := by
  rcases hx with ⟨y, rfl⟩
  refine ⟨F.map p y, ?_⟩
  exact (F.commutes p y).symm

theorem chainMap_preserves_boundary_cycles
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (F : GradedRationalChainMap D E)
    (p : ℕ) {x : V (p + 1)}
    (hx : x ∈ gradedBoundarySubmodule D p) :
    F.map (p + 1) x ∈ gradedCycleSubmodule E (p + 1) :=
  gradedBoundary_is_cycle E p (chainMap_preserves_boundaries D E F p hx)

def chainMapOnCycles
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (F : GradedRationalChainMap D E)
    (p : ℕ) :
    gradedCycleSubmodule D p →ₗ[ℚ] gradedCycleSubmodule E p :=
  { toFun := fun x =>
      ⟨F.map p x.1, chainMap_preserves_cycles D E F p x.2⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      simp
    map_smul' := by
      intro a x
      apply Subtype.ext
      simp }

def chainMapOnBoundaries
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (F : GradedRationalChainMap D E)
    (p : ℕ) :
    gradedBoundarySubmodule D p →ₗ[ℚ] gradedBoundarySubmodule E p :=
  { toFun := fun x =>
      ⟨F.map (p + 1) x.1, chainMap_preserves_boundaries D E F p x.2⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      simp
    map_smul' := by
      intro a x
      apply Subtype.ext
      simp }

theorem chainMap_maps_boundaryInCycles
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (F : GradedRationalChainMap D E)
    (p : ℕ) :
    gradedBoundaryInCycles D p ≤
      Submodule.comap (chainMapOnCycles D E F (p + 1))
        (gradedBoundaryInCycles E p) := by
  intro x hx
  change F.map (p + 1) (x : V (p + 1)) ∈
    gradedBoundarySubmodule E p
  change (x : V (p + 1)) ∈ gradedBoundarySubmodule D p at hx
  rcases hx with ⟨y, hy⟩
  refine ⟨F.map p y, ?_⟩
  have h := F.commutes p y
  simpa [hy] using h.symm

def chainMapOnCohomology
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (F : GradedRationalChainMap D E)
    (p : ℕ) :
    gradedCohomologyShadow D p →ₗ[ℚ] gradedCohomologyShadow E p :=
  by
    simpa [gradedCohomologyShadow] using
      (Submodule.mapQ (gradedBoundaryInCycles D p)
        (gradedBoundaryInCycles E p)
        (chainMapOnCycles D E F (p + 1))
        (chainMap_maps_boundaryInCycles D E F p) :
        (gradedCycleSubmodule D (p + 1) ⧸ gradedBoundaryInCycles D p) →ₗ[ℚ]
          (gradedCycleSubmodule E (p + 1) ⧸ gradedBoundaryInCycles E p))

@[simp]
theorem chainMapOnCohomology_mk
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (F : GradedRationalChainMap D E)
    (p : ℕ) (x : gradedCycleSubmodule D (p + 1)) :
    chainMapOnCohomology D E F p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (chainMapOnCycles D E F (p + 1) x) := by
  change
    (Submodule.mapQ
      (gradedBoundaryInCycles D p)
      (gradedBoundaryInCycles E p)
      (chainMapOnCycles D E F (p + 1))
      (chainMap_maps_boundaryInCycles D E F p))
      (Submodule.Quotient.mk x) =
    Submodule.Quotient.mk (chainMapOnCycles D E F (p + 1) x)
  exact Submodule.mapQ_apply _ _ _ _

@[simp]
theorem chainMapOnCohomology_id
    (D : GradedRationalDifferential V)
    (p : ℕ) :
    chainMapOnCohomology D D (gradedChainMapId D) p = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (gradedBoundaryInCycles D p).mkQ_surjective q
  rfl

theorem chainMapOnCohomology_comp
    {U : ℕ → Type*}
    [∀ p, AddCommGroup (U p)]
    [∀ p, Module ℚ (U p)]
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {F : GradedRationalDifferential U}
    (f : GradedRationalChainMap D E)
    (g : GradedRationalChainMap E F)
    (p : ℕ) :
    chainMapOnCohomology D F (gradedChainMapComp f g) p =
      (chainMapOnCohomology E F g p).comp
        (chainMapOnCohomology D E f p) := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (gradedBoundaryInCycles D p).mkQ_surjective q
  rfl

theorem chainMapOnCycles_coe
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (F : GradedRationalChainMap D E)
    (p : ℕ) (x : gradedCycleSubmodule D p) :
    (chainMapOnCycles D E F p x : W p) = F.map p x :=
  rfl

theorem chainMapOnBoundaries_coe
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (F : GradedRationalChainMap D E)
    (p : ℕ) (x : gradedBoundarySubmodule D p) :
    (chainMapOnBoundaries D E F p x : W (p + 1)) = F.map (p + 1) x :=
  rfl

theorem chainMapOnCycles_id
    (D : GradedRationalDifferential V)
    (p : ℕ) :
    chainMapOnCycles D D (gradedChainMapId D) p = LinearMap.id := by
  ext x
  rfl

theorem chainMapOnCycles_comp
    {U : ℕ → Type*}
    [∀ p, AddCommGroup (U p)]
    [∀ p, Module ℚ (U p)]
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {F : GradedRationalDifferential U}
    (f : GradedRationalChainMap D E)
    (g : GradedRationalChainMap E F)
    (p : ℕ) :
    chainMapOnCycles D F (gradedChainMapComp f g) p =
      (chainMapOnCycles E F g p).comp (chainMapOnCycles D E f p) := by
  ext x
  rfl

theorem gradedChainMapComp_preserves_cycles
    {U : ℕ → Type*}
    [∀ p, AddCommGroup (U p)]
    [∀ p, Module ℚ (U p)]
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {F : GradedRationalDifferential U}
    (f : GradedRationalChainMap D E)
    (g : GradedRationalChainMap E F)
    (p : ℕ) {x : V p}
    (hx : x ∈ gradedCycleSubmodule D p) :
    (gradedChainMapComp f g).map p x ∈ gradedCycleSubmodule F p := by
  exact chainMap_preserves_cycles E F g p
    (chainMap_preserves_cycles D E f p hx)

theorem gradedChainMapComp_preserves_boundaries
    {U : ℕ → Type*}
    [∀ p, AddCommGroup (U p)]
    [∀ p, Module ℚ (U p)]
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {F : GradedRationalDifferential U}
    (f : GradedRationalChainMap D E)
    (g : GradedRationalChainMap E F)
    (p : ℕ) {x : V (p + 1)}
    (hx : x ∈ gradedBoundarySubmodule D p) :
    (gradedChainMapComp f g).map (p + 1) x ∈
      gradedBoundarySubmodule F p := by
  exact chainMap_preserves_boundaries E F g p
    (chainMap_preserves_boundaries D E f p hx)

end InfoGeometry.Canonical
