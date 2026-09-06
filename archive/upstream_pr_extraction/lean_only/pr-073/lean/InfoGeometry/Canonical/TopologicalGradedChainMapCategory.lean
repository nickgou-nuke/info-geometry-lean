import InfoGeometry.Canonical.TopologicalGradedRationalDifferential

namespace InfoGeometry.Canonical

open CategoryTheory

variable {U V W : ℕ → Type*}
  [∀ p, NormedAddCommGroup (U p)]
  [∀ p, NormedSpace ℚ (U p)]
  [∀ p, FiniteDimensional ℚ (U p)]
  [∀ p, NormedAddCommGroup (V p)]
  [∀ p, NormedSpace ℚ (V p)]
  [∀ p, FiniteDimensional ℚ (V p)]
  [∀ p, NormedAddCommGroup (W p)]
  [∀ p, NormedSpace ℚ (W p)]
  [∀ p, FiniteDimensional ℚ (W p)]

/-!
  Identity and composition laws for the topological readout of graded chain
  maps.  These are pointwise laws; no unproved categorical equivalence is
  introduced.
-/

def topologicalGradedChainMapId
    (D : GradedRationalDifferential V) :
    TopologicalGradedRationalChainMap D D where
  algebraic := gradedChainMapId D

def topologicalGradedChainMapComp
    {D : GradedRationalDifferential U}
    {E : GradedRationalDifferential V}
    {F : GradedRationalDifferential W}
    (f : TopologicalGradedRationalChainMap D E)
    (g : TopologicalGradedRationalChainMap E F) :
    TopologicalGradedRationalChainMap D F where
  algebraic := gradedChainMapComp f.algebraic g.algebraic

@[simp] theorem continuousChainMap_id_apply
    (D : GradedRationalDifferential V)
    (p : ℕ) (x : V p) :
    continuousChainMap (topologicalGradedChainMapId D) p x = x := by
  rfl

@[simp] theorem continuousChainMap_comp_apply
    {D : GradedRationalDifferential U}
    {E : GradedRationalDifferential V}
    {F : GradedRationalDifferential W}
    (f : TopologicalGradedRationalChainMap D E)
    (g : TopologicalGradedRationalChainMap E F)
    (p : ℕ) (x : U p) :
    continuousChainMap (topologicalGradedChainMapComp f g) p x =
      continuousChainMap g p (continuousChainMap f p x) := by
  rfl

def topologicalChainMapAt
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    (F : TopologicalGradedRationalChainMap D E) (p : ℕ) :
    V p →ₗ[ℚ] W p :=
  continuousChainMap F p

@[simp] theorem topologicalChainMapAt_apply
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    (F : TopologicalGradedRationalChainMap D E)
    (p : ℕ) (x : V p) :
    topologicalChainMapAt F p x = F.algebraic.map p x := by
  rfl

@[simp] theorem topologicalChainMapAt_id_apply
    (D : GradedRationalDifferential V)
    (p : ℕ) (x : V p) :
    topologicalChainMapAt (topologicalGradedChainMapId D) p x = x := by
  rfl

@[simp] theorem topologicalChainMapAt_comp_apply
    {D : GradedRationalDifferential U}
    {E : GradedRationalDifferential V}
    {F : GradedRationalDifferential W}
    (f : TopologicalGradedRationalChainMap D E)
    (g : TopologicalGradedRationalChainMap E F)
    (p : ℕ) (x : U p) :
    topologicalChainMapAt (topologicalGradedChainMapComp f g) p x =
      topologicalChainMapAt g p (topologicalChainMapAt f p x) := by
  rfl

end InfoGeometry.Canonical
