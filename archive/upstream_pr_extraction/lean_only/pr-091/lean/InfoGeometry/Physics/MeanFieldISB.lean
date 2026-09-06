import InfoGeometry.Physics.TKKIsospinEmbedding

namespace InfoGeometry.Physics

variable (R : Type*) [CommRing R]
variable (L : Type*) [AddCommGroup L] [Module R L] [LieRing L] [LieAlgebra R L]


/-- A phenomenological Charge Symmetry Breaking (CSB) force. -/
abbrev CSB_Force := L →ₗ[R] L

namespace CSB_Force

abbrev correction (f : CSB_Force R L) : L →ₗ[R] L := f

end CSB_Force

/-- A phenomenological Charge Independence Breaking (CIB) force. -/
abbrev CIB_Force := L →ₗ[R] L

namespace CIB_Force

abbrev correction (f : CIB_Force R L) : L →ₗ[R] L := f

end CIB_Force

/-- A generalized Skyrme interaction. -/
abbrev SkyrmeInteraction := L →ₗ[R] L

namespace SkyrmeInteraction

abbrev base_functional (f : SkyrmeInteraction R L) : L →ₗ[R] L := f

end SkyrmeInteraction

/-- Decompose a Skyrme functional into a projected part plus a residual. -/
theorem triality_projector_decomposition
    (tkk : TKKAlgebra R L)
    (sk : SkyrmeInteraction R L) :
    ∃ (csb : CSB_Force R L) (cib : CIB_Force R L),
      sk.base_functional + csb.correction + cib.correction =
      (TrialityProjector : L →ₗ[R] L) ∘ₗ sk.base_functional := by
  let projected : L →ₗ[R] L := (TrialityProjector : L →ₗ[R] L) ∘ₗ sk.base_functional
  let csb : CSB_Force R L := projected - sk.base_functional
  let cib : CIB_Force R L := 0
  refine ⟨csb, cib, ?_⟩
  ext x
  classical
  simp [csb, cib, projected, sub_eq_add_neg]

end InfoGeometry.Physics
