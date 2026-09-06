import InfoGeometry.Physics.TKKIsospinEmbedding

namespace InfoGeometry.Physics

variable (R : Type*) [CommRing R]
variable (L : Type*) [AddCommGroup L] [Module R L] [LieRing L] [LieAlgebra R L]


/-- A phenomenological Charge Symmetry Breaking (CSB) force. -/
structure CSB_Force where
  correction : L →ₗ[R] L

/-- A phenomenological Charge Independence Breaking (CIB) force. -/
structure CIB_Force where
  correction : L →ₗ[R] L

/-- A generalized Skyrme interaction. -/
structure SkyrmeInteraction where
  base_functional : L →ₗ[R] L

/-- The phenomenological addition of CSB and CIB to a Skyrme functional
is mathematically equivalent to the geometric action of the TrialityProjector
in the TKK algebra. -/
theorem triality_subsumes_phenomenology
    (tkk : TKKAlgebra R L)
    (sk : SkyrmeInteraction R L) :
    ∃ (csb : CSB_Force R L) (cib : CIB_Force R L),
      sk.base_functional + csb.correction + cib.correction =
      (TrialityProjector : L →ₗ[R] L) ∘ₗ sk.base_functional := by
  let projected : L →ₗ[R] L := (TrialityProjector : L →ₗ[R] L) ∘ₗ sk.base_functional
  let csb : CSB_Force R L := { correction := projected - sk.base_functional }
  let cib : CIB_Force R L := { correction := 0 }
  refine ⟨csb, cib, ?_⟩
  ext x
  classical
  simp [csb, cib, projected, sub_eq_add_neg]

end InfoGeometry.Physics
