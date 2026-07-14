import Mathlib
import InfoGeometry.Projective.ArnoldRelations

namespace BCFWShift

open InfoGeometry.Projective.Amplituhedron

variable (R : Type*) [CommRing R]
variable (ι : Type*)
variable (f : ι → ι)

/-- A BCFW shift on the edges induced by an index shift. -/
noncomputable def bcfwLinearShift : EdgeModule R ι →ₗ[R] EdgeModule R ι :=
  Finsupp.lmapDomain R R (Prod.map f f)

/-- The induced algebra map on the exterior algebra of edges. -/
noncomputable def bcfwExteriorShift : ExteriorAlgebra R (EdgeModule R ι) →ₐ[R] ExteriorAlgebra R (EdgeModule R ι) :=
  ExteriorAlgebra.map (bcfwLinearShift R ι f)

/-- The exterior shift commutes with the edge generator `w`. -/
theorem bcfwExteriorShift_w (i j : ι) :
    bcfwExteriorShift R ι f (w R ι i j) = w R ι (f i) (f j) := by
  dsimp [bcfwExteriorShift, w, bcfwLinearShift]
  rw [ExteriorAlgebra.map_apply_ι]
  congr 1
  simp [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The BCFW shift preserves the Arnold relations on the exterior algebra. -/
theorem bcfwShift_preserves_ArnoldRel (x y : ExteriorAlgebra R (EdgeModule R ι))
    (h : ArnoldRel R ι x y) :
    ArnoldRel R ι (bcfwExteriorShift R ι f x) (bcfwExteriorShift R ι f y) := by
  induction h
  case symm i j =>
    simp only [bcfwExteriorShift_w]
    exact ArnoldRel.symm (f i) (f j)
  case mixed i j k =>
    simp only [map_add, map_mul, map_zero, bcfwExteriorShift_w]
    exact ArnoldRel.mixed (f i) (f j) (f k)

/-- The BCFW shift lifted to the Arnold-Cohen quotient algebra. -/
noncomputable def bcfwAlgebraShift : RingQuot (ArnoldRel R ι) →+* RingQuot (ArnoldRel R ι) :=
  RingQuot.lift ⟨
    (RingQuot.mkRingHom (ArnoldRel R ι)).comp (bcfwExteriorShift R ι f).toRingHom,
    by
      intro x y h
      dsimp
      apply RingQuot.mkRingHom_rel
      exact bcfwShift_preserves_ArnoldRel R ι f x y h
  ⟩

/-- Evaluating the lifted shift on a quotient image simplifies to the exterior shift. -/
theorem bcfwAlgebraShift_mkRingHom (x : ExteriorAlgebra R (EdgeModule R ι)) :
    bcfwAlgebraShift R ι f ((RingQuot.mkRingHom (ArnoldRel R ι)) x) =
    (RingQuot.mkRingHom (ArnoldRel R ι)) (bcfwExteriorShift R ι f x) := by
  dsimp [bcfwAlgebraShift]
  rw [RingQuot.lift_mkRingHom_apply]
  rfl

/-- The lifted shift maps the mixed relation expression to the shifted mixed relation expression. -/
theorem bcfwShift_eval_mixed (i j k : ι) :
    bcfwAlgebraShift R ι f (
      (RingQuot.mkRingHom (ArnoldRel R ι))
        (w R ι i j * w R ι j k +
         w R ι j k * w R ι k i +
         w R ι k i * w R ι i j)
    ) = 
      (RingQuot.mkRingHom (ArnoldRel R ι))
        (w R ι (f i) (f j) * w R ι (f j) (f k) +
         w R ι (f j) (f k) * w R ι (f k) (f i) +
         w R ι (f k) (f i) * w R ι (f i) (f j)) := by
  rw [bcfwAlgebraShift_mkRingHom]
  simp only [map_add, map_mul, bcfwExteriorShift_w]

/-- The BCFW shift preserves the property that the mixed relation vanishes in the quotient. -/
theorem bcfwShift_preserves_mixed_zero (i j k : ι) :
    bcfwAlgebraShift R ι f (
      (RingQuot.mkRingHom (ArnoldRel R ι))
        (w R ι i j * w R ι j k +
         w R ι j k * w R ι k i +
         w R ι k i * w R ι i j)
    ) = (RingQuot.mkRingHom (ArnoldRel R ι)) 0 := by
  rw [InfoGeometry.Projective.Amplituhedron.arnold_mixed_relation_quotient_zero R ι i j k]
  simp

end BCFWShift
