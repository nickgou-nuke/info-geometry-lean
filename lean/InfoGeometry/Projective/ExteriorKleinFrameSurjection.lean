import InfoGeometry.Projective.ExteriorKleinProjective
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Nondegenerate exterior frames cover the projective Klein locus

The affine exterior owner proves that a bivector in `⋀² ℝ⁴` is Klein-null
exactly when it is a simple wedge.  This file performs the next concrete
projective step: nonzero two-vector wedges map onto the projective Klein
locus.

This is the framed Plücker cover before quotienting frames by change of basis.
It is not yet an equivalence with Mathlib's `Module.Grassmannian`, and makes no
positive-Grassmannian or amplituhedron claim.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Projective.ExteriorKleinFrameSurjection

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorKleinProjective
open InfoGeometry.Projective.ExteriorPowerPluckerBridge

/-- An ordered pair in `ℝ⁴` whose exterior product is nonzero.  This is the
native framed carrier needed before quotienting by change of frame. -/
abbrev NondegenerateExteriorFrame :=
  {uv : Fin 2 → Vec4 // exteriorPower.ιMulti ℝ 2 uv ≠ 0}

/-- The projective Plücker ray of a nondegenerate ordered frame, regarded as a
point of the projective Klein locus. -/
def frameToKleinLocus (uv : NondegenerateExteriorFrame) : KleinLocus :=
  ⟨Projectivization.mk ℝ (exteriorPower.ιMulti ℝ 2 uv.1) uv.2,
    (isKlein_mk_iff _ uv.2).2
      (exteriorKleinForm_ιMulti (uv.1 0) (uv.1 1))⟩

@[simp] theorem frameToKleinLocus_val
    (uv : NondegenerateExteriorFrame) :
    (frameToKleinLocus uv).1 =
      Projectivization.mk ℝ (exteriorPower.ιMulti ℝ 2 uv.1) uv.2 :=
  rfl

/-- Every projective Klein-null exterior ray has a nondegenerate ordered-frame
representative.  This is the concrete surjective Plücker map prior to the
`GL₂`/Grassmannian quotient. -/
theorem frameToKleinLocus_surjective :
    Function.Surjective frameToKleinLocus := by
  rintro ⟨p, hp⟩
  revert hp
  refine Projectivization.ind (p := p) ?_
  intro X hX hp
  have hK : exteriorKleinForm X = 0 :=
    (isKlein_mk_iff X hX).1 hp
  obtain ⟨u, v, huv⟩ :=
    (exteriorKleinForm_eq_zero_iff_decomposable X).1 hK
  subst X
  refine ⟨⟨![u, v], hX⟩, ?_⟩
  apply Subtype.ext
  rfl

end InfoGeometry.Projective.ExteriorKleinFrameSurjection
