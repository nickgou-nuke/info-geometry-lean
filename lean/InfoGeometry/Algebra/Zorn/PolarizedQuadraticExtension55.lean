import InfoGeometry.Clifford.PolarizedMinkowski55
import InfoGeometry.Algebra.Zorn.Basic

/-!
# The precise eight-to-ten-dimensional extension is quadratic

The ten-dimensional carrier is linearly equivalent to the existing real Zorn
space plus a hyperbolic plane. The split norm becomes `detZ X - t*s`.
The lower spatial vector must change sign to reconcile the Minkowski and
Euclidean pairing conventions. Merely appending zero time coordinates to
both original Zorn vectors would have the wrong sign.

No ten-dimensional extension of the octonion multiplication is introduced.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.PolarizedQuadraticExtension55

open InfoGeometry.Clifford.PolarizedMinkowski55

abbrev NativeZorn := InfoGeometry.Canonical.ZornMatrix ℝ

/-- Explicit split into the existing eight-dimensional carrier and two scalar coordinates. -/
def boundaryZornHyperbolicEquiv : Boundary55 ≃ₗ[ℝ] (NativeZorn × (ℝ × ℝ)) where
  toFun z :=
    ({ a := z.1.1, b := z.2.1, x := z.1.2.2, y := -z.2.2.2 },
      (z.1.2.1, z.2.2.1))
  invFun p := ((p.1.a, (p.2.1, p.1.x)), (p.1.b, (p.2.2, -p.1.y)))
  left_inv z := by simp
  right_inv p := by
    apply Prod.ext
    · apply InfoGeometry.Canonical.ZornMatrix.ext <;> simp
    · rfl
  map_add' z w := by
    apply Prod.ext
    · apply InfoGeometry.Canonical.ZornMatrix.ext <;> simp [neg_add]
    · rfl
  map_smul' r z := by
    apply Prod.ext
    · apply InfoGeometry.Canonical.ZornMatrix.ext <;> simp
    · rfl

/-- The exact old norm plus a hyperbolic-plane term. -/
theorem boundaryZornHyperbolic_quadratic (z : Boundary55) :
    boundaryQuadratic z =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (boundaryZornHyperbolicEquiv z).1 -
        (boundaryZornHyperbolicEquiv z).2.1 * (boundaryZornHyperbolicEquiv z).2.2 := by
  simp [boundaryZornHyperbolicEquiv, InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
    InfoGeometry.Canonical.ZornMatrix.dot, Fin.sum_univ_three]
  ring

/-- Norm-compatible embedding of the actual Zorn carrier. -/
def zornEmbedding : NativeZorn →ₗ[ℝ] Boundary55 where
  toFun X := ((X.a, (0, X.x)), (X.b, (0, -X.y)))
  map_add' X Y := by simp [neg_add]
  map_smul' r X := by simp

theorem zornEmbedding_injective : Function.Injective zornEmbedding := by
  intro X Y h
  have hh := congrArg (fun z => (boundaryZornHyperbolicEquiv z).1) h
  simpa [boundaryZornHyperbolicEquiv, zornEmbedding] using hh

/-- The original split-octonionic norm is preserved on this selected subspace. -/
theorem zornEmbedding_norm (X : NativeZorn) :
    boundaryQuadratic (zornEmbedding X) = InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X := by
  rw [boundaryZornHyperbolic_quadratic]
  simp [zornEmbedding, boundaryZornHyperbolicEquiv]

/-- The naive spatial inclusion gives the opposite sign for the off-diagonal norm. -/
theorem naive_spatial_inclusion (X : NativeZorn) :
    boundaryQuadratic ((X.a, (0, X.x)), (X.b, (0, X.y))) =
      X.a * X.b + InfoGeometry.Canonical.ZornMatrix.dot X.x X.y := by
  simp [InfoGeometry.Canonical.ZornMatrix.dot, Fin.sum_univ_three]

/-- Nullness is inherited without asserting any new multiplication. -/
theorem zornEmbedding_null_iff (X : NativeZorn) :
    boundaryQuadratic (zornEmbedding X) = 0 ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull X := by
  rw [zornEmbedding_norm]
  rfl

end InfoGeometry.Algebra.Zorn.PolarizedQuadraticExtension55
