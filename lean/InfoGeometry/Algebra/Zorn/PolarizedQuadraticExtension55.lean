import InfoGeometry.Clifford.PolarizedMinkowski55
import InfoGeometry.Algebra.Zorn.Basic
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

/-! The existing real Zorn carrier embeds into the polarized ten-dimensional
carrier after adjoining a hyperbolic plane.  The sign on the lower spatial
slot is essential for compatibility with the two quadratic forms. -/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.PolarizedQuadraticExtension55

open InfoGeometry.Clifford.PolarizedMinkowski55
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

abbrev NativeZorn := InfoGeometry.Canonical.ZornMatrix ℝ

def boundaryZornHyperbolicEquiv : Boundary55 ≃ₗ[ℝ] (NativeZorn × (ℝ × ℝ)) where
  toFun z :=
    ({ a := z.1.1, b := z.2.1, x := z.1.2.2, y := -z.2.2.2 },
      (z.1.2.1, z.2.2.1))
  invFun p := ((p.1.a, (p.2.1, p.1.x)), (p.1.b, (p.2.2, -p.1.y)))
  left_inv z := by simp
  right_inv p := by
    apply Prod.ext
    · apply InfoGeometry.Canonical.ZornMatrix.ext <;> simp
    · ext <;> simp <;> abel
  map_add' z w := by
    apply Prod.ext
    · ext <;> simp [InfoGeometry.Canonical.ZornMatrix.smul_a,
        InfoGeometry.Canonical.ZornMatrix.smul_b,
        InfoGeometry.Canonical.ZornMatrix.smul_x,
        InfoGeometry.Canonical.ZornMatrix.smul_y] <;> ring
    · ext <;> simp <;> abel
  map_smul' r z := by
    apply Prod.ext
    · ext <;> simp [InfoGeometry.Canonical.ZornMatrix.smul_a,
        InfoGeometry.Canonical.ZornMatrix.smul_b,
        InfoGeometry.Canonical.ZornMatrix.smul_x,
        InfoGeometry.Canonical.ZornMatrix.smul_y, smul_eq_mul] <;> ring
    · rfl

theorem boundaryZornHyperbolic_quadratic (z : Boundary55) :
    boundaryQuadratic z =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (boundaryZornHyperbolicEquiv z).1 -
        (boundaryZornHyperbolicEquiv z).2.1 * (boundaryZornHyperbolicEquiv z).2.2 := by
  simp [boundaryZornHyperbolicEquiv, InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
    realCrossProduct3, InfoGeometry.Canonical.ZornMatrix.dot, Fin.sum_univ_three]
  ring

def zornEmbedding : NativeZorn →ₗ[ℝ] Boundary55 where
  toFun X := ((X.a, (0, X.x)), (X.b, (0, -X.y)))
  map_add' X Y := by
    apply Prod.ext
    · ext <;> simp [InfoGeometry.Canonical.ZornMatrix.smul_a,
        InfoGeometry.Canonical.ZornMatrix.smul_b,
        InfoGeometry.Canonical.ZornMatrix.smul_x,
        InfoGeometry.Canonical.ZornMatrix.smul_y] <;> ring
    · ext <;> simp <;> abel
  map_smul' r X := by
    apply Prod.ext
    · ext <;> simp [InfoGeometry.Canonical.ZornMatrix.smul_a,
        InfoGeometry.Canonical.ZornMatrix.smul_b,
        InfoGeometry.Canonical.ZornMatrix.smul_x,
        InfoGeometry.Canonical.ZornMatrix.smul_y, smul_eq_mul] <;> ring
    · ext <;> simp [InfoGeometry.Canonical.ZornMatrix.smul_a,
        InfoGeometry.Canonical.ZornMatrix.smul_b,
        InfoGeometry.Canonical.ZornMatrix.smul_x,
        InfoGeometry.Canonical.ZornMatrix.smul_y, smul_eq_mul] <;> ring

theorem zornEmbedding_injective : Function.Injective zornEmbedding := by
  intro X Y h
  have hh := congrArg (fun z => (boundaryZornHyperbolicEquiv z).1) h
  cases X
  cases Y
  simpa [boundaryZornHyperbolicEquiv, zornEmbedding] using hh

theorem zornEmbedding_norm (X : NativeZorn) :
    boundaryQuadratic (zornEmbedding X) =
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 X := by
  rw [boundaryZornHyperbolic_quadratic]
  simp [zornEmbedding, boundaryZornHyperbolicEquiv]

theorem naive_spatial_inclusion (X : NativeZorn) :
    boundaryQuadratic ((X.a, (0, X.x)), (X.b, (0, X.y))) =
      X.a * X.b + InfoGeometry.Canonical.ZornMatrix.dot X.x X.y := by
  simp [InfoGeometry.Canonical.ZornMatrix.dot, Fin.sum_univ_three]

theorem zornEmbedding_null_iff (X : NativeZorn) :
    boundaryQuadratic (zornEmbedding X) = 0 ↔
    InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 X := by
  rw [zornEmbedding_norm]
  rfl

end InfoGeometry.Algebra.Zorn.PolarizedQuadraticExtension55
