import InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
import InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry

/-!
# The ten-dimensional polarized Minkowski quadratic carrier

The source's coordinates `(alpha,beta,U,V)` are grouped as `((alpha,U),(beta,V))`.
The four-vectors reuse `Cl55MinkowskiCelestialSlice.Minkowski13`. This is a
quadratic space, not a ten-dimensional octonion algebra. No multiplication
instance is installed on the carrier.

The quadratic form is constructed independently from a native bilinear map.
Its explicit polarization is a bijective quadratic isometry to the existing
`Clifford55.Q55`, not merely an equality of unbundled scalar expressions.
-/

noncomputable section

namespace InfoGeometry.Clifford.PolarizedMinkowski55

open scoped BigOperators
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice

abbrev Boundary55 := (ℝ × Minkowski13) × (ℝ × Minkowski13)

/-- The mixed pairing whose diagonal is the proposed quadratic expression. -/
def mixedPairing : LinearMap.BilinForm ℝ Boundary55 :=
  LinearMap.mk₂ ℝ
    (fun z w => z.1.1 * w.2.1 - z.1.2.1 * w.2.2.1 +
      ∑ i : Fin 3, z.1.2.2 i * w.2.2.2 i)
    (by intros; simp [add_mul, Finset.sum_add_distrib] <;> ring)
    (by intros; simp [mul_assoc, Finset.mul_sum] <;> ring)
    (by intros; simp [mul_add, Finset.sum_add_distrib] <;> ring)
    (by intros; simp [mul_left_comm, Finset.mul_sum] <;> ring)

/-- Native quadratic form `alpha beta - <U,V>_(1,3)`. -/
def boundaryQuadratic : QuadraticForm ℝ Boundary55 := mixedPairing.toQuadraticMap

@[simp] theorem boundaryQuadratic_apply (z : Boundary55) :
    boundaryQuadratic z = z.1.1 * z.2.1 - z.1.2.1 * z.2.2.1 +
      ∑ i : Fin 3, z.1.2.2 i * z.2.2.2 i := rfl

/-- The actual inverse is part of the coordinate change. -/
def diagonalEquiv : Boundary55 ≃ₗ[ℝ] V55 where
  toFun z :=
    (![(z.1.1 + z.2.1)/2, (z.1.2.1 - z.2.2.1)/2,
        (z.1.2.2 0 + z.2.2.2 0)/2, (z.1.2.2 1 + z.2.2.2 1)/2,
        (z.1.2.2 2 + z.2.2.2 2)/2],
     ![(z.1.1 - z.2.1)/2, (z.1.2.1 + z.2.2.1)/2,
        (z.1.2.2 0 - z.2.2.2 0)/2, (z.1.2.2 1 - z.2.2.2 1)/2,
        (z.1.2.2 2 - z.2.2.2 2)/2])
  invFun w :=
    ((w.1 0 + w.2 0,
      (w.1 1 + w.2 1, ![w.1 2 + w.2 2, w.1 3 + w.2 3, w.1 4 + w.2 4])),
     (w.1 0 - w.2 0,
      (w.2 1 - w.1 1, ![w.1 2 - w.2 2, w.1 3 - w.2 3, w.1 4 - w.2 4])))
  left_inv z := by
    rcases z with ⟨⟨a, t, u⟩, ⟨b, s, v⟩⟩
    ext i <;> (try fin_cases i) <;> simp <;> ring
  right_inv w := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp <;> ring
  map_add' z w := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp <;> ring
  map_smul' r z := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp <;> ring

/-- The independent quadratic construction equals the existing split form. -/
theorem diagonalEquiv_quadratic (z : Boundary55) :
    Q55 (diagonalEquiv z) = boundaryQuadratic z := by
  simp [diagonalEquiv, Q55_apply, Fin.sum_univ_succ]
  ring

/-- A genuine isometry equivalence into the repository's native `(5,5)` space. -/
def diagonalIsometry : boundaryQuadratic.IsometryEquiv Q55 where
  toLinearEquiv := diagonalEquiv
  map_app' := diagonalEquiv_quadratic

/-- Actual dimension, not a dimension label attached to the carrier. -/
theorem boundary_finrank : Module.finrank ℝ Boundary55 = 10 := by
  simp [Boundary55, Minkowski13, Module.finrank_prod, Module.finrank_pi_fintype]

/-- The polar form, with the conventional factor of two retained. -/
theorem boundary_polar (z w : Boundary55) :
    QuadraticMap.polar boundaryQuadratic z w = mixedPairing z w + mixedPairing w z := by
  simp [QuadraticMap.polar, mixedPairing, Fin.sum_univ_three]
  ring

/-- The scalar boundary directions are null, but their sum is not null. -/
def alphaRay : Boundary55 := ((1, 0), (0, 0))
def betaRay : Boundary55 := ((0, 0), (1, 0))

@[simp] theorem alphaRay_null : boundaryQuadratic alphaRay = 0 := by
  simp [alphaRay]

@[simp] theorem betaRay_null : boundaryQuadratic betaRay = 0 := by
  simp [betaRay]

@[simp] theorem boundary_rays_polar :
    QuadraticMap.polar boundaryQuadratic alphaRay betaRay = 1 := by
  simp [QuadraticMap.polar, alphaRay, betaRay]

/-- Both half-carriers are totally null; their mixed pairing is essential. -/
theorem left_half_null (a : ℝ) (u : Minkowski13) :
    boundaryQuadratic ((a, u), (0, 0)) = 0 := by simp

theorem right_half_null (b : ℝ) (v : Minkowski13) :
    boundaryQuadratic ((0, 0), (b, v)) = 0 := by simp

/-- Native Clifford functoriality lifts the quadratic isometry. -/
def boundaryCliffordEquiv : CliffordAlgebra boundaryQuadratic ≃ₐ[ℝ] Cl55 :=
  CliffordAlgebra.equivOfIsometry diagonalIsometry

@[simp] theorem boundaryCliffordEquiv_ι (z : Boundary55) :
    boundaryCliffordEquiv (CliffordAlgebra.ι boundaryQuadratic z) =
      ι55 (diagonalEquiv z) := by
  exact CliffordAlgebra.map_apply_ι _ _

/-- The new coordinate carrier enters the existing neutral exterior-spinor carrier. -/
def boundaryToNeutral : Boundary55 ≃ₗ[ℝ]
    SplitClifford55ExteriorSpinor.NeutralSpace :=
  diagonalEquiv.trans Cl55NeutralHyperbolicIsometry.neutralToV55.symm

/-- Compatibility with the existing vector/covector pairing is derived. -/
theorem boundaryToNeutral_quadratic (z : Boundary55) :
    NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
      (E := SplitClifford55ExteriorSpinor.V5) (boundaryToNeutral z) =
        boundaryQuadratic z := by
  change NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
      (Cl55NeutralHyperbolicIsometry.neutralToV55.symm (diagonalEquiv z)) = _
  rw [Cl55NeutralHyperbolicIsometry.q55_neutralToV55_symm, diagonalEquiv_quadratic]

/-- The actual wedge-plus-contraction action, not a proxy 10x10 product. -/
def boundaryExteriorAction (z : Boundary55) : SplitClifford55ExteriorSpinor.SpinorEnd :=
  SplitClifford55ExteriorSpinor.neutralAction (boundaryToNeutral z)

/-- Clifford square on the existing 32-dimensional exterior spinor carrier. -/
theorem boundaryExteriorAction_sq (z : Boundary55) :
    boundaryExteriorAction z * boundaryExteriorAction z =
      boundaryQuadratic z • (1 : SplitClifford55ExteriorSpinor.SpinorEnd) := by
  rw [boundaryExteriorAction, SplitClifford55ExteriorSpinor.neutralAction_sq]
  have h := boundaryToNeutral_quadratic z
  rw [NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled_apply] at h
  rw [h]

/-- The same quadratic space generates the existing full matrix Clifford algebra. -/
def boundaryCliffordMatrixEquiv : CliffordAlgebra boundaryQuadratic ≃ₐ[ℝ]
    InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  boundaryCliffordEquiv.trans Clifford55.cl55SpinorAlgEquiv

/-- Distinguish a vector's Clifford action from multiplication on the vector carrier. -/
def boundaryMatrixAction (z : Boundary55) : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  boundaryCliffordMatrixEquiv (CliffordAlgebra.ι boundaryQuadratic z)

theorem boundaryMatrixAction_sq (z : Boundary55) :
    boundaryMatrixAction z * boundaryMatrixAction z =
      algebraMap ℝ _ (boundaryQuadratic z) := by
  unfold boundaryMatrixAction
  rw [← map_mul, CliffordAlgebra.ι_sq_scalar, AlgEquiv.commutes]

/-- The anticommutator is exactly the polarization, with no lost factor of two. -/
theorem boundaryMatrixAction_anticommutator (z w : Boundary55) :
    boundaryMatrixAction z * boundaryMatrixAction w +
      boundaryMatrixAction w * boundaryMatrixAction z =
        algebraMap ℝ _ (QuadraticMap.polar boundaryQuadratic z w) := by
  unfold boundaryMatrixAction
  rw [← map_mul, ← map_mul, ← map_add, CliffordAlgebra.ι_mul_ι_add_swap,
    AlgEquiv.commutes]

/-- The two boundary null directions give nilpotent, not idempotent, Clifford operators. -/
theorem boundary_scalar_nilpotents :
    boundaryMatrixAction alphaRay * boundaryMatrixAction alphaRay = 0 ∧
      boundaryMatrixAction betaRay * boundaryMatrixAction betaRay = 0 := by
  constructor <;> rw [boundaryMatrixAction_sq] <;> simp

/-- Their mixed operator anticommutator is the identity at this normalization. -/
theorem boundary_scalar_CAR :
    boundaryMatrixAction alphaRay * boundaryMatrixAction betaRay +
      boundaryMatrixAction betaRay * boundaryMatrixAction alphaRay = 1 := by
  rw [boundaryMatrixAction_anticommutator, boundary_rays_polar, map_one]

end InfoGeometry.Clifford.PolarizedMinkowski55
