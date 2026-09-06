import InfoGeometry.Projective.ExteriorKleinTwoPlaneIncidence
import InfoGeometry.Projective.KleinQuadricIncidence

/-!
# Coordinate compatibility of exterior and Klein incidence

The intrinsic incidence owner characterizes intersection of real two-planes
by vanishing of a combined top exterior product.  This file proves that its
scalar coordinate is exactly the repository's native six-coordinate Klein
polar incidence form.

Thus plane intersection, top-wedge degeneracy, a four-by-four determinant,
and the Klein polar equation are one kernel-checked relation.  No additional
projective, twistor, or Grassmannian carrier is introduced.
-/

noncomputable section

namespace InfoGeometry.Projective.ExteriorKleinCoordinateIncidence

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorKleinProjective
open InfoGeometry.Projective.ExteriorKleinFrameSurjection
open InfoGeometry.Projective.ExteriorKleinTwoPlaneIncidence

abbrev ExteriorFour := ⋀[ℝ]^4 Vec4

/-- The fixed order `t,x,y,z` on the four native coordinates. -/
def finFourIndex : Fin 4 → I4
  | 0 => I4.t
  | 1 => I4.x
  | 2 => I4.y
  | 3 => I4.z
  | _ => I4.t

def coordinateDual (i : Fin 4) : Module.Dual ℝ Vec4 :=
  LinearMap.proj (finFourIndex i)

/-- Evaluation of a top exterior vector in the ordered native coordinate
coframe. -/
noncomputable def topExteriorCoordinate : ExteriorFour →ₗ[ℝ] ℝ :=
  (exteriorPower.alternatingMapToDual ℝ Vec4 4) coordinateDual

def standardFrame (i : Fin 4) : Vec4 :=
  Pi.single (finFourIndex i) 1

theorem topExteriorCoordinate_standard :
    topExteriorCoordinate (exteriorPower.ιMulti ℝ 4 standardFrame) = 1 := by
  rw [topExteriorCoordinate,
    exteriorPower.alternatingMapToDual_apply_ιMulti]
  rw [show Matrix.of (fun i j => coordinateDual j (standardFrame i)) = 1 by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinateDual, standardFrame, finFourIndex]]
  exact Matrix.det_one

theorem topExteriorCoordinate_surjective :
    Function.Surjective topExteriorCoordinate := by
  intro r
  refine ⟨r • exteriorPower.ιMulti ℝ 4 standardFrame, ?_⟩
  rw [map_smul, topExteriorCoordinate_standard, smul_eq_mul, mul_one]

theorem topExteriorCoordinate_finrank_eq :
    Module.finrank ℝ ExteriorFour = Module.finrank ℝ ℝ := by
  have hcard : Fintype.card I4 = 4 := by decide
  rw [exteriorPower.finrank_eq ℝ 4, Module.finrank_pi, hcard,
    Module.finrank_self]
  norm_num

/-- A top exterior vector is determined by its scalar coordinate. -/
theorem topExteriorCoordinate_injective :
    Function.Injective topExteriorCoordinate :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    topExteriorCoordinate_finrank_eq).2 topExteriorCoordinate_surjective

/-- Matrix having four native vectors as rows in `t,x,y,z` order. -/
def rowsMatrix (u v s t : Vec4) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => ![u, v, s, t] i (finFourIndex j)

theorem topExteriorCoordinate_ιMulti_eq_det (u v s t : Vec4) :
    topExteriorCoordinate (exteriorPower.ιMulti ℝ 4 ![u, v, s, t]) =
      (rowsMatrix u v s t).det := by
  rw [topExteriorCoordinate,
    exteriorPower.alternatingMapToDual_apply_ιMulti]
  congr 1

theorem top_wedge_eq_zero_iff_det_eq_zero (u v s t : Vec4) :
    exteriorPower.ιMulti ℝ 4 ![u, v, s, t] = 0 ↔
      (rowsMatrix u v s t).det = 0 := by
  constructor
  · intro h
    rw [← topExteriorCoordinate_ιMulti_eq_det, h, map_zero]
  · intro h
    apply topExteriorCoordinate_injective
    rw [topExteriorCoordinate_ιMulti_eq_det, h, map_zero]

/-- Six-coordinate Plücker readout in the carrier owned by
`KleinQuadricIncidence`. -/
def linePlucker (u v : Vec4) :
    InfoGeometry.Projective.KleinQuadric.Plucker6 ℝ where
  p01 := u I4.t * v I4.x - u I4.x * v I4.t
  p02 := u I4.t * v I4.y - u I4.y * v I4.t
  p03 := u I4.t * v I4.z - u I4.z * v I4.t
  p12 := u I4.x * v I4.y - u I4.y * v I4.x
  p13 := u I4.x * v I4.z - u I4.z * v I4.x
  p23 := u I4.y * v I4.z - u I4.z * v I4.y

/-- The four-frame determinant is the native Klein polar incidence pairing
of the two corresponding Plücker lines. -/
theorem det_rows_eq_incidence (u v s t : Vec4) :
    (rowsMatrix u v s t).det =
      InfoGeometry.Projective.KleinQuadricIncidence.Plucker6.incidenceForm
        (linePlucker u v) (linePlucker s t) := by
  have h12 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h21 : (2 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
  have h22 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h31 : (3 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
  have h32 : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := by decide
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Matrix.det_fin_three, rowsMatrix, finFourIndex,
    linePlucker,
    InfoGeometry.Projective.KleinQuadricIncidence.Plucker6.incidenceForm,
    h12, h21, h22, h31, h32]
  ring

theorem combinedFrame_eq_vec (uv st : NondegenerateExteriorFrame) :
    combinedFrame uv st = ![uv.1 0, uv.1 1, st.1 0, st.1 1] := by
  funext i
  fin_cases i <;> rfl

/-- The coordinate-free incidence transported to the projective Klein locus
is exactly the existing six-coordinate polar incidence equation. -/
theorem kleinIncident_iff_coordinate_incidence
    (uv st : NondegenerateExteriorFrame) :
    KleinIncident (frameToKleinLocus uv) (frameToKleinLocus st) ↔
      InfoGeometry.Projective.KleinQuadricIncidence.Plucker6.incidenceForm
        (linePlucker (uv.1 0) (uv.1 1))
        (linePlucker (st.1 0) (st.1 1)) = 0 := by
  rw [kleinIncident_frameToKleinLocus_iff_wedge_eq_zero,
    combinedFrame_eq_vec, top_wedge_eq_zero_iff_det_eq_zero,
    det_rows_eq_incidence]

end InfoGeometry.Projective.ExteriorKleinCoordinateIncidence
