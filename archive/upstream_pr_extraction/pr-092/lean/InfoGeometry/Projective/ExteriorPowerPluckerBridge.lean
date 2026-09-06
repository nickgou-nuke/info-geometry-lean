import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.KleinExteriorAlternating
import InfoGeometry.Projective.KleinQuadricPlucker

/-!
# Exterior-power readout for the six Plücker coordinates

This is the first literal exterior-power layer behind the coordinate
`Bivector4` owner.  The alternating map is built from the six (2\times2)
minors, and Mathlib's universal property of `⋀[ℝ]^2` produces the linear
readout.  No dimension or Grassmannian assertion is bundled into this file.
-/

noncomputable section

namespace InfoGeometry.Projective.ExteriorPowerPluckerBridge

open InfoGeometry.Canonical.FierzKleinFoundation

private abbrev CoordinatePlucker6 :=
  _root_.InfoGeometry.Projective.KleinQuadricPlucker.Plucker6 ℝ

private abbrev CoordinateVec4 :=
  _root_.InfoGeometry.Projective.KleinQuadricPlucker.Vec4 ℝ

private def toCoordinatePlucker (P : Bivector4) : CoordinatePlucker6 :=
  ⟨P.p01, P.p02, P.p03, P.p12, P.p13, P.p23⟩

private def fromCoordinatePlucker (P : CoordinatePlucker6) : Bivector4 :=
  ⟨P.p01, P.p02, P.p03, P.p12, P.p13, P.p23⟩

private def toCoordinateVec4 (u : Vec4) : CoordinateVec4 :=
  ⟨u I4.t, u I4.x, u I4.y, u I4.z⟩

private def fromCoordinateVec4 (u : CoordinateVec4) : Vec4 :=
  fun i => match i with
    | I4.t => u.x0
    | I4.x => u.x1
    | I4.y => u.x2
    | I4.z => u.x3

private theorem wedgeVec4_fromCoordinate (u v : CoordinateVec4) :
    wedgeVec4 (fromCoordinateVec4 u) (fromCoordinateVec4 v) =
      fromCoordinatePlucker
        (_root_.InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.pluckerLine u v) := by
  cases u
  cases v
  apply Bivector4.ext <;> rfl

private theorem fromCoordinatePlucker_toCoordinate (P : Bivector4) :
    fromCoordinatePlucker (toCoordinatePlucker P) = P := by
  rfl

private theorem coordinateKleinQ_eq_kleinForm (P : Bivector4) :
    _root_.InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
        (toCoordinatePlucker P) = kleinForm P := by
  rfl

private theorem bivector4_exists_wedge_of_klein
    (P : Bivector4) (hP : kleinForm P = 0) :
    ∃ u v : Vec4, wedgeVec4 u v = P := by
  have hK :
      _root_.InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
          (toCoordinatePlucker P) = 0 := by
    rw [coordinateKleinQ_eq_kleinForm, hP]
  by_cases hp01 : (toCoordinatePlucker P).p01 ≠ 0
  · obtain ⟨u, v, huv⟩ :=
      _root_.InfoGeometry.Projective.KleinQuadricPlucker.kleinRel_exists_pluckerLine_of_p01_ne_zero
        (toCoordinatePlucker P) hK hp01
    refine ⟨fromCoordinateVec4 u, fromCoordinateVec4 v, ?_⟩
    rw [wedgeVec4_fromCoordinate, huv, fromCoordinatePlucker_toCoordinate]
  · by_cases hp02 : (toCoordinatePlucker P).p02 ≠ 0
    · obtain ⟨u, v, huv⟩ :=
        _root_.InfoGeometry.Projective.KleinQuadricPlucker.kleinRel_exists_pluckerLine_of_p02_ne_zero
          (toCoordinatePlucker P) hK hp02
      refine ⟨fromCoordinateVec4 u, fromCoordinateVec4 v, ?_⟩
      rw [wedgeVec4_fromCoordinate, huv, fromCoordinatePlucker_toCoordinate]
    · by_cases hp03 : (toCoordinatePlucker P).p03 ≠ 0
      · obtain ⟨u, v, huv⟩ :=
          _root_.InfoGeometry.Projective.KleinQuadricPlucker.kleinRel_exists_pluckerLine_of_p03_ne_zero
            (toCoordinatePlucker P) hK hp03
        refine ⟨fromCoordinateVec4 u, fromCoordinateVec4 v, ?_⟩
        rw [wedgeVec4_fromCoordinate, huv, fromCoordinatePlucker_toCoordinate]
      · have h01 : P.p01 = 0 := by
          by_contra h
          exact hp01 (by simpa [toCoordinatePlucker] using h)
        have h02 : P.p02 = 0 := by
          by_contra h
          exact hp02 (by simpa [toCoordinatePlucker] using h)
        have h03 : P.p03 = 0 := by
          by_contra h
          exact hp03 (by simpa [toCoordinatePlucker] using h)
        by_cases hp12 : P.p12 ≠ 0
        · let u : Vec4 := fun i => match i with
            | I4.t => 0
            | I4.x => 1
            | I4.y => 0
            | I4.z => -(P.p23 / P.p12)
          let v : Vec4 := fun i => match i with
            | I4.t => 0
            | I4.x => 0
            | I4.y => P.p12
            | I4.z => P.p13
          refine ⟨u, v, ?_⟩
          apply Bivector4.ext <;>
            simp [u, v, wedgeVec4, h01, h02, h03]
          · simp only [div_mul_cancel₀ _ hp12]
        · by_cases hp13 : P.p13 ≠ 0
          · let u : Vec4 := fun i => match i with
              | I4.t => 0
              | I4.x => 1
              | I4.y => P.p23 / P.p13
              | I4.z => 0
            let v : Vec4 := fun i => match i with
              | I4.t => 0
              | I4.x => 0
              | I4.y => 0
              | I4.z => P.p13
            refine ⟨u, v, ?_⟩
            have h12 : P.p12 = 0 := not_ne_iff.mp hp12
            apply Bivector4.ext
            · simp [u, v, wedgeVec4, h01]
            · simp [u, v, wedgeVec4, h02]
            · simp [u, v, wedgeVec4, h03]
            · simp [u, v, wedgeVec4, h12]
            · simp [u, v, wedgeVec4]
            · simp [u, v, wedgeVec4]
              exact div_mul_cancel₀ P.p23 hp13
          · let u : Vec4 := fun i => match i with
              | I4.t => 0
              | I4.x => 0
              | I4.y => 1
              | I4.z => 0
            let v : Vec4 := fun i => match i with
              | I4.t => 0
              | I4.x => 0
              | I4.y => 0
              | I4.z => P.p23
            refine ⟨u, v, ?_⟩
            have h12 : P.p12 = 0 := not_ne_iff.mp hp12
            have h13 : P.p13 = 0 := not_ne_iff.mp hp13
            apply Bivector4.ext <;>
              simp [u, v, wedgeVec4, h01, h02, h03, h12, h13]

abbrev PluckerCoords := Fin 6 → ℝ

def pluckerCoords (u v : Vec4) : PluckerCoords := ![
  u I4.t * v I4.x - u I4.x * v I4.t,
  u I4.t * v I4.y - u I4.y * v I4.t,
  u I4.t * v I4.z - u I4.z * v I4.t,
  u I4.x * v I4.y - u I4.y * v I4.x,
  u I4.x * v I4.z - u I4.z * v I4.x,
  u I4.y * v I4.z - u I4.z * v I4.y]

/-- Coordinate readout of the canonical alternating Plücker wedge.

This is deliberately derived from `wedgeVec4Alternating`; the six-minor
formula has a single owner. -/
def pluckerAlternating : Vec4 [⋀^Fin 2]→ₗ[ℝ] PluckerCoords :=
  bivector4CoordinateLinearEquiv.toLinearMap.compAlternatingMap
    wedgeVec4Alternating

@[simp] theorem pluckerAlternating_apply (u v : Vec4) :
    pluckerAlternating ![u, v] = pluckerCoords u v := by
  funext i
  fin_cases i <;>
    simp [pluckerAlternating, pluckerCoords, wedgeVec4,
      bivector4CoordinateLinearEquiv_apply]

noncomputable def pluckerExteriorMap :
    (⋀[ℝ]^2 Vec4) →ₗ[ℝ] PluckerCoords :=
  exteriorPower.alternatingMapLinearEquiv pluckerAlternating

theorem pluckerExteriorMap_ιMulti (u v : Vec4) :
    pluckerExteriorMap (exteriorPower.ιMulti ℝ 2 ![u, v]) =
      pluckerCoords u v := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    pluckerAlternating ![u, v]

def i4Basis (i : I4) : Vec4 := fun j => if j = i then 1 else 0

def pluckerBasisPair (k : Fin 6) : Fin 2 → I4 := fun j =>
  if k = 0 then if j = 0 then I4.t else I4.x
  else if k = 1 then if j = 0 then I4.t else I4.y
  else if k = 2 then if j = 0 then I4.t else I4.z
  else if k = 3 then if j = 0 then I4.x else I4.y
  else if k = 4 then if j = 0 then I4.x else I4.z
  else if j = 0 then I4.y else I4.z

theorem pluckerBasisPair_readout (k : Fin 6) :
    pluckerCoords (i4Basis (pluckerBasisPair k 0))
      (i4Basis (pluckerBasisPair k 1)) = Pi.single k 1 := by
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [pluckerCoords, pluckerBasisPair, i4Basis]

theorem pluckerExteriorMap_surjective :
    Function.Surjective pluckerExteriorMap := by
  rw [← LinearMap.range_eq_top]
  apply le_antisymm le_top
  rw [← (Pi.basisFun ℝ (Fin 6)).span_eq]
  apply Submodule.span_le.2
  rintro _ ⟨k, rfl⟩
  refine ⟨exteriorPower.ιMulti ℝ 2 (fun j => i4Basis (pluckerBasisPair k j)), ?_⟩
  change pluckerExteriorMap
      (exteriorPower.ιMulti ℝ 2
        ![i4Basis (pluckerBasisPair k 0), i4Basis (pluckerBasisPair k 1)]) = _
  rw [pluckerExteriorMap_ιMulti, pluckerBasisPair_readout]
  simp [Pi.basisFun]

theorem pluckerExteriorMap_finrank_eq :
    Module.finrank ℝ (⋀[ℝ]^2 Vec4) = Module.finrank ℝ PluckerCoords := by
  have hcard : Fintype.card I4 = 4 := by decide
  rw [exteriorPower.finrank_eq ℝ 2, Module.finrank_pi, Module.finrank_pi, hcard]
  decide

noncomputable def pluckerExteriorLinearEquiv :
    (⋀[ℝ]^2 Vec4) ≃ₗ[ℝ] PluckerCoords := by
  apply LinearEquiv.ofBijective pluckerExteriorMap
  refine ⟨?_, pluckerExteriorMap_surjective⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    pluckerExteriorMap_finrank_eq).2 pluckerExteriorMap_surjective

/-- The literal exterior-power carrier and the repo's `Bivector4` carrier are
    linearly equivalent. -/
noncomputable def exteriorBivectorLinearEquiv :
    (⋀[ℝ]^2 Vec4) ≃ₗ[ℝ] Bivector4 :=
  pluckerExteriorLinearEquiv.trans bivector4CoordinateLinearEquiv.symm

theorem exteriorBivectorLinearEquiv_ιMulti (u v : Vec4) :
    exteriorBivectorLinearEquiv (exteriorPower.ιMulti ℝ 2 ![u, v]) =
      wedgeVec4 u v := by
  apply bivector4CoordinateLinearEquiv.injective
  simp [exteriorBivectorLinearEquiv, pluckerExteriorLinearEquiv,
    pluckerExteriorMap_ιMulti, pluckerCoords, wedgeVec4,
    bivector4CoordinateLinearEquiv_apply]

/-- The universal exterior wedge and the canonical coordinate alternating map
commute through the literal exterior/bivector linear equivalence. -/
theorem exteriorBivectorLinearEquiv_ιMulti_eq_alternating (u v : Vec4) :
    exteriorBivectorLinearEquiv (exteriorPower.ιMulti ℝ 2 ![u, v]) =
      wedgeVec4Alternating ![u, v] := by
  rw [exteriorBivectorLinearEquiv_ιMulti, wedgeVec4Alternating_apply]

/-- Over `ℝ`, the Klein equation is exactly the existence of a simple
coordinate wedge.  This is the affine decomposability converse, before any
projective quotient or Grassmannian packaging. -/
theorem kleinForm_eq_zero_iff_exists_wedge (P : Bivector4) :
    kleinForm P = 0 ↔ ∃ u v : Vec4, wedgeVec4 u v = P := by
  constructor
  · exact bivector4_exists_wedge_of_klein P
  · rintro ⟨u, v, rfl⟩
    exact wedgeVec4_on_klein u v

def exteriorKleinForm (X : ⋀[ℝ]^2 Vec4) : ℝ :=
  kleinForm (exteriorBivectorLinearEquiv X)

/-- The transported Klein polynomial is homogeneous of degree two. -/
theorem exteriorKleinForm_smul (c : ℝ) (X : ⋀[ℝ]^2 Vec4) :
    exteriorKleinForm (c • X) = c ^ 2 * exteriorKleinForm X := by
  unfold exteriorKleinForm
  rw [map_smul]
  change
    (c * (exteriorBivectorLinearEquiv X).p01) *
          (c * (exteriorBivectorLinearEquiv X).p23) -
        (c * (exteriorBivectorLinearEquiv X).p02) *
          (c * (exteriorBivectorLinearEquiv X).p13) +
        (c * (exteriorBivectorLinearEquiv X).p03) *
          (c * (exteriorBivectorLinearEquiv X).p12) =
      c ^ 2 * kleinForm (exteriorBivectorLinearEquiv X)
  unfold kleinForm
  ring

theorem exteriorKleinForm_ιMulti (u v : Vec4) :
    exteriorKleinForm (exteriorPower.ιMulti ℝ 2 ![u, v]) = 0 := by
  rw [exteriorKleinForm, exteriorBivectorLinearEquiv_ιMulti]
  exact wedgeVec4_on_klein u v

/-- The transported Klein null locus in the literal exterior square is
exactly the locus of decomposable degree-two tensors. -/
theorem exteriorKleinForm_eq_zero_iff_decomposable
    (X : ⋀[ℝ]^2 Vec4) :
    exteriorKleinForm X = 0 ↔
      ∃ u v : Vec4, X = exteriorPower.ιMulti ℝ 2 ![u, v] := by
  constructor
  · intro hX
    obtain ⟨u, v, huv⟩ :=
      (kleinForm_eq_zero_iff_exists_wedge
        (exteriorBivectorLinearEquiv X)).1 hX
    refine ⟨u, v, ?_⟩
    apply exteriorBivectorLinearEquiv.injective
    rw [exteriorBivectorLinearEquiv_ιMulti]
    exact huv.symm
  · rintro ⟨u, v, rfl⟩
    exact exteriorKleinForm_ιMulti u v

/-- Compatibility alias for the affine exterior-power decomposability
characterization. -/
theorem exteriorKleinForm_zero_iff_exists_ιMulti
    (X : ⋀[ℝ]^2 Vec4) :
    exteriorKleinForm X = 0 ↔
      ∃ u v : Vec4,
        X = exteriorPower.ιMulti ℝ 2 ![u, v] :=
  exteriorKleinForm_eq_zero_iff_decomposable X

theorem pluckerCoords_on_klein (u v : Vec4) :
    (pluckerCoords u v) 0 * (pluckerCoords u v) 5
      - (pluckerCoords u v) 1 * (pluckerCoords u v) 4
      + (pluckerCoords u v) 2 * (pluckerCoords u v) 3 = 0 := by
  simp [pluckerCoords]
  ring

theorem pluckerCoords_eq_wedgeVec4 (u v : Vec4) :
    Bivector4.mk (pluckerCoords u v 0) (pluckerCoords u v 1)
      (pluckerCoords u v 2) (pluckerCoords u v 3)
      (pluckerCoords u v 4) (pluckerCoords u v 5) =
      wedgeVec4 u v := by
  rfl

end InfoGeometry.Projective.ExteriorPowerPluckerBridge
