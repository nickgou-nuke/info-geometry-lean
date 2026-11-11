/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.ExteriorKleinOperatorAction
import InfoGeometry.Projective.ExteriorKleinNullTwistorIncidence
import Mathlib.LinearAlgebra.Determinant

/-!
# Determinant covariance of the native Klein form

The ordered top exterior coordinate transforms by the determinant. Its
identification with the Klein polar pairing on simple wedges extends by the
exterior-power universal property to every pair of bivectors. The quadratic
law then follows from polarization over `ℝ`. No decomposability, invertibility,
orthogonality, or commutativity of the endomorphisms is assumed in these laws.
-/

noncomputable section

namespace InfoGeometry.Projective.ExteriorKleinOperatorAction

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorPowerPluckerBridge
open InfoGeometry.Projective.ExteriorKleinProjective
open InfoGeometry.Projective.ExteriorKleinCoordinateIncidence
open InfoGeometry.Projective.ExteriorKleinNullTwistor
open InfoGeometry.Projective.ExteriorKleinNullTwistorIncidence

/-- The fixed `t,x,y,z` coordinate order as an equivalence. -/
def finFourIndexEquiv : Fin 4 ≃ I4 where
  toFun := finFourIndex
  invFun
    | I4.t => 0
    | I4.x => 1
    | I4.y => 2
    | I4.z => 3
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by cases i <;> rfl

/-- The existing standard frame, now carrying its native Mathlib basis laws. -/
def coordinateBasis : Module.Basis (Fin 4) ℝ Vec4 :=
  (Pi.basisFun ℝ I4).reindex finFourIndexEquiv.symm

theorem coordinateBasis_eq_standardFrame :
    (coordinateBasis : Fin 4 → Vec4) = standardFrame := by
  funext i j
  simp [coordinateBasis, standardFrame, finFourIndexEquiv, Pi.basisFun,
    Pi.single_apply]

theorem topExteriorCoordinate_ιMulti_eq_basis_det (v : Fin 4 → Vec4) :
    topExteriorCoordinate (exteriorPower.ιMulti ℝ 4 v) = coordinateBasis.det v := by
  let f : Vec4 [⋀^Fin 4]→ₗ[ℝ] ℝ :=
    topExteriorCoordinate.compAlternatingMap (exteriorPower.ιMulti ℝ 4)
  have h := f.eq_smul_basis_det coordinateBasis
  have hb : f coordinateBasis = 1 := by
    change topExteriorCoordinate
      (exteriorPower.ιMulti ℝ 4 (coordinateBasis : Fin 4 → Vec4)) = 1
    rw [coordinateBasis_eq_standardFrame, topExteriorCoordinate_standard]
  rw [hb, one_smul] at h
  exact DFunLike.congr_fun h v

/-- Covariance of the entire fourth exterior power, including singular actions. -/
theorem topExteriorCoordinate_map (A : Module.End ℝ Vec4) (Z : ExteriorFour) :
    topExteriorCoordinate (exteriorPower.map 4 A Z) =
      LinearMap.det A * topExteriorCoordinate Z := by
  have h : topExteriorCoordinate.comp (exteriorPower.map 4 A) =
      LinearMap.det A • topExteriorCoordinate := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change topExteriorCoordinate (exteriorPower.map 4 A (exteriorPower.ιMulti ℝ 4 v)) =
      LinearMap.det A * topExteriorCoordinate (exteriorPower.ιMulti ℝ 4 v)
    rw [exteriorPower.map_apply_ιMulti, topExteriorCoordinate_ιMulti_eq_basis_det,
      topExteriorCoordinate_ιMulti_eq_basis_det, Module.Basis.det_comp]
  exact DFunLike.congr_fun h Z

/-- The unnormalized polar form is the ordered top exterior coordinate on
two simple wedges. In particular, its diagonal is twice the quadratic form. -/
theorem exteriorKleinPolar_pair (u v s t : Vec4) :
    QuadraticMap.polar exteriorKleinQuadraticForm
        (exteriorPower.ιMulti ℝ 2 ![u, v])
        (exteriorPower.ιMulti ℝ 2 ![s, t]) =
      topExteriorCoordinate (exteriorPower.ιMulti ℝ 4 ![u, v, s, t]) := by
  rw [exteriorKleinQuadraticForm_polar,
    exteriorBivectorLinearEquiv_ιMulti, exteriorBivectorLinearEquiv_ιMulti,
    topExteriorCoordinate_ιMulti_eq_det, det_rows_eq_incidence]
  simp only [wedgeVec4, linePlucker,
    InfoGeometry.Projective.KleinQuadricIncidence.Plucker6.incidenceForm]
  ring

theorem exteriorKleinPolar_map_pair (A : Module.End ℝ Vec4) (u v s t : Vec4) :
    QuadraticMap.polar exteriorKleinQuadraticForm
        (exteriorPower.map 2 A (exteriorPower.ιMulti ℝ 2 ![u, v]))
        (exteriorPower.map 2 A (exteriorPower.ιMulti ℝ 2 ![s, t])) =
      LinearMap.det A * QuadraticMap.polar exteriorKleinQuadraticForm
        (exteriorPower.ιMulti ℝ 2 ![u, v])
        (exteriorPower.ιMulti ℝ 2 ![s, t]) := by
  rw [exteriorMap_pair, exteriorMap_pair, exteriorKleinPolar_pair, exteriorKleinPolar_pair]
  have hf : A ∘ ![u, v, s, t] = ![A u, A v, A s, A t] := by
    funext i
    fin_cases i <;> rfl
  simpa only [exteriorPower.map_apply_ιMulti, hf] using
    topExteriorCoordinate_map A (exteriorPower.ιMulti ℝ 4 ![u, v, s, t])

/-- Full bilinear covariance: neither input is required to be a simple wedge. -/
theorem exteriorKleinPolar_map (A : Module.End ℝ Vec4) (X Y : ExteriorSquare) :
    QuadraticMap.polar exteriorKleinQuadraticForm
        (exteriorPower.map 2 A X) (exteriorPower.map 2 A Y) =
      LinearMap.det A * QuadraticMap.polar exteriorKleinQuadraticForm X Y := by
  let L : ExteriorSquare →ₗ[ℝ] ExteriorSquare →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun U V => QuadraticMap.polar exteriorKleinQuadraticForm
        (exteriorPower.map 2 A U) (exteriorPower.map 2 A V))
      (fun U U' V => by rw [map_add, QuadraticMap.polar_add_left])
      (fun c U V => by rw [map_smul, QuadraticMap.polar_smul_left])
      (fun U V V' => by rw [map_add, QuadraticMap.polar_add_right])
      (fun c U V => by rw [map_smul, QuadraticMap.polar_smul_right])
  have h : L = LinearMap.det A • exteriorKleinQuadraticForm.polarBilin := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro u
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change QuadraticMap.polar exteriorKleinQuadraticForm
        (exteriorPower.map 2 A (exteriorPower.ιMulti ℝ 2 u))
        (exteriorPower.map 2 A (exteriorPower.ιMulti ℝ 2 v)) =
      LinearMap.det A * QuadraticMap.polar exteriorKleinQuadraticForm
        (exteriorPower.ιMulti ℝ 2 u) (exteriorPower.ιMulti ℝ 2 v)
    have hu : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    rw [hu, hv]
    exact exteriorKleinPolar_map_pair A (u 0) (u 1) (v 0) (v 1)
  exact congrArg (fun T : ExteriorSquare →ₗ[ℝ] ExteriorSquare →ₗ[ℝ] ℝ => T X Y) h

theorem exteriorKleinPolar_map_eq_zero_iff (A : Module.End ℝ Vec4)
    (hA : LinearMap.det A ≠ 0) (X Y : ExteriorSquare) :
    QuadraticMap.polar exteriorKleinQuadraticForm
        (exteriorPower.map 2 A X) (exteriorPower.map 2 A Y) = 0 ↔
      QuadraticMap.polar exteriorKleinQuadraticForm X Y = 0 := by
  rw [exteriorKleinPolar_map]
  simp [hA]

theorem exteriorKleinPolar_map_of_det_one (A : Module.End ℝ Vec4)
    (hA : LinearMap.det A = 1) (X Y : ExteriorSquare) :
    QuadraticMap.polar exteriorKleinQuadraticForm
        (exteriorPower.map 2 A X) (exteriorPower.map 2 A Y) =
      QuadraticMap.polar exteriorKleinQuadraticForm X Y := by
  rw [exteriorKleinPolar_map, hA, one_mul]

/-- Determinant covariance on every bivector, including nondecomposable ones. -/
theorem exteriorKleinQuadraticForm_map (A : Module.End ℝ Vec4) (X : ExteriorSquare) :
    exteriorKleinQuadraticForm (exteriorPower.map 2 A X) =
      LinearMap.det A * exteriorKleinQuadraticForm X := by
  have h := exteriorKleinPolar_map A X X
  simp only [QuadraticMap.polar_self, two_smul] at h
  nlinarith

theorem kleinForm_bivectorAction (A : Module.End ℝ Vec4) (P : Bivector4) :
    kleinForm (bivectorAction A P) = LinearMap.det A * kleinForm P := by
  simpa [exteriorKleinQuadraticForm_apply, exteriorKleinForm, bivectorAction] using
    exteriorKleinQuadraticForm_map A (exteriorBivectorLinearEquiv.symm P)

theorem exteriorKleinQuadraticForm_map_of_det_one (A : Module.End ℝ Vec4)
    (hA : LinearMap.det A = 1) (X : ExteriorSquare) :
    exteriorKleinQuadraticForm (exteriorPower.map 2 A X) =
      exteriorKleinQuadraticForm X := by
  rw [exteriorKleinQuadraticForm_map, hA, one_mul]

theorem kleinForm_bivectorAction_of_det_one (A : Module.End ℝ Vec4)
    (hA : LinearMap.det A = 1) (P : Bivector4) :
    kleinForm (bivectorAction A P) = kleinForm P := by
  rw [kleinForm_bivectorAction, hA, one_mul]

theorem kleinForm_bivectorAction_eq_zero_iff (A : Module.End ℝ Vec4)
    (hA : LinearMap.det A ≠ 0) (P : Bivector4) :
    kleinForm (bivectorAction A P) = 0 ↔ kleinForm P = 0 := by
  rw [kleinForm_bivectorAction]
  simp [hA]

end InfoGeometry.Projective.ExteriorKleinOperatorAction
