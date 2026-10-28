/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.LieJordanPeirceColimit
import InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus
import InfoGeometry.Algebra.PeirceQuadraticCycle

/-!
# Boundary and quadratic readouts in the actual matrix-tower direct limit

The existing stage maps preserve both sandwich actions, the doubled boundary,
and all quadratic pair coefficients. No diagonal subalgebra, analytic limit,
or completion is substituted for the repository's noncommutative carrier.
-/

namespace InfoGeometry.Canonical.LieJordanBoundaryColimit

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

theorem ofStage_crossTransport (n : ℕ) (u v x : Stage n) :
    ofStage n (crossTransport (R := ℝ) u v x) =
      crossTransport (R := ℝ) (ofStage n u) (ofStage n v) (ofStage n x) :=
  map_crossTransport (R := ℝ) (ofStage n) u v x

theorem ofStage_orientedTransport (n : ℕ) (u v x : Stage n) :
    ofStage n (orientedTransport (R := ℝ) u v x) =
      orientedTransport (R := ℝ) (ofStage n u) (ofStage n v) (ofStage n x) :=
  map_orientedTransport (R := ℝ) (ofStage n) u v x

theorem ofStage_boundary (n : ℕ) (u : Stage n) (z : Stage n × Stage n) :
    Prod.map (ofStage n) (ofStage n) (boundary (R := ℝ) u z) =
      boundary (R := ℝ) (ofStage n u) (Prod.map (ofStage n) (ofStage n) z) := by
  apply Prod.ext
  · change ofStage n (u * z.2 - z.2 * u) =
      ofStage n u * ofStage n z.2 - ofStage n z.2 * ofStage n u
    simp only [map_sub, map_mul]
  · change ofStage n (u * z.1 + z.1 * u) =
      ofStage n u * ofStage n z.1 + ofStage n z.1 * ofStage n u
    simp only [map_add, map_mul]

/-- Even the omitted signed sandwich obstruction survives faithful inclusion. -/
theorem oriented_defect_survives (n : ℕ) (u v x : Stage n) :
    orientedTransport (R := ℝ) (ofStage n u) (ofStage n v) (ofStage n x) ≠ 0 ↔
      orientedTransport (R := ℝ) u v x ≠ 0 := by
  have hinj : Function.Injective (ofStage n) := by
    apply directLimitOf_injective stageBond
    intro k
    change Function.Injective (matStageEmbed k)
    exact matStageEmbed_injective k
  rw [← ofStage_orientedTransport]
  constructor
  · intro hne hz
    apply hne
    rw [hz, map_zero]
  · intro hne hz
    apply hne
    apply hinj
    simpa only [map_zero] using hz

/-- Quadratic conservation remains a noncommutative operator identity. -/
theorem ofStage_quadratic_commutes (n : ℕ) (u v : Stage n)
    (hu : u * u = 0) (hv : v * v = 0) :
    (ofStage n u * ofStage n v + ofStage n v * ofStage n u) *
        (ofStage n u + ofStage n v) =
      (ofStage n u + ofStage n v) *
        (ofStage n u * ofStage n v + ofStage n v * ofStage n u) := by
  have hu' : ofStage n u * ofStage n u = 0 := limit_square_zero hu
  have hv' : ofStage n v * ofStage n v = 0 := limit_square_zero hv
  rw [mul_add,
    InfoGeometry.Algebra.PeirceQuadraticCycle.quadratic_commutes_left hu',
    InfoGeometry.Algebra.PeirceQuadraticCycle.quadratic_commutes_right hv',
    ← add_mul]

end InfoGeometry.Canonical.LieJordanBoundaryColimit
