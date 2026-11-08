/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Cosmology.SpacetimeParabolicQuotient

/-!
# Axiomatic Audit of the Finite Matrix Lemmas

This module performs the official axiomatic and non-vacuity audit of
`InfoGeometry.Cosmology.SpacetimeParabolicQuotient`.
It checks the inverse, finite vacuum quotient, native finite-dimensional
`SL₂`-coset equivalence, soldering-root annihilation, ray-stabilizer, and
normalized-projector theorems in the owner file. The coset equivalence is for
the projectivization of the explicit real matrix quotient; it does not identify
that quotient with the repository's faithful completed filtered GNS space.
-/

namespace InfoGeometry.Cosmology.SpacetimeParabolicQuotient.Audit

open InfoGeometry.Cosmology.SpacetimeParabolicQuotient
open Matrix

theorem audit_sl2_two_sided_inv (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : IsSL2 g) :
    sl2Inv g * g = 1 ∧ g * sl2Inv g = 1 :=
  ⟨sl2Inv_mul_eq_one g hg, mul_sl2Inv_eq_one g hg⟩

theorem audit_inGNSNull_annihilator (A : Matrix (Fin 2) (Fin 2) ℝ) :
    InGNSNull A ↔ mulVec A cyclicVacuum = 0 :=
  inGNSNull_iff_mulVec_vacuum A

theorem audit_finite_quotient_to_spinor_equiv :
    Nonempty ((Matrix (Fin 2) (Fin 2) ℝ ⧸ LinearMap.ker vacuumColumnMap) ≃ₗ[ℝ]
      (Fin 2 → ℝ)) :=
  ⟨vacuumNullQuotientEquiv⟩

theorem audit_finite_quotient_left_action (A X : Matrix (Fin 2) (Fin 2) ℝ) :
    vacuumNullQuotientEquiv (Submodule.Quotient.mk (A * X)) =
      mulVec A (vacuumNullQuotientEquiv (Submodule.Quotient.mk X)) :=
  vacuumNullQuotient_left_action_intertwining A X

theorem audit_parabolic_coset_to_projective_quotient :
    Nonempty ((RealSL2 ⧸ vacuumRayStabilizer) ≃ VacuumNullProjectiveLine) :=
  ⟨vacuumRayCosetEquivProjectiveNullQuotient⟩

theorem audit_soldering_root_class_zero :
    (Submodule.Quotient.mk
      InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootPlus :
        Matrix (Fin 2) (Fin 2) ℝ ⧸ LinearMap.ker vacuumColumnMap) = 0 :=
  solderingRootPlus_class_eq_zero

theorem audit_opposite_soldering_root_survives :
    (Submodule.Quotient.mk
      InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootMinus :
        Matrix (Fin 2) (Fin 2) ℝ ⧸ LinearMap.ker vacuumColumnMap) ≠ 0 :=
  solderingRootMinus_class_ne_zero

theorem audit_soldering_null_roots_have_distinct_vacuum_classes :
    InfoGeometry.Clifford.Soldering.q22
        InfoGeometry.Clifford.SolderingIsomorphism.vecRootPlus = 0 ∧
      InfoGeometry.Clifford.Soldering.q22
        InfoGeometry.Clifford.SolderingIsomorphism.vecRootMinus = 0 ∧
      (Submodule.Quotient.mk
        InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootPlus :
          Matrix (Fin 2) (Fin 2) ℝ ⧸ LinearMap.ker vacuumColumnMap) = 0 ∧
      (Submodule.Quotient.mk
        InfoGeometry.Projective.SplitQuaternionRankOneProjective.rootMinus :
          Matrix (Fin 2) (Fin 2) ℝ ⧸ LinearMap.ker vacuumColumnMap) ≠ 0 :=
  soldering_null_roots_have_distinct_vacuum_classes

theorem audit_parabolic_stabilizer (g : Matrix (Fin 2) (Fin 2) ℝ) :
    StabilizesVacuumRay g ↔ IsSL2 g ∧ IsParabolicUpper g :=
  stabilizesVacuumRay_iff_parabolic g

theorem audit_vacuum_expectation_bounded (u : Fin 2 → ℝ)
    (h : (u 0)^2 + (u 1)^2 = 1) :
    |vacuumState (projector u)| ≤ 1 :=
  vacuumState_projector_bound u h

theorem audit_projector_norm (u : Fin 2 → ℝ)
    (h : (u 0)^2 + (u 1)^2 = 1) :
    frobNormSq (projector u) = 1 :=
  projector_frobNormSq u h

theorem audit_commutator_bound (u : Fin 2 → ℝ)
    (h : (u 0)^2 + (u 1)^2 = 1) :
    frobNormSq (commutator boostGenerator (projector u)) ≤ 1 / 2 :=
  commutator_boost_projector_bound u h

#print axioms audit_sl2_two_sided_inv
#print axioms audit_inGNSNull_annihilator
#print axioms audit_finite_quotient_to_spinor_equiv
#print axioms audit_finite_quotient_left_action
#print axioms audit_parabolic_coset_to_projective_quotient
#print axioms audit_soldering_root_class_zero
#print axioms audit_opposite_soldering_root_survives
#print axioms audit_soldering_null_roots_have_distinct_vacuum_classes
#print axioms audit_parabolic_stabilizer
#print axioms audit_vacuum_expectation_bounded
#print axioms audit_projector_norm
#print axioms audit_commutator_bound

end InfoGeometry.Cosmology.SpacetimeParabolicQuotient.Audit
