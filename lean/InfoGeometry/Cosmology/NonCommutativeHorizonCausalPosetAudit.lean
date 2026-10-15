/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Cosmology.NonCommutativeHorizonCausalPoset

/-!
# Axiomatic Audit of Non-Commutative Horizon Causal Poset

This module audits `InfoGeometry.Cosmology.NonCommutativeHorizonCausalPoset`:
1. `audit_gns_left_ideal`: Left ideal property of `gnsRadical`.
2. `audit_gns_right_ideal_tracial`: Two-sided ideal property under traciality.
3. `audit_krein_isometry`: Krein isometry $B(\theta)^\dagger B(\theta) = 1$.
4. `audit_null_cone_invariance`: Exact invariance of the Krein null cone.
-/

namespace InfoGeometry.Cosmology.NonCommutativeHorizon.Audit

open Archetype_II_GNS_Radical
open Archetype_III_Tracial_Modular
open Archetype_IV_Krein_Metric
open Archetype_V_Bogoliubov_Rindler
open Matrix

variable {R : Type*} [CommRing R] [StarRing R]
variable {A : Type*} [Ring A] [StarRing A] [Algebra R A] [StarModule R A]

theorem audit_gns_left_ideal (φ : A →ₗ[R] R) (a : A) (x : A) (hx : x ∈ gnsRadical φ) :
    a * x ∈ gnsRadical φ :=
  gnsRadical_is_left_ideal φ a x hx

theorem audit_gns_right_ideal_tracial (φ : A →ₗ[R] R) (hTr : IsTracial φ)
    (a : A) (x : A) (hx : x ∈ gnsRadical φ) :
    x * a ∈ gnsRadical φ :=
  gnsRadical_is_right_ideal_of_tracial φ hTr a x hx

theorem audit_krein_isometry (θ : ℝ) :
    kreinAdjoint (bogoliubovTransform θ) * bogoliubovTransform θ = 1 :=
  bogoliubov_is_krein_isometry θ

theorem audit_null_cone_invariance (θ : ℝ) (v : Fin 2 → ℝ) (hv : IsKreinNull v) :
    IsKreinNull (bogoliubovTransform θ *ᵥ v) :=
  bogoliubov_preserves_null_cone θ v hv

#print axioms audit_gns_left_ideal
#print axioms audit_gns_right_ideal_tracial
#print axioms audit_krein_isometry
#print axioms audit_null_cone_invariance

end InfoGeometry.Cosmology.NonCommutativeHorizon.Audit
