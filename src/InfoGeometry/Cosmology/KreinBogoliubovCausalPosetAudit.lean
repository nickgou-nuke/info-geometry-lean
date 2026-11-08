/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Cosmology.KreinBogoliubovCausalPoset

/-!
# Axiomatic Audit of Krein Space Doubling and Bogoliubov Causal Poset

This module audits `InfoGeometry.Cosmology.KreinBogoliubov`:
1. `audit_gns_left_ideal`: Confirms unconditional left ideal property of GNS radical.
2. `audit_gns_right_ideal_tracial`: Confirms two-sided ideal property under traciality.
3. `audit_krein_metric_sq`: Confirms $\eta^2 = 1$.
4. `audit_krein_isometry`: Confirms $B(\theta)^\dagger B(\theta) = 1$.
5. `audit_null_cone_invariance`: Confirms preservation of the Krein null cone.
-/

namespace InfoGeometry.Cosmology.KreinBogoliubov.Audit

open InfoGeometry.Cosmology.KreinBogoliubov

variable {A : Type*} [Ring A] [StarRing A]

theorem audit_gns_left_ideal (phi : A → A) (a x : A) (hx : x ∈ GNSRadical phi) :
    a * x ∈ GNSRadical phi :=
  gnsRadical_is_left_ideal phi a x hx

theorem audit_gns_right_ideal_tracial (phi : A → A) (hTr : IsTracial phi)
    (a x : A) (hx : x ∈ GNSRadical phi) :
    x * a ∈ GNSRadical phi :=
  gnsRadical_is_right_ideal_of_tracial phi hTr a x hx

theorem audit_krein_metric_sq : kreinMetric * kreinMetric = 1 :=
  kreinMetric_sq

theorem audit_krein_isometry (θ : ℝ) :
    kreinAdjoint (bogoliubovTransform θ) * bogoliubovTransform θ = 1 :=
  bogoliubov_is_krein_isometry θ

theorem audit_null_cone_invariance (θ : ℝ) (v : Fin 2 → ℝ) :
    IsKreinNull (boostVec θ v) ↔ IsKreinNull v :=
  bogoliubov_preserves_null_cone θ v

#print axioms audit_gns_left_ideal
#print axioms audit_gns_right_ideal_tracial
#print axioms audit_krein_metric_sq
#print axioms audit_krein_isometry
#print axioms audit_null_cone_invariance

end InfoGeometry.Cosmology.KreinBogoliubov.Audit
