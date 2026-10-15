/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Epistemology.ChentsovMetricInvariance

/-!
# Audit Companion: Chentsov Metric Invariance

This module audits the foundational axioms and kernel dependency manifest
of `InfoGeometry.Epistemology.ChentsovMetricInvariance`.
-/

open InfoGeometry.Epistemology.ChentsovMetricInvariance

#print axioms fisherMetric_symm
#print axioms fisherMetric_nonneg
#print axioms fisherMetric_eq_score_expectation
#print axioms pushforwardTangent_sum_zero
#print axioms congruent_kernel_zero_of_ne
#print axioms congruent_pushforward_at
#print axioms congruent_pushforward_tangent_at
#print axioms chentsov_congruent_metric_invariance
#print axioms chentsov_congruent_pushforward_fisher_isometry
#print axioms injectiveCongruentKernel
