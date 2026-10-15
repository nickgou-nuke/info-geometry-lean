/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.HodgeGeometricCalculus

/-!
# Audit Companion: Hodge Duality, Interior Contraction, and Geometric Calculus

This module audits the foundational axioms and kernel dependency manifest
of `InfoGeometry.Algebra.HodgeGeometricCalculus`.
-/

open InfoGeometry.Algebra.HodgeGeometricCalculus

#print axioms hodge_sq_vector_2d
#print axioms hodge_sq_scalar_2d
#print axioms hodge_sq_bivector_2d
#print axioms laplacian_commutes_d
#print axioms laplacian_commutes_delta
#print axioms harmonic_annihilated_by_laplacian
#print axioms compile_hodge_geometric_calculus
