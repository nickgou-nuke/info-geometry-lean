/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Canonical.SuperGrassmannianManifold

/-!
# Audit Companion: Super-Grassmannian Manifold

This module audits the foundational axioms and kernel dependency manifest
of `InfoGeometry.Canonical.SuperGrassmannianManifold`.
-/

open InfoGeometry.Canonical.SuperGrassmannianManifold

#print axioms metric_anti_invariance
#print axioms tplus_isotropic_two_mul
#print axioms tminus_isotropic_two_mul
#print axioms orthoComplement_idempotent
#print axioms projector_ortho_annihilation
#print axioms ortho_projector_annihilation
#print axioms compile_super_grassmannian_manifold
