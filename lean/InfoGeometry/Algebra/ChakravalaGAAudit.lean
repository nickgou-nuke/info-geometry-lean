/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.ChakravalaGA

/-!
# Audit Companion: Grassmann-Clifford Differential Algebras (chakravala Archetypes)

This module audits the foundational axioms and kernel dependency manifest
of `InfoGeometry.Algebra.ChakravalaGA`.
-/

open ChakravalaGA

#print axioms koszulSign_symm
#print axioms koszulSign_add_left
#print axioms superBracket_fermionic
#print axioms superBracket_bosonic
#print axioms superBracket_skew
#print axioms clifford_anticommutator
#print axioms clifford_orthogonal_swap
#print axioms grassmann_anticomm
#print axioms grassmann_nilpotent
#print axioms mathlib_exteriorAlgebra_anticomm
#print axioms mathlib_exteriorAlgebra_swap
#print axioms mathlib_exteriorAlgebra_nilpotent
#print axioms mathlib_exteriorAlgebra_superBracket_zero
#print axioms geometric_bivector_sq_neg_one
