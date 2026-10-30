/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SpinorialCore.KreinAdjoint

/-! Kernel audit for the distinction between indefinite-form preservation and
ordinary orthogonality, and for the unitary commutant criterion. -/

open InfoGeometry.Canonical.SpinorialCore.Krein
open InfoGeometry.Canonical.SpinorialCore.Krein.Counterexample

#print axioms isometry_defect_decomposition
#print axioms isIsometry_iff_commute_of_unitary
#print axioms signature_boost_noncommute
#print axioms boost_preserves_signature
#print axioms boost_not_orthogonal
