/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus

/-!
# Axiom audit for Peirce corner conjugation calculus

## i. Overview

This file asks Lean to report the transitive axiom dependencies of the finite
ring lemmas in the elementary-expansion operator-calculus owner.

## ii. Key results

- Kernel reports for the shear inverse, base-corner expansion, diagonal correction,
  and conditional commutator identity.

## iii. Table of contents

1. Transitive axiom reports for the selected declarations.

## iv. References

- `InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus`
-/

#print axioms InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugator_mul_inverse
#print axioms InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation_base_expansion
#print axioms InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation_even_shift
#print axioms InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation_even_shift_commutator_correction
#print axioms InfoGeometry.Canonical.GrothendieckElementaryExpansionOperatorCalculus.cornerConjugation_even_shift_eq_commutator
