/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.DiscreteHodgeDiracKrein

/-!
# Audit: Discrete Hodge–Dirac–Krein Chiral Operator

Independent audit verifying that:
1. All theorems bridging the discrete Hodge–Dirac operator, Laplacian squaring,
   chiral grading, Krein fundamental symmetry, and Krein-Dirac intertwining compile cleanly.
2. The Master Certificate `compile_discrete_hodge_dirac_krein` is instantiated.
3. Every theorem depends strictly on standard Core Lean 4 / Mathlib axioms:
   `[propext, Classical.choice, Quot.sound]`.
4. Zero `sorry`, zero `admit`, and zero custom axioms are introduced.
-/

namespace InfoGeometry.QuantumContext.DiscreteHodgeDiracAudit

open InfoGeometry.QuantumContext.DiscreteHodgeDirac

/-- Verification 1: Master Certificate compilation. -/
theorem test_certificate_compiles (R : Type*) [CommRing R] :
    DiscreteHodgeDiracKreinCertificate R :=
  compile_discrete_hodge_dirac_krein R

/- Verification 2: Check axioms of master compilation constructor. -/
#print axioms compile_discrete_hodge_dirac_krein

/- Verification 3: Check axioms of Hodge Laplacian generation. -/
#print axioms dirac_sq_eq_laplacian

/- Verification 4: Check axioms of chiral grading and anticommutation. -/
#print axioms chiralGamma_sq
#print axioms dirac_anticomm_chiral

/- Verification 5: Check axioms of Krein fundamental symmetry and almost-complex structure. -/
#print axioms kreinJ_sq
#print axioms kreinJ_anticomm_chiral
#print axioms dirac_anticomm_kreinJ_symmetric

/- Verification 6: Check axioms of Krein-Chiral Dirac intertwining. -/
#print axioms kreinDirac_explicit

end InfoGeometry.QuantumContext.DiscreteHodgeDiracAudit
