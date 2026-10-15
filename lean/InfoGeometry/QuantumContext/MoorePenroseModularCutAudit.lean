/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MoorePenroseModularCut

/-!
# Audit: Moore–Penrose Modular Cut & Regularized Araki Modular Theory

Independent audit verifying that:
1. All theorems bridging the Moore–Penrose pseudoinverse, support projector,
   eviction projector, GNS left ideal annihilation, regularized KMS commutation,
   and attention sink anchor compile cleanly.
2. The Master Certificate `compile_moore_penrose_modular_cut` is instantiated.
3. Every theorem depends strictly on standard Core Lean 4 / Mathlib axioms:
   `[propext, Classical.choice, Quot.sound]`.
4. Zero `sorry`, zero `admit`, and zero custom axioms are introduced.
-/

namespace InfoGeometry.QuantumContext.MoorePenroseAudit

open InfoGeometry.QuantumContext.MoorePenrose

/-- Verification 1: Master Certificate compilation. -/
theorem test_certificate_compiles (n : ℕ) :
    MoorePenroseModularCutCertificate n :=
  compile_moore_penrose_modular_cut n

/- Verification 2: Check axioms of master compilation constructor. -/
#print axioms compile_moore_penrose_modular_cut

/- Verification 3: Check axioms of Penrose identities. -/
#print axioms penrose_one
#print axioms penrose_two
#print axioms mul_pinv_eq_support
#print axioms pinv_mul_eq_support

/- Verification 4: Check axioms of projector idempotency and orthogonality. -/
#print axioms support_idempotent
#print axioms eviction_idempotent
#print axioms support_add_eviction
#print axioms support_mul_eviction

/- Verification 5: Check axioms of left ideal annihilation. -/
#print axioms pinv_annihilates_eviction
#print axioms eviction_annihilates_density

/- Verification 6: Check axioms of regularized KMS commutation and attention sink. -/
#print axioms regularized_kms_on_support
#print axioms active_support_anchor

end InfoGeometry.QuantumContext.MoorePenroseAudit
