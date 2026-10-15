/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.DrazinSpectralKernel

/-!
# Audit: Drazin Generalized Inverse & Nilpotent Spectral Kernel

Independent audit verifying that:
1. All theorems bridging the Drazin axioms, spectral projector, kernel projector,
   Fitting decomposition, and group inverse Markov kernel compile cleanly.
2. Every theorem depends strictly on standard Core Lean 4 / Mathlib axioms:
   `[propext, Classical.choice, Quot.sound]`.
3. Zero `sorry`, zero `admit`, and zero custom axioms are introduced.
-/

namespace InfoGeometry.QuantumContext.DrazinAudit

open InfoGeometry.QuantumContext.Drazin

/- Verification 1: Check axioms of spectral projector properties. -/
#print axioms spectralProj_comm
#print axioms spectralProj_idempotent
#print axioms kernelProj_idempotent
#print axioms spectral_add_kernel
#print axioms spectral_mul_kernel

/- Verification 2: Check axioms of kernel annihilation. -/
#print axioms index_annihilates_kernel_proj

/- Verification 3: Check axioms of group inverse Markov specialization and model witness. -/
#print axioms group_inverse_nilpotent_zero
#print axioms group_inverse_reconstruction
#print axioms isDrazinInverse_one

end InfoGeometry.QuantumContext.DrazinAudit


