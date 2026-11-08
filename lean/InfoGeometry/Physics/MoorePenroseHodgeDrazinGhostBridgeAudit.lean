/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Physics.MoorePenroseHodgeDrazinGhostBridge

/-!
# Axiom audit: `MoorePenroseHodgeDrazinGhostBridge`

This audit originally listed thirteen `#print axioms` targets.  The
regular/harmonic block is now **implemented** in the owner module and audited
below:

`regular_add_harmonic_id`, `regular_projector_idempotent`,
`harmonic_projector_idempotent`, `harmonic_projector_in_kernel`,
`regular_sector_exact_inversion`, `moore_penrose_is_drazin_index_one`,
`drazin_annihilates_null`, and the capstone
`certified_mp_hodge_drazin_ghost_synthesis`.

`moore_penrose_is_drazin_index_one` is proved under the EP hypothesis
`A * A_plus = A_plus * A`.  The unconditional statement is false: for the
nilpotent shift `A = !![0, 1; 0, 0]` the Moore--Penrose laws hold while
`A * A * A† = 0 ≠ A`.

## Frontier (declared, not implemented)

The remaining claims need Hodge/BRST carriers that this module does not
provide.  They stay recorded here so the debt remains greppable, and they are
deliberately *not* introduced as `axiom`, `sorry`, or `: True` theorem
surfaces, because auditing a declaration that does not exist asserts a
falsehood in machine-checkable form.

- `hodge_diffusion_dissipation` — dissipativity of Hodge diffusion.
- `brst_squared_annihilation` — square-zero BRST charge.
- `brst_exact_is_closed` — exactness of the BRST differential.
- `brst_ghost_charge_collapse` — collapse of the ghost charge.
- `brst_physical_ghost_decoupling` — decoupling of physical and ghost modes.

## Audit of the declarations that actually exist

Besides the sector block, the owner proves the exact equivalence
`ghost_commutator_eq_zero_iff`, reducing vanishing of the defect commutator to
commutation of the Moore--Penrose candidate under the Drazin commutation law.
-/

open InfoGeometry.Physics.MoorePenroseHodgeDrazinGhostBridge

#print axioms IsMoorePenrose
#print axioms IsDrazinIndexOne
#print axioms defect_ghost
#print axioms zero_ghost_implies_metric_commutation
#print axioms operator_ghost_commutator
#print axioms ghost_commutator_eq_zero_iff

#print axioms regularProjector
#print axioms harmonicProjector
#print axioms regularPart
#print axioms harmonicPart
#print axioms toIsMoorePenroseInverse
#print axioms toIsDrazinInverse
#print axioms regular_add_harmonic_id
#print axioms regularPart_add_harmonicPart
#print axioms regular_projector_idempotent
#print axioms harmonic_projector_idempotent
#print axioms harmonic_projector_in_kernel
#print axioms drazin_annihilates_null
#print axioms regular_sector_exact_inversion
#print axioms moore_penrose_is_drazin_index_one
#print axioms CertifiedMPHodgeDrazinGhostSynthesis
#print axioms certified_mp_hodge_drazin_ghost_synthesis
