import InfoGeometry.Physics.MoorePenroseHodgeDrazinGhostBridge

/-!
# Axiom audit: `MoorePenroseHodgeDrazinGhostBridge`

This audit previously listed thirteen `#print axioms` targets
(`regular_add_harmonic_id`, `regular_projector_idempotent`,
`harmonic_projector_idempotent`, `harmonic_projector_in_kernel`,
`regular_sector_exact_inversion`, `hodge_diffusion_dissipation`,
`brst_squared_annihilation`, `brst_exact_is_closed`,
`brst_ghost_charge_collapse`, `brst_physical_ghost_decoupling`,
`moore_penrose_is_drazin_index_one`, `drazin_annihilates_null`,
`certified_mp_hodge_drazin_ghost_synthesis`).

None of those thirteen declarations exist. The owner module
`InfoGeometry.Physics.MoorePenroseHodgeDrazinGhostBridge` contains only the
five declarations audited below, and the file previously failed to compile with
thirteen `Unknown constant` errors, which broke the whole `InfoGeometry.All`
surface.

## Frontier (declared, not implemented)

The following claims are **unimplemented**. They are recorded here so the debt
stays greppable and visible. They are deliberately *not* introduced as `axiom`,
`sorry`, or `: True` theorem surfaces, and they are *not* audited, because
auditing a declaration that does not exist asserts a falsehood in
machine-checkable form. Each one needs real mathematics before it can be
written down.

- `regular_add_harmonic_id` — regular plus harmonic decomposition identity.
- `regular_projector_idempotent` — idempotence of the regular projector.
- `harmonic_projector_idempotent` — idempotence of the harmonic projector.
- `harmonic_projector_in_kernel` — the harmonic projector lands in the kernel.
- `regular_sector_exact_inversion` — exact inversion on the regular sector.
- `hodge_diffusion_dissipation` — dissipativity of Hodge diffusion.
- `brst_squared_annihilation` — square-zero BRST charge.
- `brst_exact_is_closed` — exactness of the BRST differential.
- `brst_ghost_charge_collapse` — collapse of the ghost charge.
- `brst_physical_ghost_decoupling` — decoupling of physical and ghost modes.
- `moore_penrose_is_drazin_index_one` — Moore-Penrose inverse has Drazin
  index one.
- `drazin_annihilates_null` — the Drazin inverse annihilates the null space.
- `certified_mp_hodge_drazin_ghost_synthesis` — the intended capstone synthesis.

## Audit of the declarations that actually exist
-/

open InfoGeometry.Physics.MoorePenroseHodgeDrazinGhostBridge

#print axioms IsMoorePenrose
#print axioms IsDrazinIndexOne
#print axioms defect_ghost
#print axioms zero_ghost_implies_metric_commutation
#print axioms operator_ghost_commutator
