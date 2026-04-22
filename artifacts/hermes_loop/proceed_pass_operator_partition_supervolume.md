# Proceed pass: operatorial partition -> supervolume bridge

This pass turned the previously red operatorial partition/supervolume bridge into
an actual theorem surface.

## New file
- `lean/InfoGeometry/Canonical/OperatorPartitionSupervolumeBridge.lean`

## New theorem
- `ConformalGibbsSouriauOperatorContext.operatorMassieu_eq_log_generalizedBerezinianScale_of_operatorPartition_eq_generalizedBerezinianScale`

## Meaning
This is the smallest truthful exact bridge currently available between:
- the operatorial Souriau/Weyl partition lane, and
- the generalized Berezinian super-volume lane.

It does NOT claim that the partition is definitionally a Berezinian.
Instead it says:
- if the caller supplies an explicit witness
  `C.operatorPartition = generalizedBerezinianScale S`,
- then the operatorial Massieu potential is exactly
  `log (generalizedBerezinianScale S)`.

So one explicit hypothesis package has been converted into a theorem-backed
bridge surface, without fabricating the stronger identity that is still not
owned.

## Verification
- `lake env lean lean/InfoGeometry/Canonical/OperatorPartitionSupervolumeBridge.lean` ✅
- `lake build InfoGeometry.Canonical.OperatorPartitionSupervolumeBridge` ✅
- manual harness:
  - `tests/test_operatorial_partition_supervolume_bridge_owner_theorem.py` ✅
  - `tests/test_weighted_weyl_equilibrium_bridge_theorems.py` ✅

## Graph / Alexandria context used
- SCC-first Arango audit already established that weak basin overlap is not proof
  of a theorem route in the Souriau/RN corridor.
- Alexandria fetch + semantic ingest + graph ranking were run locally over the
  arXiv seed corpus; live Alexandria-Arango ingest remained unavailable because
  the second Arango instance on `127.0.0.1:8530` was down.
- The present theorem was therefore chosen by raw-source descent, not by
  semantic overreach.

## Remaining open debt
Still not owned:
- `operatorPartition = generalizedBerezinianScale ...` as a theorem generated
  from existing operatorial structure alone
- stronger boson/fermion signed supertrace character decomposition theorems
- full Souriau partition = Weyl character theorem surface

So the next honest target is the witness-producing theorem, not a rhetorical
claim that the identity already holds unconditionally.
