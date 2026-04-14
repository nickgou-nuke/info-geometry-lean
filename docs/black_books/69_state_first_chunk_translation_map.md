# 69. State-First Chunk Translation Map (Owner-Surface Index)

*Date: April 14, 2026*  
*Context: Chunked translation of type-III state-first doctrine into canonical Lean surfaces*

## Rule

This chapter records theorem/file mappings only.
No narrative claims beyond compiled owner surfaces.

## Chunk 1

- File: `lean/InfoGeometry/Canonical/OperatorialCramerRaoStateFirstChunk1.lean`
- Theorem:
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk1.stateFirst_modularSplit_singularClosure_operatorialCramerRao`

## Chunk 2

- File: `lean/InfoGeometry/Canonical/OperatorialCramerRaoStateFirstChunk2.lean`
- Theorems:
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2.StateFirstCommutationInterface`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2.stateFirstCommutationInterface_of_wedgeCalibrated`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2.modularSplit_and_supercharge_of_commutationInterface`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2.modularSplit_degenerates_to_active_of_apex_zero`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2.stateFirst_apexZero_activeOnly_operatorialCramerRao`

## Chunk 3

- File: `lean/InfoGeometry/Canonical/OperatorialCramerRaoStateFirstChunk3.lean`
- Theorems/defs:
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3.FierzAdmissibleState`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3.fierzAdmissibleState_true`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3.StateFirstAdmissibleOperator`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3.projectorCompressed`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3.stateFirstAdmissibleOperator_of_wedgeCalibrated`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3.stateFirstAdmissibleOperator_modularFlow_state_stable`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3.stateFirstAdmissibleOperator_projectorCompressed_stable`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3.stateFirst_admissibleGate_transport_and_operatorialCramerRao`

## Chunk 4

- File: `lean/InfoGeometry/Canonical/OperatorialCramerRaoStateFirstChunk4.lean`
- Theorems/defs:
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4.MeasurableOperator`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4.measurableOperator_projectorCompressed_stable`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4.measurableOperator_modularFlow_state_stable`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4.measurableOperator_uncertainty_bridge`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4.stateFirst_measurable_uncertainty_operatorialCramerRao_package`

## Semantic Audit Surface

- File: `lean/InfoGeometry/Canonical/OperatorialCramerRaoStateFirstSemanticAudit.lean`
- Axiom print checks:
  - `Chunk1.stateFirst_modularSplit_singularClosure_operatorialCramerRao`
  - `Chunk2.stateFirst_apexZero_activeOnly_operatorialCramerRao`
  - `Chunk3.stateFirst_admissibleGate_transport_and_operatorialCramerRao`
  - `Chunk4.stateFirst_measurable_uncertainty_operatorialCramerRao_package`
- Audit theorems:
  - `chunk2_active_only_reduction_audit`
  - `chunk3_admissibility_package_audit`
  - `chunk4_measurable_uncertainty_package_audit`

## CI Build Lane

- Script: `tools/infra/build_state_first_lane.py`
- Targets:
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk1`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4`
  - `InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit`
