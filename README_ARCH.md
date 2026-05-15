# Architecture Roadmap: Type III Standard-Form and Hestenes-Krein Readouts

This document records the proof pipeline, dependency hygiene rules, and audit
invariants for the theorem-safe Type III lane in this repository.

The purpose of the stack is not to construct Tomita-Takesaki theory, a
von Neumann algebra standard form, a Type III determinant, or a trace.  The
purpose is to isolate socket interfaces and conditional readbacks that connect:

```text
Drazin/Hodge causal splitting
  -> bounded supercharge energy
  -> Souriau modular normalization
  -> bounded modular thermal/rotor boundary certificates
  -> standard-form cone-vector expectation
  -> Hestenes-Krein real readout
  -> Cantor/Wigner-Jones cylinder weights
  -> Weyl/GW projective volume readouts
```

## 1. Core doctrine

### 1.1 No primitive trace in the Type III lane

Do not write Type III sector size as:

```text
Tr(p_w)
```

The accepted replacement is a supplied standard-form vector readout:

```text
omega(A) = <A xi_omega, xi_omega>
```

or, in the Hestenes-Krein real lane:

```text
phi_Omega(A) = [A Omega, Omega]_J
```

where the Krein pairing is repository-owned as:

```lean
KreinSpace.kreinInner
```

### 1.2 No automatic determinant in the Type III lane

Do not use an unrestricted determinant or a ring homomorphism
`Op ->+* R` as a Type III phase-volume primitive.

Determinant-like or phase-volume readouts must be supplied as calibrated
channels, and invariance must be a witness/readback.  The canonical infinite
Type III replacements are modular weights, Connes cocycles, spatial
derivatives, and Araki relative entropy.

### 1.3 Natural cone is not the Krein causal cone

The set:

```text
{xi | [xi, xi]_J >= 0}
```

is a Krein causal/nonnegative cone.  It is not automatically the
Haagerup-Araki standard-form natural positive cone.

The standard-form natural cone is carried by explicit sockets:

```text
M_*^+ <-> P
omega(A) = <A xi_omega, xi_omega>
J xi = xi for xi in P
P = P^vee
```

Self-duality, cyclicity, separatingness, and uniqueness are witness data unless
a concrete analytic backend supplies the theorem.

### 1.4 KMS is translated to Hestenes-Krein rotor periodicity

In the Hestenes-Krein lane, the complex analytic language of KMS is not used as
the primitive formulation.  The thermal boundary condition is represented by
supplied real rotor/phase periodicity and Hestenes geometric analyticity.

Analyticity in this real lane means compatibility with the phase rotor/axis:
operators and flows must preserve the Hestenes phase structure, expressed by
commutation or calibrated covariance with the rotor/phase-axis action.

Audit rule: do not claim a complex strip theorem here.  The Hestenes-Krein
formulation carries a real periodicity/rotor boundary socket.  Any comparison
back to the usual complex KMS strip condition must be a separate calibration
theorem or certificate.

### 1.5 Krein null-cone preservation requires a Krein-isometry witness

A vector flow preserves the Krein null cone only under an explicit
Krein-isometry law:

```lean
KreinSpace.IsKreinIsometry
```

This is not derivable from the word "modular" or from `K^2 = -1`.

## 2. Standard-form lock

Module:

```lean
InfoGeometry.Canonical.StandardFormNaturalConeBridge
```

This module is the canonical lock for trace-to-expectation replacement.  It is
a socket plus conditional readback layer, not a full Type III theorem.

### 2.1 Cone-vector expectation socket

Primary carrier:

```lean
NaturalConeStandardFormInterface
```

It supplies:

```lean
act
J
cone
isNormalPositive
coneVector
eval
innerReadout
coneVector_mem
eval_eq_vector_readout
J_fixes_cone
cone_self_dual
cone_self_dual_holds
```

Main readbacks:

```lean
NaturalConeStandardFormInterface.coneVector_mem_of_normal
NaturalConeStandardFormInterface.eval_eq_vector_readout_of_normal
NaturalConeStandardFormInterface.J_fixes_coneVector
NaturalConeStandardFormInterface.cone_self_dual_readback
```

Meaning:

```text
given omega in M_*^+,
xi_omega := coneVector omega,
eval omega A = innerReadout (A xi_omega) xi_omega.
```

### 2.2 Cantor/cylinder face socket

Primary carrier:

```lean
NaturalConeCantorFaceSystem
```

It supplies:

```lean
standard
cylinderProjection
face
face_law
face_law_holds
cylinderWeight
cylinderWeight_pos
```

Main readbacks:

```lean
NaturalConeCantorFaceSystem.face_law_readback
NaturalConeCantorFaceSystem.cylinderPotential
NaturalConeCantorFaceSystem.branchIncrement
NaturalConeCantorFaceSystem.cylinderPotential_child
```

The logarithmic potential and branch increment are delegated to:

```lean
InfoGeometry.Canonical.TypeIIIModularCantorSystem
```

This avoids reimplementing:

```text
-log(weight w)
-log(weight (child w b) / weight w)
```

### 2.3 Conditional finite-level expectation partition

Predicate:

```lean
IsFinitePartitionOfUnity
```

Predicate:

```lean
EvalPreservesFiniteIndexedSums
```

Theorem:

```lean
expectation_sum_eq_total_of_partition
```

Meaning:

```text
if sum_w p_w = 1
and eval preserves finite BinaryWord-indexed sums,
then sum_w omega(p_w) = omega(1).
```

This is the theorem-safe replacement for:

```text
sum_{|w|=n} <Omega, p_w Omega> = 1
```

It requires an explicit partition witness and either normalization or a total
expectation target.  No trace, determinant, or density matrix is used.

### 2.4 Finite-level witness carrier

Primary carrier:

```lean
FiniteCylinderExpectationPartition
```

It supplies:

```lean
faces
one
levelWords
omega
omega_mem
level_partition_law
level_partition_law_holds
expectation_partition_law
```

Main readbacks:

```lean
FiniteCylinderExpectationPartition.omega_isNormalPositive
FiniteCylinderExpectationPartition.level_expectation_sum_eq_total
FiniteCylinderExpectationPartition.level_partition_holds
FiniteCylinderExpectationPartition.level_expectation_sum_eq_one
FiniteCylinderExpectationPartition.cylinderExpectation_eq_vector_readout
FiniteCylinderExpectationPartition.totalExpectation_eq_vector_readout
```

Use this carrier when the concrete backend already supplies the expectation
partition law.

### 2.5 Modular localizer socket

Primary carrier:

```lean
ModularNaturalConeFaceBridge
```

It supplies cylinder projectors and their modular mirrors as preservation
witnesses.

Localizer:

```text
L_w = p_w * J p_w J
```

Lean name:

```lean
ModularNaturalConeFaceBridge.localizationOp
```

Main readbacks:

```lean
ModularNaturalConeFaceBridge.localizationOp_mem_naturalCone
ModularNaturalConeFaceBridge.modularConeFace
ModularNaturalConeFaceBridge.mem_modularConeFace_iff
ModularNaturalConeFaceBridge.modularConeFace_subset_naturalCone
ModularNaturalConeFaceBridge.localizationOp_fixes_of_mem_modularConeFace
```

Binary-word specialization:

```lean
BinaryWordModularFaceBridge
```

## 3. Hestenes-Krein specialization

### 3.1 Real thermal/rotor boundary packet

Module:

```lean
InfoGeometry.Krein.HestenesModularKMSBridge
```

Primary carrier:

```lean
HestenesKreinKMSPacket
```

Core fields include:

```lean
phaseAxis
phase_sq
modularFlow
rotor
rotorInv
modularFlow_eq_rotor_conjugation
rotor_preserves_kreinInner
flow_is_hestenes_analytic
```

Main readbacks:

```lean
HestenesKreinKMSPacket.phaseAxis_sq
HestenesKreinKMSPacket.hestenes_flow_to_abstract_flow
HestenesKreinKMSPacket.modularFlow_eq_rotor_conjugation_theorem
HestenesKreinKMSPacket.rotor_preserves_HestenesNaturalCone
HestenesKreinKMSPacket.modular_rotor_preserves_null_cone
HestenesKreinKMSPacket.hestenes_kms_boundary
```

Audit rule: `HestenesNaturalCone` in this file is a Hestenes/Krein cone
candidate.  It is not the full standard-form natural cone unless a separate
standard-form bridge identifies it as such.

### 3.2 Vacuum readout

Module:

```lean
InfoGeometry.Krein.HestenesKreinVacuumBridge
```

Primary carrier:

```lean
HestenesKreinVacuum
```

Core readout:

```lean
HestenesKreinVacuum.vacuumRealState
```

Meaning:

```text
phi_Omega(A) = [A Omega, Omega]_J.
```

Main readbacks:

```lean
HestenesKreinVacuum.vacuumRealState_id
HestenesKreinVacuum.vacuum_rotor_fixed
HestenesKreinVacuum.vacuum_rotor_norm_invariant
HestenesKreinVacuum.vacuum_J_fixed
HestenesKreinVacuum.vacuumRealState_flow_invariant
HestenesKreinVacuum.vacuum_mem_naturalCone
HestenesKreinVacuum.vacuum_not_null
```

Audit rule: `Omega` is a distinguished state vector, not the apex of the cone.
The cone apex is `0`.  Cyclic/separating content remains a certificate.

### 3.3 Krein natural-cone adapter

Module:

```lean
InfoGeometry.Krein.HestenesKreinNaturalConeBridge
```

Primary carriers:

```lean
HestenesKreinNaturalConeBridge
HestenesKreinNaturalConeVacuum
HestenesKreinNaturalConeKMSBridge
KreinIsometricVectorFlow
```

Main readbacks:

```lean
HestenesKreinNaturalConeBridge.eval_readback
HestenesKreinNaturalConeBridge.J_fixes_coneVector
HestenesKreinNaturalConeVacuum.Omega_fixed_by_J
HestenesKreinNaturalConeKMSBridge.complexEval_eq_vacuum_readout
HestenesKreinNaturalConeKMSBridge.kms_boundary_holds
KreinIsometricVectorFlow.vectorFlow_preserves_krein_null
```

This layer keeps the natural cone explicit and separate from the Krein causal
cone.  Its KMS-named declarations are compatibility adapters to the existing
operator-thermodynamic API; the Hestenes-Krein interpretation is real
rotor/phase periodicity, not a primitive complex strip theorem.

## 4. Wigner-Jones / GW volume readouts

### 4.1 Omega volume

Module:

```lean
InfoGeometry.Canonical.StandardFormOmegaVolumeBridge
```

Primary carrier:

```lean
NaturalConeVolumeBridge
```

Main readouts:

```lean
NaturalConeVolumeBridge.wignerJonesAtom
NaturalConeVolumeBridge.atomExpectation
NaturalConeVolumeBridge.localizedExpectation
NaturalConeVolumeBridge.modularVolumePotential
NaturalConeVolumeBridge.modularVolumeIncrement
```

Main normalization readbacks:

```lean
NaturalConeVolumeBridge.total_expectation_is_unity
NaturalConeVolumeBridge.total_localizedExpectation_is_unity
```

These depend on supplied partition and normalization fields.

### 4.2 Hestenes/Jones filtration

Module:

```lean
InfoGeometry.Krein.HestenesJonesFiltrationBridge
```

Main readbacks:

```lean
HestenesJonesFiltrationBridge.volumeState_eq_vacuumRealState
HestenesJonesFiltrationBridge.atomExpectation_eq_vacuumRealState
HestenesJonesFiltrationBridge.localizedExpectation_eq_vacuumRealState
HestenesJonesFiltrationBridge.total_wignerJones_vacuumExpectation_is_unity
HestenesJonesFiltrationBridge.modularVolumePotential_eq_neg_log_vacuumRealState
HestenesJonesFiltrationBridge.modularVolumeIncrement_eq_neg_log_vacuumRealState_ratio
```

### 4.3 Hestenes/Jones to Weyl/GW adapter

Module:

```lean
InfoGeometry.Krein.HestenesJonesGWVolumeBridge
```

Main readbacks:

```lean
HestenesJonesGWVolumeBridge.physicalVolume_eq_localizedExpectation
HestenesJonesGWVolumeBridge.physicalVolume_eq_hestenesLocalizedExpectation
HestenesJonesGWVolumeBridge.physicalVolume_scale_invariant
HestenesJonesGWVolumeBridge.modularVolumePotential_eq_neg_log_vacuumRealState
HestenesJonesGWVolumeBridge.total_projective_face_volume_is_unity
```

This is the bridge where existing projective Weyl/GW physical volume is
calibrated to Hestenes-Krein vacuum expectation over localized standard-form
faces.

## 5. Projective shadow doctrine

The projective shadow doctrine is:

```text
standard-form / Type III socket data
  + projective GW or Drazin localization intensity
  + inverse Weyl gauge
  -> gauge-fixed physical readout
```

Raw projective representatives are not physical observables.  A physical
readout exists only after a Weyl/modular calibration cancels the projective
weight.

For the GW/Weyl volume lane, the intended weight-cancellation pattern is:

```text
I_GW(c · s)      = c^2  I_GW(s)
G_Weyl(c · s)    = c^-2 G_Weyl(s)
V_phys(s)        = I_GW(s) * G_Weyl(s)
V_phys(c · s)    = V_phys(s)
```

This is the same architectural pattern as the Weyl-normalized CAR/CCR lane:

```text
lambda^2 * nu = 1
lambda^2 * kappa = 1
```

and the same audit principle used for determinant-like or phase-volume
readouts:

```text
invariance is calibrated by a supplied readout channel,
not inferred from Type III structure alone.
```

Repository anchors for this doctrine include:

```lean
InfoGeometry.Canonical.WeylHomogeneousReadoutBridge
InfoGeometry.Canonical.StandardFormProjectiveGWBridge
InfoGeometry.Canonical.WeylGWVolumeBridge
InfoGeometry.Krein.HestenesJonesGWVolumeBridge
```

Audit rule: a module may define projective intensity, Weyl gauge, or physical
volume only if it states the weight law or imports a bridge that already owns
the weight law.  Do not identify a projective representative with a physical
observable without the gauge-cancellation readback.

## 6. Dependency pipeline

The bridge stack should remain acyclic:

```text
Drazin / Hodge causal split
  -> supercharge regular-support Hamiltonian
  -> Souriau modular Hamiltonian normalization
  -> bounded modular flow and thermal/rotor boundary certificates
  -> standard-form natural cone socket
  -> omega expectation / Cantor cylinder weights
  -> Hestenes-Krein real readout
  -> Weyl/GW projective volume readout
```

Do not import downstream volume or thermal/rotor boundary layers into upstream Drazin/Hodge
algebra.

## 7. Forbidden shortcuts

Treat these as architecture defects:

1. Using `[VonNeumannAlgebra M]` unless that typeclass is already repo-owned.
2. Claiming standard-form existence, natural-cone self-duality, cyclicity,
   separatingness, or uniqueness without a witness.
3. Defining `HestenesNaturalCone` as the standard-form natural cone merely from
   `[xi, xi]_J >= 0`.
4. Claiming `sum_w omega(p_w) = omega(1)` without a partition witness and
   finite-sum readout law.
5. Using `Tr(p_w)`, density matrices, or determinant homomorphisms as Type III
   primitives.
6. Claiming complex KMS strip analyticity from `K^2 = -1`.
7. Claiming Hestenes-Krein rotor periodicity without a supplied rotor/phase
   boundary witness.
8. Claiming Krein null-cone preservation without a Krein-isometry witness.
9. Reimplementing existing owner APIs such as `TypeIIIModularCantorSystem`
   cylinder potentials or `WeylHomogeneousReadoutBridge` readout laws.
10. Treating a projective representative as a physical readout before Weyl or
   modular gauge cancellation.

## 8. Targeted validation commands

Use these for the current standard-form/Hestenes/Weyl-GW lane:

```bash
lake build InfoGeometry.Canonical.StandardFormNaturalConeBridge
lake build InfoGeometry.Canonical.StandardFormOmegaVolumeBridge
lake build InfoGeometry.Canonical.StandardFormProjectiveGWBridge
lake build InfoGeometry.Krein.HestenesKreinNaturalConeBridge
lake build InfoGeometry.Krein.HestenesJonesFiltrationBridge
lake build InfoGeometry.Krein.HestenesJonesGWVolumeBridge
lake build InfoGeometry.Krein.All
```

For the broader canonical/operator-thermodynamic stack, run targeted owner
builds first:

```bash
lake build InfoGeometry.Canonical.WeylNormalizedCARCCRBridge
lake build InfoGeometry.Canonical.SuperchargeModularHamiltonianBridge
lake build InfoGeometry.Canonical.SouriauOperatorialLogPotential
lake build InfoGeometry.Canonical.StandardFormCore
lake build InfoGeometry.Canonical.TypeIIIModularCantorSystem
lake build InfoGeometry.OperatorAlgebra.OperatorThermodynamics
```

Then run umbrella builds:

```bash
lake env lean lean/InfoGeometry/Canonical/All.lean
lake build InfoGeometry.Canonical.All
```

For broader release validation, run:

```bash
lake build
```

## 9. Final synthesis

The current stack formalizes this theorem-safe doctrine:

```text
projector atoms are not measured by trace;
they are measured by cone-vector expectation.
```

```text
cylinder weights are not determinants;
they are state readouts omega(p_w).
```

```text
physical Weyl/GW volume is not primitive;
it is a calibrated projective readout over standard-form faces.
```

The standard-form bridge is therefore locked as:

```text
socket + conditional readbacks
```

not as:

```text
full Type III theorem.
```

## 10. Repository claims

When the corresponding modules compile, the repository claims the following
Lean-checked dependency skeleton:

```text
Projector splits yield lightcone arrows.
Drazin/MP mismatch yields chiral anomaly/supercharge data.
Odd Dirac/supercharge squares into even Laplacian/Hamiltonian data.
Weyl normalization turns homogeneous CAR/CCR data into canonical relations.
Souriau calibration turns K_sur into a normalized thermodynamic Hamiltonian readout.
Thermal/rotor boundary, Standard Form, and Type III interpretations are supplied
  through explicit sockets/certificates.
```

Any module introducing thermal/rotor boundary conditions, Standard Form, Type
III language, Connes cocycles, or natural cones must do one of the following:

1. use existing owner modules;
2. prove its theorem locally;
3. carry an explicit certificate/predicate without theorem content.

## 11. Architectural status

The current architecture is refactor-complete if all local bridges build and
are imported in the appropriate `All.lean` umbrella files.

This is not a claim that the repository proves full Type III analysis.  It is a
claim that the dependency skeleton is architecturally sealed:

```text
all major physical interpretations now pass through explicit theorem-bearing
or witness-gated sockets.
```
