# Real Beltrami flow and cotangent transport

## Intake and scope

The request is to implement and publish the explicit real Arnold/SDiff/chiral
connection discussed on 2026-11-27. The concrete mathematical target is
`u_s(x,y,z) = (cos z, -s sin z, 0)` and its particle flow
`phi_(s,t)(x,y,z) = (x + t cos z, y - s t sin z, z)`.

This is a native spatial example and representation bridge (analysis risk R4).
It does not assert an infinite-dimensional Lie-group manifold, the general
Euler–Arnold geodesic theorem, or a spectral decomposition of curl.

## Existing owners and exact carriers

- `Canonical/NavierStokesShearReconstruction` owns `Space = Fin 3 → ℝ`, actual
  coordinate derivatives, divergence, curl, advection, and the pointwise PDE.
- `Quantum/DualFlatKreinGraph` owns `EuclideanSpace ℝ (Fin n)` paired with its
  native real linear dual and the half-normalized neutral pairing.
- `Quantum/MobiusRealCotangentLift` transports a vector by a linear equivalence
  and a covector by composition with its inverse. It already proves pairing,
  grading, and composition compatibility.
- Native Mathlib `Homeomorph`, `Subgroup`, `ContDiff`, `MeasurePreserving`,
  `MeasurableEquiv.piFinSuccAbove`, and `MeasurePreserving.skew_product` provide
  the smooth volume-preserving automorphism construction.

## Proof obligations

1. Compute the field's actual derivatives, divergence, curl and advection.
   Prove stationary unforced Euler for every real `s`. Prove curl equals
   `s • velocity` when `s ^ 2 = 1`; the actual helicity density equals `s`
   for every real parameter.
2. Construct the particle flow, its inverse at negative time, composition,
   smoothness, time derivative, spatial Fréchet derivative, and determinant.
3. Construct a subgroup of smooth measure-preserving homeomorphisms, prove
   actual Lebesgue preservation, and construct the one-parameter group map.
4. Transport the actual spatial derivative to the existing Euclidean carrier.
   Construct the momentum covector and actual curl state. Prove physical
   cotangent transport under `s ^ 2 = 1` and identify the neutral quadratic
   readout with the computed physical helicity density.
5. Compute helicity over explicit finite regions. Do not identify a rectangular
   fundamental cell with an invariant subset or an already constructed torus.

## Hypotheses and rejected stronger claims

The flow and stationary Euler equation hold for arbitrary real `s`. Exact
momentum preservation by the inverse-transpose derivative requires `s ^ 2 = 1`;
the general covector defect is proportional to
`t * (1 - s ^ 2) * sin z * cos z`. A volume-preserving derivative need not be
orthogonal. The implementation includes a nonorthogonal derivative witness.

The unit-sign fields have constant squared norm one on all of real coordinate
space. No finite whole-space energy or helicity is claimed. The subgroup
construction supplies group operations and smooth measure-preserving elements;
it supplies no infinite-dimensional topology or Lie algebra. Identifying curl
spectral chirality with existing doubled-space projectors remains open.

The generic subgroup preserves the chosen measure and may contain
orientation-reversing maps. The explicit Beltrami flow additionally preserves
orientation, as its computed Jacobian determinant is one.

## Provenance and acceptance

The source baseline is upstream `fe24e350b08fdea04f74c0748ef9fd9417c47529`.
Lean and Mathlib pins remain those in the repository toolchain and manifest.
Candidate authors, independent semantic review, and final execution review are
separate roles. Acceptance requires compilation of the exact source closure,
native transitive axiom inspection, placeholder/semantic scans, and the tracked
publication gates, with root-package failures reported separately from the
selected-module results.

## Verified implementation

| Owner | Main results |
| --- | --- |
| `Canonical/ArnoldBeltramiFlow` | `coordDeriv_velocity`, `curl_velocity_formula`, `curl_velocity`, `stationary_euler`, `hasDerivAt_flow`, `hasFDerivAt_flow`, `flowJacobian_det` |
| `Canonical/SmoothVolumePreservingGroup` | `smoothVolumePreservingSubgroup`, a native subgroup with proved closure under composition and inversion |
| `Canonical/ArnoldBeltramiVolume` | `measurePreserving_flow`, `flowHom`, `flowHom_injective`, `helicity_integral_periodicCell` |
| `Canonical/ArnoldBeltramiCotangentTransport` | `tangentEquiv_fderiv`, `cotangentLift_physicalState`, `neutralPair_physicalState`, `physicalState_nonnull`, `tangentEquiv_nonorthogonal` |

The spatial family and its particle flow are smooth for every real parameter.
The curl-eigenfield, unit-length, and physical momentum-transport statements
retain `s ^ 2 = 1`. Both signs are included. The helicity integral is a native
Lebesgue integral over `[0, 2π]^3`, equal to `(2π)^3 * s`.

Two supporting changes are required: `Quantum/DualFlatKreinGraph` now imports
the specific Mathlib inner-product-space owner rather than the full umbrella
(its declarations are unchanged), and a missing closing line in the existing
`check_operator_geometry.py` baseline-blob lookup is restored. No verification
condition, toolchain, or dependency pin is weakened or changed.

## Focused validation

On 2026-11-27, the exact 13-module source closure compiled with Lean `4.34.1`
and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. All five modified
mathematical owners passed with warnings treated as errors. Compatibility
checks include the existing `MobiusRealCotangentLift`, `PACKreinEquivalence`,
and `SplitPAC44KreinCarrierBridge` consumers; the repository umbrella is outside
this focused result. Existing linter warnings in those unchanged consumers are
reported by the checker and are not warnings in the modified owners.

`Canonical/ArnoldBeltramiDeclarationAudit` inspects every declaration owned by
the five selected modules, including generated declarations, with native
`Lean.collectAxioms` and type/value dependency inspection. The run accepted
147 declarations: 41 spatial-flow, 32 cotangent-transport, 24 volume-flow,
4 group-construction, and 46 existing `DualFlatKreinGraph` declarations.
The only permitted foundational axioms are `propext`, `Classical.choice`, and
`Quot.sound`; unsafe declarations, partial declarations, owner-local axioms,
and any other transitive axiom are rejected. This is distinct from a text scan.

Independent A-A source review passed the exact theorem sources, checked the
physical interpretation and nonvacuity, and confirmed the scope boundaries.
Independent QA-A then repeated the full focused check from fresh repository
artifacts and passed the same 13-module closure and 147-declaration audit
(117 theorem declarations and 30 definitions). All eight unchanged repository
dependencies match their exact baseline bytes. The source and verification-tool
hashes match both runs. The three unchanged consumer modules emit respectively
4, 4, and 1 existing linter warnings; all modified owners and the audit are
warning-clean. Source scans found no proof holes, custom axioms, unsafe proof
bypasses, or vacuous certificates in the new mathematical owners.

To reproduce the focused check from the repository root, set `ARNOLD_MATHLIB`
to a clean checkout of the pinned Mathlib revision and `ARNOLD_LEAN` to the
pinned Lean binary, with the required Mathlib caches available, then run:

```bash
python3 tools/quality/check_operator_geometry.py \
  --repo . --mathlib "$ARNOLD_MATHLIB" --lean "$ARNOLD_LEAN" \
  --work-dir /tmp/arnold-beltrami-verification \
  --owner InfoGeometry.Quantum.DualFlatKreinGraph \
  --owner InfoGeometry.Canonical.ArnoldBeltramiFlow \
  --owner InfoGeometry.Canonical.ArnoldBeltramiCotangentTransport \
  --owner InfoGeometry.Canonical.SmoothVolumePreservingGroup \
  --owner InfoGeometry.Canonical.ArnoldBeltramiVolume \
  --target InfoGeometry.Canonical.ArnoldBeltramiCotangentTransport \
  --target InfoGeometry.Canonical.ArnoldBeltramiVolume \
  --target InfoGeometry.Quantum.PACKreinEquivalence \
  --target InfoGeometry.Quantum.SplitPAC44KreinCarrierBridge \
  --owner-warnings-as-errors --audit \
  --audit-source lean/InfoGeometry/Canonical/ArnoldBeltramiDeclarationAudit.lean
```

The checker records exact source hashes, compiler version, dependency revisions,
compilation order, and native declaration-audit output. Its existing custom-owner
`--base-ref` limitation is not altered by this change; unchanged repository
dependency sources are compared separately against the baseline.

## Root integration and publication status

The maintained `ci_bootstrap.py paths` preflight fails: `HomotopyHypothesis`
and `Atlas` have missing, untracked path-package configurations, and `GIFT` is
an uninitialized gitlink. The tracked `InfoGeometryCore` path package passes
that preflight. A real invocation of `run_locked_lake_build.py` for the new
cotangent and volume targets exited with code 1 because the
`external_refs/homotopy-hypothesis-lean4` package directory is absent.

The tracked staged proof gate passed. The tracked pre-push hook was executed
for the new-branch update and failed in its incremental stage at that same
locked root build. All six changed Lean files passed the other executed
incremental checks: zero textual debt, zero semantic-content findings, and
zero tracked-scope debt or unclassified-source findings. The hook stopped
before its later new-ref gate invocation; pre-push acceptance did not pass.

A separate `bash scripts/quality/post_build_gate.sh --full` invocation exited
with code 1. The root build remained blocked. The repository-wide vacuity
check exited with code 2 and reported incomplete coverage (1,201 unreadable
tracked paths in this partial checkout) and heuristic findings. The full
semantic-content command also exited with code 2, despite reporting zero
current findings. The full tracked-scope, quarantine, textual-debt, and theory
report commands passed. These results are retained as integration blockers,
not replaced by the focused source-closure certificate.

The user explicitly requested implementation and upstream publication. The
delivery is therefore a draft review checkpoint with these failures retained,
pending root integration and publication-gate acceptance. The focused source
and native-axiom results do not certify the root package or make the PR ready
to merge. No missing dependency is replaced with a moving branch or a stub.

Mathematical references:

- V. I. Arnold, 1966, *Sur la géométrie différentielle des groupes de Lie de
  dimension infinie et ses applications à l'hydrodynamique des fluides parfaits*,
  https://doi.org/10.5802/aif.233.
- B. Khesin, 2012, *Dynamics of symplectic fluids and point vortices*, §2,
  https://doi.org/10.1007/s00039-012-0182-7.
- B. Khesin, D. Peralta-Salas and C. Yang, 2022, *The helicity uniqueness
  conjecture in 3D hydrodynamics*, https://doi.org/10.1090/tran/8483.
