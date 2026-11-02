# 3D mirror-symmetry research companions

This directory contains a historical collection of scripts and proof-language
files inspired by Koroteev–Zeitlin's mirror-symmetry research. The Lean file
in this packet is [ThreeDMirrorSymmetry.lean](ThreeDMirrorSymmetry.lean).
It currently proves three elementary commutativity statements. It does not
construct instanton moduli spaces or prove a mirror equivalence.

Source reviewed on 2026-11-03 at commit
`214f7bcf733eaf4720913bc2c082936f2480d3fc`. This review records the Lean
declarations and tracked companion paths; it is not a fresh execution report
for the seven backends. Use the
[repository search protocol](../docs/REPO_DEEP_SEARCH_PROTOCOL.md) when looking
for related results elsewhere.

## Exact Lean content

All three theorems are in namespace `ThreeDMirrorSymmetry`.

| Theorem | Statement |
|---|---|
| `complex_add_comm` | `a + b = b + a` for complex numbers. |
| `complex_mul_comm` | `a * b = b * a` for complex numbers. |
| `matrix_add_comm` | `A + B = B + A` for complex matrices. |

The filename is `ThreeDMirrorSymmetry.lean`; the older spelling
`3DMirrorSymmetry.lean` is not the owner. The more extensive quiver-side packet
is documented in [README_KOROTEEV_ZEITLIN.md](../tools/infra/README_KOROTEEV_ZEITLIN.md),
which also explains its current limitations. Imports and similarly named files
must not be treated as evidence that this small module proves their subject.

## Companion inventory

| File | Backend / intended research role |
|---|---|
| [3d_mirror_symmetry_sympy.py](3d_mirror_symmetry_sympy.py) | SymPy computations around Bethe and QQ data. |
| [ThreeDMirrorSymmetry.lean](ThreeDMirrorSymmetry.lean) | The three Lean statements listed above. |
| [3d_mirror_dmodules.sage](3d_mirror_dmodules.sage) | SageMath D-module and Weyl-algebra exploration. |
| [qq_system_m2.m2](qq_system_m2.m2) | Macaulay2 QQ-ideal exploration. |
| [3d_mirror_symmetry.v](3d_mirror_symmetry.v) | Coq source companion. |
| [3d_mirror_symmetry.thy](3d_mirror_symmetry.thy) | Isabelle/HOL source companion; see [ROOT](ROOT) for session configuration. |
| [3d_mirror_gap.g](3d_mirror_gap.g) | GAP quiver exploration. |

These are source entries, not a table of completed mathematical equivalences.
Before reporting a cross-system result, state the proposition checked by each
backend, the translation between representations, and the run provenance.

## Research context

The historical intake lists quiver dimension/framing data, XXZ Bethe equations,
QQ systems, twisted Miura opers, quantum K-theory, and exchange of Kähler and
equivariant parameters. Preserve these as research topics. The present Lean
owner supplies none of the maps or compatibility theorems needed to conclude
the full mirror-symmetry statement.

The complete original narrative and bibliographic references are available in
the [historical README](https://github.com/nickgou-nuke/info-geometry-lean/blob/214f7bcf733eaf4720913bc2c082936f2480d3fc/proofs/README_3D_MIRROR.md).
Its blanket verification and completion claims are not current build evidence.

## Targeted local checks

Use the repository-root environment and shared lock for Lean elaboration:

```bash
python3 tools/infra/run_locked_lean.py --wait-for-build-lock proofs/ThreeDMirrorSymmetry.lean
```

This checks the source against the prepared dependency environment. It does
not build missing imports automatically. Follow the [root build guide](../README.md)
for setup and owner builds. The nested [lakefile.toml](lakefile.toml) describes
the separate proofs package; a blanket `lake build` inside this directory is a
broader operation than checking this packet.

The Python companion can be examined and run separately when its dependencies
are available:

```bash
python3 proofs/3d_mirror_symmetry_sympy.py
```

A successful script run does not add a theorem to the Lean owner.
