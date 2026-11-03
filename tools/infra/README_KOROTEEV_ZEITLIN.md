# Koroteev–Zeitlin mirror-symmetry research packet

This packet collects source inspired by the research topic “3D Mirror Symmetry
for Instanton Moduli Spaces.” Its Lean owner is
[KoroteevZeitlinMirror.lean](../../lean/InfoGeometry/Quiver/KoroteevZeitlinMirror.lean),
in namespace `KoroteevZeitlin`. That owner currently provides metadata records,
explicit formulas, and limited witness theorems. It does not establish a full
formalization of the paper merely by using its terminology or theorem names.

Source reviewed on 2026-11-03 at commit
`214f7bcf733eaf4720913bc2c082936f2480d3fc`. No new Lean or companion-backend
execution is recorded here. Read actual types and hypotheses using the
[repository search protocol](../../docs/REPO_DEEP_SEARCH_PROTOCOL.md).

## Current Lean scope

The distinctions below follow declarations and proof terms. Some source
docstrings retain broader research descriptions; use the types to determine
what a theorem establishes.

| Surface | What is present in this owner |
|---|---|
| `NakajimaQuiverVariety`, `quiverDim` | Dimension/framing vectors, parameters, and numerical dimension metadata. The dimension formula uses natural-number subtraction. The record does not construct a hyperkähler quotient. |
| `X_kl`, `X_kk_selfMirror` | A metadata family with `dimℂ := 0`; the named self-mirror theorem states reflexive equalities of its vectors. |
| `MirrorPair`, `X_kl_mirror_pair` | Two metadata records with equal recorded dimension and parameter functions. The supplied parameter functions are zero; no mutually inverse geometric maps are fields. |
| `QQSystem`, `QQRelation` | Polynomial and parameter data plus a separately defined predicate. The current predicate subtracts `Q i * Q_tilde i` from itself and equates the result to a neighbor product. It is not the shifted q-difference relation described in the research narrative. |
| `MiuraHbarOper.is_miura` | The reflexive equality `M.connection = M.connection`. |
| `qLanglands_QQ_to_opers` | Existence of an oper record with a matching `hbar`, using zero twist and connection. Its conclusion contains no bijection. |
| `XXZBetheData`, `BAE_ratio`, `IsBetheState` | An explicit finite-product ratio and the predicate that each ratio equals one. These definitions do not by themselves prove correspondence with geometric objects. |
| `HilbK_dim`, `HilbK_selfMirror` | The dimension recorded as `2 * k`, and a `MirrorPair` using the same record on both sides. |
| `quantum_K_mirror_iso`, `instanton_qK_mirror` | Ring equivalences between carriers both defined as `ℂ`, constructed with `RingEquiv.refl ℂ`. A curve-counting quantum product is not constructed by these declarations. |
| `trsLaxMatrix`, `trs_RLL` | An explicit matrix formula and existence of an `R` satisfying the displayed relation, witnessed by the zero matrix. The theorem does not require an invertible or nonzero R-matrix. |
| `instantonModuli_dim_sym`, `instanton_mirror_duality` | Symmetry of the recorded dimension `2 * N * k` and a metadata `MirrorPair`; no isomorphism of moduli spaces is the conclusion. |
| `X_kl_vertex_qKZ` | Returns the recurrence already supplied in the `VertexFunction.is_qkz` field. |
| `QQ_Bethe_bijection` | Repackages a supplied Bethe state and its assumed properties. Its type does not provide a bijection or construct a Bethe state from a QQ solution alone. |
| `X_kl_vw_swap` | Two constant-value statements about the `v` vectors. |

These are useful starting data and local algebraic statements. A clean build
would verify those statements as written; it would not strengthen their
conclusions into the corresponding geometric or physical interpretations.

## Tracked companion inventory

The inventory records source availability. Backend-specific scope and
successful execution require separate reviews and logs.

| System | File |
|---|---|
| SageMath | [koroteev_zeitlin_sage.sage](koroteev_zeitlin_sage.sage) |
| GAP | [koroteev_zeitlin_gap.g](koroteev_zeitlin_gap.g) |
| Macaulay2 | [koroteev_zeitlin_macaulay2.m2](koroteev_zeitlin_macaulay2.m2) |
| SymPy | [koroteev_zeitlin_sympy.py](../sympy/koroteev_zeitlin_sympy.py) |
| Coq | [KoroteevZeitlinMirror.v](bridge_data/KoroteevZeitlinMirror.v) |
| Isabelle/HOL | [KoroteevZeitlinMirror.thy](bridge_data/KoroteevZeitlinMirror.thy) |
| GaAlgebra | [koroteev_zeitlin_galgebra.py](koroteev_zeitlin_galgebra.py) |

The separate [proofs packet](../../proofs/README_3D_MIRROR.md) has a much
smaller Lean owner, `proofs/ThreeDMirrorSymmetry.lean`. Do not interchange its
status with the quiver owner above.

## Historical research goals

The original intake connected quiver varieties, QQ systems, Bethe equations,
Miura opers, quantum K-theory, tRS matrices, and mirror parameter exchange. It
also proposed explicit mirror isomorphisms, qKZ monodromy, an A∞ enhancement,
a Bethe/oper bijection, and a quantum product. These remain a useful list of
research obligations to check against actual owners and maps. They are not
completion claims supported by the limited declarations summarized here.

To strengthen this packet, specify the intended geometric carriers, define the
relevant relations with their nondegeneracy hypotheses, and construct maps
whose inverse, compatibility, and transport laws are theorem conclusions.
Record each such result beside its owner and exact hypotheses. Symbolic
examples or dimension equalities alone do not supply these maps.

The original bibliography and broader narrative are retained in the
[historical packet](https://github.com/nickgou-nuke/info-geometry-lean/blob/214f7bcf733eaf4720913bc2c082936f2480d3fc/tools/infra/README_KOROTEEV_ZEITLIN.md).
That version's cross-system completion percentages and physical identifications
are historical assertions, not current verification evidence.

## Targeted verification

From the repository root, with the pinned dependencies prepared:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Quiver.KoroteevZeitlinMirror
```

Consult the [root build guide](../../README.md). Record the commit, command,
backend versions, and exit status when reporting a new run. Distinguish a
successful build of the current declarations from completion of the research
goals above.
