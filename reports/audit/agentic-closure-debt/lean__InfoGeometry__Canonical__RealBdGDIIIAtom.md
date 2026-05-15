# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:47.654284+00:00`
Root: `lean/InfoGeometry/Canonical/RealBdGDIIIAtom.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **16**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RealBdGDIIIAtom.lean` | `advisory` | 38 | 0 | 16 | 6 | 22 |

## Findings by file

### `lean/InfoGeometry/Canonical/RealBdGDIIIAtom.lean`
- module: `InfoGeometry.Canonical.RealBdGDIIIAtom`
- status: `advisory`
- debt_score: `38`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L55 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L57 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L64 [soft] `law-field-locker` in `structure-field DIIISymmetryProxy.T_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field DIIISymmetryProxy.C_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field DIIISymmetryProxy.TC_eq_S` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field DIIISymmetryProxy.CT_eq_neg_S` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `simp-law-injection` in `simp-declaration cptSuperchargeOp_eq_modularK` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `simp-law-injection` in `simp-declaration cptSuperchargeOp_eq_modularK_root` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L113 [soft] `simp-law-injection` in `simp-declaration canonicalDIIIProxy_S_eq_neg_modularSuperchargeOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L117 [soft] `simp-law-injection` in `simp-declaration canonicalDIIIProxy_S_eq_neg_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L121 [soft] `simp-law-injection` in `simp-declaration canonicalDIIIProxy_T_eq_cptSuperchargeOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L125 [soft] `simp-law-injection` in `simp-declaration canonicalDIIIProxy_T_eq_modularK` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L130 [soft] `simp-law-injection` in `simp-declaration canonicalDIIIProxy_T_eq_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L135 [soft] `simp-law-injection` in `simp-declaration canonicalDIIIProxy_C_eq_paritySuperchargeOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L139 [soft] `simp-law-injection` in `simp-declaration canonicalDIIIProxy_C_eq_modular_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L200 [advisory] `bridge-shaped-declaration` in `theorem canonicalDIIIProxy_commutator_packet_of_realBdGDatum` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L242 [soft] `skeletal-proof` in `theorem canonicalDIIIProxy_T_maps_plus_to_minus` — proof appears to close via minimal tactic one-liner
  - L249 [soft] `skeletal-proof` in `theorem canonicalDIIIProxy_T_maps_minus_to_plus` — proof appears to close via minimal tactic one-liner
  - L280 [soft] `skeletal-proof` in `theorem canonicalDIIIProxy_fixedGradingIndexSign` — proof appears to close via minimal tactic one-liner
  - L304 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L810 [advisory] `existential-packaging` in `theorem canonicalDIIIProxy_transport_root_parity_vortexWitness_kkt_headSuperBracket_closure` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

