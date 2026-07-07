# Hestenes/Krein complex-axis multi-system packet

Scope: finite exact algebra around the real square-minus-one Hestenes/Krein phase axis.

This packet intentionally does not introduce a new Lean owner theorem. The Lean side is already owned in the repository; this directory mirrors the finite algebra in external CAS/proof systems and audits the existing Lean owner declarations.

## Exact finite theorem surface

Let

```text
K = [[0,-1],[1,0]]
J = [[0, 1],[1,0]]
epsilon = [[1,0],[0,-1]]
```

Then:

1. `K^2 = -I`.
2. `J^2 = I`.
3. `epsilon^2 = I`.
4. `J epsilon = K` and `epsilon J = -K`.
5. `trace(K)=0`.
6. `rho(a,b)=aI+bK` preserves complex multiplication:
   `rho(a,b) rho(c,d) = rho(ac-bd, ad+bc)`.
7. For a general real matrix `A=[[p,q],[r,s]]`, `[K,A]=0` exactly imposes the complex-linear shape `r=-q`, `s=p`.

## Existing Lean owner surfaces found by deep search

| Claim family | Existing owner | Key declarations |
|---|---|---|
| doubled real phase axis | `lean/InfoGeometry/Krein/DoubledSpace.lean` | `complex_i`, `complex_i_sq`, `modular_j_involution`, `spectral_epsilon_involution`, `modular_j_spectral_epsilon_anticommute` |
| split `Cl(1,1)` atom | `lean/InfoGeometry/Quantum/RealSplitClifford.lean` | `RealSplitCl11Action.K`, `RealSplitCl11Action.K_sq`, `doubledSpaceCl11Action_K` |
| categorical complexification from `K^2=-Id` | `lean/InfoGeometry/Quantum/RealKCategory.lean` | `RealKVect`, `complexModule`, `complexI_smul_eq_K` |
| projective generic complexification from `S^2=-Id` | `lean/InfoGeometry/Projective/FiveGradedCentralizer.lean` | `complexSMul`, `complex_mul_smul`, `complexModule` |
| Hestenes scalar/operator coefficient embedding | `lean/InfoGeometry/Canonical/HestenesComplexTranslation.lean` | `hestenesScalar`, `hestenesScalar_I_sq`, `hestenesCoeff_mul`, `hestenesScalar_commutes_iff_phaseLinear`, `modular_j_conjugates_complex_i` |
| Hestenes commutant/normalizer laws | `lean/InfoGeometry/Canonical/HestenesCommutantGeometry.lean` | `CommutesWithHestenesK`, `commutesWithHestenesK_iff_phaseLinear`, `hestenesLeftCoeff_mul` |
| rotor/bivector packaging | `lean/InfoGeometry/Clifford/RealDoubledHestenesAnchor.lean` | `doubledIBivector`, `doubledI_rotor_exp_reverse`, `doubledI_rotor_reverse_comp_exp` |
| bounded Hestenes/Krein commutator derivation | `lean/InfoGeometry/Canonical/HestenesKreinModularGeometry.lean` | `hestenesCommutator`, `modularDerivation`, `modularDerivation_eq_zero_iff_commutes`, `IsMonogenic`, `isMonogenic_iff_commutes` |
| Clifford `Cl(1,1)` pseudoscalar lane | `lean/InfoGeometry/Clifford/Hestenes.lean` | `pseudoscalar_sq`, `cl11_commutator_is_derivation`, `cl11Rep_pseudoscalar_eq_spectral_epsilon` |

## Engines

Run:

```bash
python3 tools/multisystem/hestenes_krein_complex_axis/run_all.py
```

The runner first checks that the repo-wide deep-search artifacts exist. This is
deliberate: no new theorem/code surface in this packet is justified without the
search-first duplication audit.

Deep-search artifacts:

- `deep_search_inventory_lean.json` — maintained `lean/` scan.
- `deep_search_inventory_tools.json` — maintained `tools/` scan.
- `deep_search_inventory_docs_misc.json` — `docs/`, `scripts/`, `tests/`, and
  root metadata scan.
- `deep_search_external_refs_rg.txt` — `external_refs/` and `lib/` scan using
  `rg --no-ignore` with generated/cache/vendor exclusions.
- `deep_search_duplication_table.md` — synthesized owner/duplication table.

Verified lanes:

- SymPy exact symbolic matrices: `sympy_hk_complex_axis.py`
- Sage exact polynomial matrices: `sage_hk_complex_axis.sage`
- GAP rational representative matrix relations: `gap_hk_complex_axis.g`
- Singular polynomial ideal reduction: `singular_hk_complex_axis.sing`
- Macaulay2 with explicit `Dmodules` package load plus polynomial reductions: `macaulay2_hk_complex_axis.m2`
- Coq/Rocq integer-pair proof: `HestenesKreinComplexAxis.v`
- Isabelle/HOL integer-pair proof: `HestenesKreinComplexAxis.thy` with `ROOT`
- Lean owner source audit: `lean_owner_source_audit.py`

Last observed result:

```text
deep_search_artifact_audit: ok
sympy: ok
sage: ok
gap: ok
singular: ok
macaulay2_dmodules: ok
coq: ok
isabelle: ok
lean_owner_source_audit: ok
HK_COMPLEX_AXIS_MULTI_SYSTEM_OK
```

## Negative scope / open claims

This finite packet does not prove:

- full Hestenes spacetime algebra classification;
- global Krein/Tomita--Takesaki analytic modular theory;
- unbounded operator-domain closure;
- real split `G_{2(2)}` or split-octonion automorphism classification;
- D-module holonomicity for a geometric PDE system.

Those require separate owner surfaces and native Lean proof closure. This packet only grounds the shared algebraic axis used by those later bridges.
