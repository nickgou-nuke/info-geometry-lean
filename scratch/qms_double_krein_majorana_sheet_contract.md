# Ground-truth contract: Majorana nilpotent maps and Krein sheets

## Mathematical claim

On the repository's canonical doubled real carrier `DoubledSpace E`, the concrete
split-null CAR creation and annihilation maps have sheet-valued kernels and
images. Creation annihilates the positive epsilon sheet and maps the negative
sheet to the positive sheet; annihilation annihilates the negative sheet and
maps the positive sheet to the negative sheet. The PHS-invariant sum of these
maps is `modular_j`, which swaps the sheets and is invertible. Its vector
kernel is therefore trivial; it is a connector between sheets, not a vector
zero mode.

## Carrier and conventions

`DoubledSpace E = WithLp 2 (E × E)`, with `spectral_epsilon (x, ξ) = (x, -ξ)`.
`plusSheet` and `minusSheet` are the +1 and -1 eigensets of this involution.
The operators are `concreteCARCreation` and `concreteCARAnnihilation` from the
canonical split-null CAR construction.

## Existing proved facts

- `TomitaKreinNilpotentAtom.concrete_creation_square_zero` and
  `concrete_annihilation_square_zero`.
- `SuperchargeCARCCRBridge.concrete_creation_comp_annihilation_eq_spectralPlusProj`
  and `concrete_annihilation_comp_creation_eq_spectralMinusProj`.
- `MajoranaPHSZeroMode.concrete_majorana_swap_is_phs_invariant` and
  `concrete_majorana_swap_eq_modular_j`.
- `SplitQuadraticSheets.mem_plusSheet_iff_snd_eq_zero` and
  `mem_minusSheet_iff_fst_eq_zero`.
- `BogoliubovFockSuper.cliffordConcreteCreation_apply_to_doubled` and
  `cliffordConcreteAnnihilation_apply_to_doubled`.

## Completed declarations

Add pointwise kernel characterizations:

```lean
concreteCARCreation u = 0 ↔ u ∈ plusSheet
concreteCARAnnihilation u = 0 ↔ u ∈ minusSheet
(∃ v, concreteCARCreation v = u) ↔ u ∈ plusSheet
(∃ v, concreteCARAnnihilation v = u) ↔ u ∈ minusSheet
```

Also state the sheet-to-sheet actions on canonical points and characterize the
full images of both maps. These are finite algebraic statements over the
already-defined doubled carrier.

`MajoranaSheetConnectors.lean` proves these claims, including
`majorana_swap_kernel_iff_zero`.

## Not established by this contract

No analytic/BdG Hamiltonian zero-mode theorem, nonzero vector kernel for the
Majorana swap, white/black graph identification, topological boundary mode,
index theorem, or physical Majorana particle interpretation is asserted.

## Evidence / discovery receipt

`scratch/double_krein_majorana_sheets_discovery.json` is navigation evidence
only. Its graph lane was unavailable because the local Python environment
lacks `networkx`; source inspection is authoritative.
