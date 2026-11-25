# Independent source review

Disposition: source review accepted for the exact real linear-algebra and
finite-network scope in THEOREM_CONTRACT.md. This review is separate from
compiler and axiom audit receipts. Compilation of the repaired dependency
closure remains pending at this review snapshot; no compiler pass or
release acceptance is asserted here.

The mathematical reviewer checked the native dual carrier and graph submodules,
the existing para-involution, and the definitions of the imported minors,
signed edge sums, and block Dirac operator. The review found no mathematical
defect in the statements or normalization.

Specific findings:

- The mirror, graph swap and fixed-locus results require no skew premise.
- The epsilon half-pairing has sign minus one; the raw contraction has factor
  minus two. Both edge-matrix and real block-operator scalings agree.
- The supplied minor owner uses exactly the same multiplication order as the
  local real spinor specialization.
- Congruence and forward image require no invertibility; the kernel transport
  is a sufficient implication, with no unjustified converse.
- The product parity is one sign per edge, so physical CPT invariance is not
  inferred from the anti-isometry.
- The Plücker identity includes rank-deficient spinor families. It does not
  assert a nonzero projective coordinate vector or construct a Grassmannian
  point. Positivity and a geometric realization of the supplied graph/signing
  are additional conditions, as recorded in the theorem contract.

## Review of compiler-directed repairs

The initial source review compared the predecessor graph owners byte for
byte. Subsequent changes were inspected against that predecessor and against
the initial review of the two new owners:

- `SkewGraphNeutralPairing.lean`: added `map_add` and `map_neg` to the two
  `simpa only` steps in `dualGraph_orthogonal_eq` and
  `dualGraph_sup_neg_eq_top_iff`. These expose linear-map evaluation after
  subtraction has been rewritten as addition of a negative. Renamed the
  local witnesses from `ξ₊`/`ξ₋` to `ξPlus`/`ξMinus` to avoid the reported
  parser failure. No declaration statement, hypothesis, or witness value
  changed.
- `PlabicDiracCourantUnification.lean`: explicitly eta-expanded the edge
  weight argument before rewriting in `edgeSumMatrix_eps2` and
  `edgeSumDirac_eps2`. This exposes the applied `contractionWeight` expression
  to `simp_rw`; it changes neither the weight nor the factor minus two.
  Renamed the spinor-family binder from the reserved lambda token to
  `spinors` in the two Plücker statements and proofs. These statements are
  alpha-equivalent to the reviewed mathematical contracts.
- `MatrixDiracGraphs.lean` remains byte-for-byte identical to the predecessor
  owner.
- `DiracGraphMirror.lean`: the product-parity proof now applies the exact
  native `Finset.prod_neg` theorem after rewriting the anti-isometry. This
  replaces a local induction and preserves the theorem statement.

The repairs preserve the reviewed theorem contracts. No new mathematical
defect or obvious elaboration mismatch was found in this source review.
The reviewer read all four final owners and their relevant imported APIs,
compared source text, and computed hashes; the reviewer ran no Lean build,
test, or axiom audit. Decisive compiler and axiom results belong to the
separate serialized verification record.

## Additional independent final review

A separate reviewer inspected all four owner files, the relevant imported
definitions, the verifier, native audit, reconciliation script, and saved
failed-run evidence. It found no concrete mathematical or verification-design
defect requiring a change. It then reread the direct `Finset.prod_neg` proof
and confirmed that the source-review disposition was preserved. The review
did not run Lean or the native audit and does not supply compiler acceptance.
The reviewer also accepted the compiler-path normalization after checking
executable identity and the archived recovery evidence, and confirmed the
spinor-family binder rename without changing the source-review disposition.

Reviewed source identities:

| File | SHA-256 |
| --- | --- |
| `SkewGraphNeutralPairing.lean` | `8a73617a5994451bad5cfb3748e541f9b75fb6b3ae29a08aa46afd92eea5e210` |
| `MatrixDiracGraphs.lean` | `f421eed87480b01d5698bf44b2fe6fd05ea21942cda7b7d59c91bb7fac88b2b0` |
| `DiracGraphMirror.lean` | `d231e2b562fd50b439f1ae9e4fa466545f7d04808ef0a264bdad9f2675e64928` |
| `PlabicDiracCourantUnification.lean` | `ccea9530dcf1462df101a65f994efe20844e1cc46db2be183eb02c4f98e1d396` |
