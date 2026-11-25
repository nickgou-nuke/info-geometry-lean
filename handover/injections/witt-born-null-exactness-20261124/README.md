# Witt modes, Born exchange, and null exactness

This continuation of draft PR #446 extracts the valid algebraic targets from
the attached proposed module and rejects its incorrect multiplication table.
The incoming text is preserved in `source-intake.txt`; its claims of successful
compilation are not treated as evidence.

## Implementation

- `Canonical/ZornCliffordWittBorn.lean` uses the existing genuine real
  sixteen-dimensional Dirac action. It adds the source frame, its Clifford
  relations, four normalized primal/dual Witt modes, the unnormalized factor
  four identity, and the four-negative-generator Born exchange involution.
- `Algebra/ZornNullIncidence.lean` gains two focused results: conjugate range
  is contained in the left kernel for null inputs, and equals that kernel for
  nonzero null inputs. The existing finrank-four results supply the dimension
  argument; no duplicate trace proof or octonion carrier is introduced.
- `Verification/SuppliedTableCounterexample.lean` is an isolated integer
  specialization of the exact supplied coefficients. It records failures of
  alternativity, conjugate contraction, norm composition, and the advertised
  seven-operator volume. It is not imported by `InfoGeometry.All`.

The source orientation is unchanged: the previously ordered eight-generator
volume represents minus the chosen chirality. This continuation supplies no
full Clifford algebra equivalence or physical reciprocity theorem.

## Review and validation

- `CONTRACT.md` records exact carriers, normalization, hypotheses, and scope.
- `SOURCE_REVIEW.md` is the independent mathematical and source review.
- `VALIDATION_REVIEW.md` reviews suite selection, import/audit coverage, and
  the corrected single acquisition of the maintained build lock.
- `VALIDATION.md` records actual native and CI outcomes. Source review alone
  does not establish elaboration or axiom acceptance.
- `failed-native-check.json` preserves the earlier local native retry that
  was killed while compiling the existing Zorn prerequisite.

The checker has a small `supplied-zorn-counterexample` suite and a combined
`witt-born-null-exactness` suite. The latter covers both previous PR target sets
and these additions, with a 50-module repository dependency closure and a
15-owner declaration audit. These inventory counts are not passing-build
claims. Existing repository gates and dependency pins remain unchanged.
