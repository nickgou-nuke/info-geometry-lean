# Triality/cotangent source review

## Status and roles

This is a source review record, not a Lean kernel receipt. Native acceptance,
the changed synthesis consumer's compatibility build, and the ordinary root
publication gate are distinct requirements.

Generation and review were separated:

- The groupoid candidate was authored by the API reviewer and independently
  reviewed by the mathematical reviewer and integrating author.
- The form-transport and shear candidates were authored by the mathematical
  reviewer and inspected independently by the integrating author.
- The matrix core extraction and coordinate bridge were authored by the
  repository reviewer and inspected independently by the mathematical
  reviewer and integrating author.
- The order-three theorem was authored by the integrating author and reviewed
  independently by the mathematical reviewer. The concrete matrix/cotangent
  bridge was independently reviewed by the repository reviewer.
- The verifier generalization, wrapper, and hosted workflow were independently
  reviewed for retained defaults, exact pins, locks, ownership, axiom scope,
  source fingerprints, and failure handling.

No authoring worker ran a compiler or altered repository owners. Candidates
were integrated after review. One source-level bridge issue was corrected:
the pinned `pow_three'` lemma matches the left-associated matrix composition;
`pow_three` has the other association. The frozen proposal was retained.

## Exact source inventory

The existing bounded source inventory counted 91 explicitly named public
declarations in seven modules. Nine are the relocated existing matrix
declarations. This is not a native environment count; private helpers and
generated declarations are additionally covered by the native audit when it
runs.

| Owner | Public source heads | SHA-256 at source review |
|---|---:|---|
| `Algebraic.CoadjointActionGroupoid` | 23 | `20a558393fdf8b350ceb99fb5e84395299022e675d077743ee63fc7329ac3d48` |
| `Algebraic.CotangentFormTransport` | 7 | `15212cb964cf9bed77fe35f1c0a9e5d12bddd71a1daee5422da99c6f6c5cfd9d` |
| `Algebraic.CotangentFixedPointObstruction` | 6 | `1e2014337aeaeeaeae2ef18e7a3762f4562bcb21cefbe22b1bbe92e6779202e2` |
| `Algebraic.OrderThreeFixedForm` | 4 | `89627063dceb177becb543ecb83c9be1ff94d407603a9df66a6ea67a6a1bfdda` |
| `Lie.TrialityCartanMatrixCore` | 9 | `50b22bd3278b10b4e2b0a2127403a4ecd80623c46f22ccaf7ab02ac1d9b759de` |
| `Lie.CartanTrialityFirstCoordinate` | 36 | `23bdadc53effad3889c3eebcbd6676372b406a82893ad57f7b284f989a8cc9c7` |
| `Lie.CartanTrialityCotangentFixedForm` | 6 | `de07e3dc6af23860d85498f30d3b257d309993d81a491aa7cee9307570b37ab7` |

The groupoid integration removes the candidate-status comment and annotates
the two class-valued action definitions with Lean's `instance_reducible`
attribute. It does not disable the class-reducibility warning or change any
mathematical statement.

## Semantic review

The action category has native typed endpoints. Its label composition is
`(f ≫ g).hom = g.hom * f.hom`, and the functor and both naturality proofs
use that order. The fixed action is derived from intertwining. Its inclusion
is faithful; fullness is not claimed. The arrow equivalence characterizes
precisely the fixed group labels between already-fixed objects.

The cotangent carrier uses the actual algebraic dual. Bracket terms come from
the native Lie bracket, and covariance uses a native `LieEquiv`. The full
twisted bilinear form is nondegenerate, with alternation proved separately.
The shear example supplies an actual nonzero radical vector for a preserved
form's fixed restriction. The order-three repair proves both radicals vanish
by the fixed orbit sum. The concrete four-dimensional cycle supplies that
hypothesis for its contragredient cotangent lift.

The new matrix convention is conjugated to the old one by the actual signed
permutation. The existing presentation is transported through that proved
conjugation. The fixed-plane dimension is obtained from a native linear
equivalence, and the two specified vectors are actual basis values.
Nontriviality, orthogonality, and both requested cycle readouts use the
original noncommutative matrix carrier.

The review does not promote Euclidean matrix orthogonality to a Killing-form
identification, or the fixed two-plane to a complete fixed Lie algebra.
The existing larger synthesis's bracket-transport construction and other
triality actions are recorded in the intake contract with their own scopes.
No smooth cotangent groupoid or physical dynamics are constructed here.

## Name-preserving extraction

The extracted block begins with the Vector–Spinor Hadamard swap comment and
ends immediately before the integer-valued 24-root enumeration. The original
122-line declaration/proof block has SHA-256
`4accd6d59f1397005999062100d15ab0a046f9199829a646907f2ddffbd81ea2`.
It has no dependency on preceding private Krein declarations. Its original
namespace, options, noncomputable section, and required open namespaces are
retained. The large synthesis imports the new owner, preserving all nine
public names. No compatibility aliases or duplicate definitions are added.

The native focused audit uses module metadata rather than namespace-prefix
guesses, so it checks declarations now owned by `TrialityCartanMatrixCore`
despite their retained original namespace. The hosted workflow separately
builds the large synthesis after the focused transaction succeeds.

## Validation controls

The shared verifier retains its original six targets and seventeen reused
declarations as defaults. The new wrapper selects seven targets and eleven
explicit reused declarations. The toolchain and root/focused package pins
are unchanged. The same shared lock, exact dependency revisions and tracked
cleanliness, fresh warnings-as-errors elaboration, native module ownership,
and transitive axiom checks remain required.

Target and reused-name lists are validated before path/command use. Explicit
extra sources must be existing tracked files. The final checks require
unchanged HEAD, source hashes, generated audit source, package state, and
override contents. No failure is ignored or converted to a passing receipt.

The workflow fetches the exact public commit without configuring credentials,
does not recurse into submodules, and preserves `contents: read`. The focused
receipt is retained even if the later synthesis compatibility build fails.
Python, YAML, and embedded-Python syntax were independently parsed during
source review; these checks do not execute the native verifier.

## Executed source checks

At the seven-owner checkpoint, these commands exited zero:

- `git diff --cached --check`.
- `python3 -B tools/quality/proof_proxy_staged_gate.py`.
- `python3 -B tools/quality/placeholder_audit.py --strict` with the seven
  selected owner paths: zero hard findings and two reviewed soft findings.
- `python3 -B tools/infra/axiom_audit.py --fail-on-gaps` with those paths:
  zero source-level open gaps.
- `python3 -B tools/quality/repo_lean_scope_audit.py` with those paths:
  zero debt or scope findings.
- `python3 -B tools/quality/semantic_content_audit.py` with one
  `--file-prefix` per selected owner and `--gate`: seven selected files and
  zero findings.

The soft flags concern `bracketForm_isAlt`, which applies native bracket
alternation and linearity at zero, and the private real-number helper
`eq_zero_of_three_sum`. Both were inspected at their actual types. The latter
only cancels the real coefficient three inside the full native bilinear-form
argument; it does not replace the operator or form carrier.

Both Python files parsed. The workflow parsed as YAML, all six run-step shell
snippets passed `bash -n`, and both embedded Python blocks parsed. A direct
source-snapshot inspection confirmed inclusion of all six required tracked
extra files. A byte comparison against the original owner confirmed the
declared hash of the relocated matrix proof block.

The maintained root path-package preflight actually ran and exited one:
HomotopyHypothesis and Atlas lack their required configurations and tracked
provenance, and the pinned GIFT Gitlink is uninitialized. InfoGeometryCore's
tracked configuration is present. This preflight is not a compiler run or a
full publication-gate pass. The earlier local native transaction remains
queued on another job's shared build lock; that job and lock were untouched.

Native acceptance of this new seven-owner change is pending. The focused
hosted workflow supplies the compiler, fresh-source, and native axiom route,
followed by the separate synthesis compatibility build. Draft publication
does not discharge any of those requirements.
