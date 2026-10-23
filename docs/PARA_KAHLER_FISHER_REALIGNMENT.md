# Positive and neutral bilinear forms: constructive realignment

## Ground-truth contract

The obstruction in `Physics/ParaKahlerFisherCompatibilityObstruction.lean`
assumes the fundamental symmetry acts as the identity everywhere. Combining
that identification with para-anti-invariance and nonnegative Fisher diagonals
forces every diagonal to vanish. The BKM obstruction separately rules out
global anti-invariance of its strictly positive real bilinear form.

The existing owner `Krein/DiracKreinFisherBridge.lean` already resolves the
incompatible identification by a specified carrier map and a fundamental
symmetry. For a real bilinear form `G` on a complete real inner-product space
`E`, it constructs on the existing `DoubledSpace E = WithLp 2 (E × E)`:

- `doubledPositiveBilin G u v = G u.fst v.fst + G u.snd v.snd`;
- `diracKreinBilin G u v = G u.fst v.fst - G u.snd v.snd`;
- a `ParaKahlerDatum` when `G` is symmetric, using `modular_j` as the
  anti-invariant involution. `spectral_epsilon` flips the second coordinate.

The narrowly missing consequences addressed here are recovery of the doubled
sum form by twisting back with `spectral_epsilon`, preservation of `G` by the
explicit first-sheet inclusion `x ↦ to_doubled x 0`, exact left/right radical
descriptions, and equivalence of nondegeneracy before and after doubling.
These use Mathlib's two-sided `LinearMap.Nondegenerate`, without finite
dimension assumptions. They preserve the whole original carrier, rather than
replacing an operator space with a scalar example.

The new owner imports the existing construction; it introduces no new
structure or assumed witness. No manifold, Lie thermodynamic system, BKM
inner-product instance, or automatic identification of the two forms is
claimed. Specific operator/BKM instantiation remains a separate compatibility
task. For arbitrary `G`, the sum form need not be positive; this implementation
does not prove a positivity equivalence. Existing `FiniteParaKahler` duality and isotropic-eigenspace results are
reused conceptually and not duplicated.

## Verification

The locked build of `InfoGeometry.Krein.DiracKreinNondegeneracyAudit` passed
(4192 jobs). All six axiom reports contain only `propext`, `Classical.choice`
and `Quot.sound`. Strict screening of the two new Lean files passed with zero
traps, and `git diff --check` passed. The build replayed 168 dependency/package
warning lines; none came from the two new files. Log:
`/tmp/dirac-krein-nondegeneracy-build.log`.

Independent A-A Poincare passed the final three files after the sum-form
wording correction. Independent QA-A Popper returned
`ACCEPTED_WITH_LIMITED_SCOPE` after rerunning the locked build, six axiom
reports, strict screening and diff checks. Its log is
`/tmp/dirac-krein-nondegeneracy-qa.log`. This is targeted verification, not
repository-wide completion.
