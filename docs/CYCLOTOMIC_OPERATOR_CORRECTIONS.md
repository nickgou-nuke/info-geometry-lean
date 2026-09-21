# Cyclotomic and split-operator corrections

## Source owners reused

- `Algebra/SplitQuaternionMatrices.lean`: real matrix units, complementary
  idempotents, multiplication table, and nonzero nilpotents.
- `Geometry/MoebiusChiralGeneratorClassification.lean`: upper/lower nilpotent
  matrices and traceless-generator identities.
- `Physics/HestenesKreinOperatorCalculus.lean`: actual `NormedSpace.exp`
  formulas for square-negative, square-positive, and square-zero generators.
- `Algebra/LieCyclotomicBridge.lean`: native polynomial evaluation, exact
  orders three and four, and rotation/exponential correspondence.

## Corrected statements

`Algebra/CubicCompanionFlow.lean` uses the existing cubic companion `M` and
the corrected generator `J₃ = (2M + I) / sqrt(3)`. It states and proves
`J₃² = -I` and `exp((2π/3) J₃) = M`. The companion is not orthogonal in the
standard Euclidean coordinates. It is not identified with the standard
rotation matrix by literal equality.

`Algebra/SplitCliffordOperatorModes.lean` works in associative rings and
native real matrices, not in a fictitious associative octonion algebra.
Anticommuting `B² = -I` and `K² = I` imply `(BK)² = I` and
`(θB + ξK)² = (ξ² - θ²)I`. The mixed square and the null exponential reuse
the existing analytic owner. The two off-diagonal null matrices have
anticommutator `I`; the complementary idempotents instead have zero mixed
products and are not interchangeable with those nilpotents.

`Algebra/MoebiusTraceInvariant.lean` uses `trace(M)² / det(M)`, which is
unchanged under nonzero scalar multiplication. Its intended projective
domain is invertible matrices. The diagonal representative with parameter
`2 + i` has determinant one and trace ratio `128/25 + (96/25)i`.
Its trace discriminant is therefore `28/25 + (96/25)i`.
This is an explicit nonreal example, not a proof of a four-class exhaustion.
The identity also has trace ratio four, so a parabolic classification must
exclude scalar representatives. Real matrices never have nonreal real-valued
discriminants.

The parameter `2i` gives trace ratio `-9/4` despite the induced projective map
being `w ↦ -4w`, a dilation with a half-turn. Nonreal trace ratio is therefore
not a necessary condition for dilation-rotation behavior. The proposed
four-way sign chart is not promoted to a classification theorem. Likewise,
`Mat₂(ℝ) ⊕ ℝ³ ⊕ (ℝ³)*` has dimension ten, not eight; the Zorn vector-space
carrier has two scalar diagonal entries and two three-vector entries.

These statements do not identify `M₂(ℝ)` with the eight-dimensional
split-octonions, prove CAR for four proposed octonionic generators, establish
a global Möbius classification, or derive mass, thermalization, detector
quantization, or Zitterbewegung. The rational group-algebra CRT decomposition
is into cyclotomic fields, not full matrix algebras. No CRT theorem is added
by these modules.

## Verification

`Algebra/ParabolicJordanZorn.lean` reuses the existing `NPart` shear. It adds
exact nilpotence index two for a nonzero parameter, the native Mathlib
eigenspace and its finrank one, eigenvector characterization, impossibility
of invertible diagonalization, the additive parameter law, and absence of
positive powers equal to the identity. No custom eigenvector predicate or
duplicate matrix carrier is introduced. The zero parameter is explicitly
excluded from the defective-Jordan statements.

This does not identify the additive shear group with a Galois group.
Artin–Schreier extensions require a positive-characteristic field and an
equation `x^p - x = a`; they are not consequences of a real square-zero
matrix. Reversing the parameter changes an upper shear into its inverse,
not into a lower shear. Quotienting `GL₂` by `{±I}` is not generally the
same as quotienting by all invertible scalar matrices to obtain `PGL₂`.

Companion regression examples and axiom reports are in
`Algebra/CyclotomicOperatorCorrectionsTests.lean`.
At authoring time the pre-existing full `lake build -R` held the shared lock;
no compilation success is claimed for these additions. A narrow owner build
was queued behind that lock. Run the following after the lane is available:

```bash
cat AGENTS.md >/dev/null
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Algebra.CyclotomicOperatorCorrectionsTests
```
