# Represented finite-seed density exponential v7

Source-only repair; independent AA and locked QA required. No builds or live edits.
V6 and all earlier candidates are preserved.

## Exact failure and repair

The terminal log `/tmp/qa-a-finiteseedrepresenteddensityexponential20261024v6-7buo_11y/compile.log`
reports header synthesis failures for `HSMul ℝ SeedClosure ?m` (line 67) and
`Monoid SeedClosure` (line 74). These occur before the two proof bodies.
V6 result-type annotations did not resolve them.

V7 adds two local structure selections BEFORE both statements:

* `seedClosureMonoid` is the `toNormedRing.toRing.toMonoid` projection of
  `representedCStarClosureCStarAlgebra` at the actual finite-seed family.
* `seedClosureRealSMul` is the `toSMul` projection of the existing
  `Algebra.complexToReal`, with its carrier, Semiring and complex Algebra
  arguments explicitly supplied from that same native closure CStarAlgebra.

Both exponential arguments use `@SMul.smul ℝ SeedClosure
(seedClosureRealSMul H hH β)` explicitly. This eliminates heterogeneous scalar
result inference at the failing syntax, rather than adding another outer type
annotation. Inverse coercion still first inverts the actual represented density
unit in `SeedClosureˣ`, then coerces its value into SeedClosure.

## Source-backed structure selection

* `Canonical/FilteredGNSRepresentedCStarClosure.lean:46–59`: represented closure
  is the native closed StarSubalgebra of bounded operators; its CStarAlgebra is
  `StarSubalgebra.cstarAlgebra`.
* Mathlib `Analysis/CStarAlgebra/Classes.lean:38`: CStarAlgebra extends NormedRing
  and NormedAlgebra ℂ on the same carrier.
* Mathlib `Analysis/Normed/Module/Basic.lean:274`: NormedAlgebra extends Algebra.
* Mathlib `LinearAlgebra/Complex/Module.lean:174`: Algebra.complexToReal is the
  standard `Algebra.restrictScalars ℝ ℂ A` instance.

These are native projections/restriction, not replacement norm or carrier data.
The local real action selects the same restriction used by the generic helper;
QA must still confirm definitional alignment at concrete application.

## Preserved mathematical contract

For every finite seed stage k, Hermitian H and every real β, prove that the
existing representedDensityUnit has value exp(-β • seedStageHom(H)), and its
actual unit inverse has value exp(β • seedStageHom(H)). Both proof bodies
still consume the accepted native FiniteMappedGibbsDensityExponential theorems.
No positivity restriction on β, extra assumption, changed state, alternate
unit, new theorem wrapper, budget increase or transparency change.

No claim that elaboration succeeds until independent QA. This is not by itself
an analytic KMS/strip-bound theorem.
