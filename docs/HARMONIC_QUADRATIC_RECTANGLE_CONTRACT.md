# Harmonic quadratic rectangle means

Carrier: the existing `HarmonicRectangle.rectangleIntegral`, an iterated
real interval integral of a field on `ℂ`. The owner already computes the
field `Re(z²)` and proves its center-mean criterion for positive half-sides.
The extension treats `Re(a*z²+b*z+c)` for arbitrary complex coefficients.

Contract: prove harmonicity, the exact rectangle integral, and (for positive
half-sides `w,h`) average `c.re + a.re*(w²-h²)/3`. The average equals the
center value iff `a.re=0 ∨ w=h`. This includes mixed `xy` terms and affine
terms. It does not assert a rectangular mean theorem for all harmonic
functions, nor classify all harmonic functions as quadratics.

Source discovery: maintained Lean searches for `rectangleIntegral`,
quadratic/rectangle combinations, and harmonic/quadratic combinations found
the integral owner and its tests and aggregate imports. Other harmonic
normal-form hits use different carriers, not this rectangle integral.
The proof uses native interval integration and analytic harmonicity;
no replacement integral or surrogate field is introduced.

Parent locked verification passed (session 66904, 3547 jobs,
`/tmp/harmonic-quadratic-audit.log`): seven new named lemmas, eight axiom
reports including the original counterexample, and three examples. The
transitive axiom union is `[propext, Classical.choice, Quot.sound]`.
No warnings originate in the new owner or audit; eight dependency-source
warnings and two package notices remain. Strict screening reports zero
traps. Independent semantic review passed. Independent kernel QA passed
(session 11264, 3547 jobs, `/tmp/harmonic-quadratic-qa.log`), confirming all
eight standard-axiom reports, three examples, zero own-source warnings,
zero strict-screen traps, and clean scoped diffs.
