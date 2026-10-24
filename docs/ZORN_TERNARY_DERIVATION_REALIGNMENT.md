# Standard-derivation replacement for the associator fundamental identity

The raw Zorn associator is not a Filippov bracket. The existing owners
`Algebra/ZornPeirceMixedAssociator.lean` and
`Algebra/ZornAssociatorFilippovObstruction.lean` give explicit defects.
The constructive replacement retains the native canonical split-octonion
carrier and uses the already defined `splitThreeBracket` in
`Lie/SplitOctonionStandardDerivationThreeBracketBridge.lean`.

That operation is `T(x,y,z) = D(x,y)(z)`, where the standard derivation has
the proved normal form

    D(x,y)(z) = [[x,y],z] - 3 ((xy)z - x(yz)).

`Lie/SplitOctonionStandardDerivation.lean` owns the normal form and the
constructed derivation. `Lie/CanonicalZornStandardDerivationCovariance.lean`
already proves its covariance. The new `Lie/SplitOctonionThreeBracketCovariance`
exposes the consequence through the existing ternary API:

    D(T(u,v,w)) = T(Du,v,w) + T(u,Dv,w) + T(u,v,Dw).

Specializing to the proved derivation `D(x,y)` gives

    T(x,y,T(u,v,w)) = T(T(x,y,u),v,w)
                    + T(u,T(x,y,v),w) + T(u,v,T(x,y,w)).

No extra derivation assumption is imposed on the specialization. This proves
the ternary derivation identity; it does not assert total alternation,
identify T with the raw associator, or construct a Nambu–Poisson algebra.
The raw associator obstruction and this replacement are compatible statements
about different, explicitly specified operations on the same algebra.

Search evidence: recursive source searches in `lean/InfoGeometry`, followed by
`lean`, `lib`, `scratch`, and `proofs`, found the covariance owner and both
Algebra/Lie ternary interfaces. Their definitions and imports were inspected.
This is a local classification of the associator claim, not a repo-wide
absence or completion claim. The Algebra interface uses AbstractKingdon;
this extension consumes the Lie interface on the canonical Zorn carrier.

Parent verification: session 19487 exited zero, 3127 jobs, log
`/tmp/zorn-three-bracket-covariance-audit.log`. Both new declarations report
exactly `propext`, `Classical.choice`, and `Quot.sound`; no warnings originate
in the two new modules. Independent semantic review passed. Independent QA
session 38925 exited zero with 3127 jobs, two standard-three axiom reports,
zero own-source warnings, and zero strict-screen traps. Its log is
`/tmp/zorn-three-bracket-covariance-qa.log`.
