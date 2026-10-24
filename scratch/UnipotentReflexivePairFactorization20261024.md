# Unipotent reflexive-pair factorization

Uncompiled sandbox proposal; AA and serial QA required. No live edits/builds.

All statements use only an associative Ring A and primitive hypotheses on d,B.
No structures, carriers, global operator definitions or theorem packets added.

- `unipotent_triple_factorization` needs d*d=0 and d*B*d=d only.
- `unipotent_triple_mul_inverse` and `unipotent_inverse_mul_triple` need only
  d*d=0 and B*B=0. They give both ordered inverse products with the literal
  reverse/sign-flipped triple; reflexivity is not needed for invertibility.
- `support_square`, `support_mul_skew`, and `skew_mul_support` use both
  square-zero and both reflexive laws, with explicit ordered ring products.
- `skew_square` needs only the two square-zero laws.
- `ambient_skew_square` proves W*W = 1-2*(d*B+B*d) for the literal ambient
  expression W=1-d*B-B*d+d-B, using the named support identities.
- `ambient_skew_fourth` derives W^4=1 from that square and support idempotence.

Source comparison: `Algebra.CayleyPeirceKANUnipotentBridge` already proves the
two one-factor inverse identities in a conjunction. The candidate does not
import that broad owner for these elementary local ring calculations.
`Canonical.GrassmannianBundleCyclotomicOrientability` has active-support
identities and an ambient symmetric reflection. It is deliberately not an
import dependency here, as requested; the helpers are short explicit proofs.
`Singular.SquareZeroMoorePenrose` can supply the primitive hypotheses for an
actual MP pair, but these lemmas do not require star or MP assumptions.

W^4=1 is not exact order four; zero pairs, trivial rings and characteristic two
are permitted. No G2, Klein, Spin/Pin, octonion-automorphism or projective action
claim is made. Raw nonassociative multiplication is outside the Ring contract.

QA should check the associativity-only inverse cancellations and noncomm_ring
rewrites against the named support identities. No compiler evidence claimed.
