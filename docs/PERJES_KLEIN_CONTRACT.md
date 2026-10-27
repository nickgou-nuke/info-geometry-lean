# Perjes particle theory and Klein glide integration

Source: Z. Perjes, Introduction to Twistor Particle Theory, KFKI-1980-76,
sections 3--6. The separate Klein glide/Pin extension is requested by the user;
it is not attributed to that report. Base: PR #228 at d6d7a86cf5cadef212082e879605390f0fafaea8.

The native PenroseIncidence, PenroseTwistor, InfinityTwistor, polynomial CCR,
SpinorOuterProduct and Klein deck owners are reused. The source convention is
omega=-i X pi, while the existing incidence uses +i. The actual equivalence
changes the sign of the upper block. The diagonal Hermitian frame is related
to the off-diagonal incidence frame by an actual linear equivalence, with a
factor-two metric normalization; physical helicity is half the incidence norm.

The contravariant infinity map is an independent dual-to-vector map, not the
inverse of the degenerate covariant infinity twistor. The symmetric kinematic
tensor is distinct from the antisymmetric Pluecker bivector. Its momentum and
angular readouts retain the epsilon and i conventions.

Verification is pending. The scoped checker compiles exact, unmodified sources
in the selected dependency closure against the repository pins and audits all
owned declarations transitively. This is not a root package build and does not
reuse the parent's diagnostic verification as evidence for the new additions.
No dependency pins are changed. The upstream contour/cohomology correspondence
and particle classification must not be replaced by assumed conclusion fields.

A glide is an affine map whose square is a translation. Its derivative reverses
orientation. A spinor lift needs additional Pin data; the sign of its square
is not implied by the base glide. On the nonorientable base this is a Pin lift,
not an ordinary Spin structure. Constant deck representations supply flat
monodromy data; they are not curvature-derived Berry phases without a connection.
