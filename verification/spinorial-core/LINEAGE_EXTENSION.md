# Lineage extension: exact mathematical scope

These modules continue the corrected core from commit
`7b34cb71d0c8801b7456419a456b5bba66057373`. They extract algebraic constructions
from the two October 2 lineage notes, without treating their historical narrative
or their proposed physical resolutions as premises.

## 1. Jordan / nonassociative algebra: derivations act associatively

`BilinearDerivations.lean` starts with an arbitrary bilinear product
`V →ₗ[R] V →ₗ[R] V`. It assumes neither associativity nor alternativity. It proves
that Leibniz endomorphisms are closed under the commutator, constructs their
native `LieSubalgebra R (Module.End R V)`, and constructs its faithful inclusion
representation and the Lie stabilizer of a chosen vector. For a genuine
idempotent it derives the linearized idempotent equation.

This is a representation of the derivation Lie algebra. It is not a
multiplication-preserving embedding of the original nonassociative algebra into
an associative matrix algebra. No G2 or compact-gauge classification is claimed.

## 2. Dirac / Krein: adjoints, actual exponentials, and probability distinctions

`KreinAdjoint.lean` proves the fundamental-symmetry adjoint laws, the equivalence
of `U† J U = J` and `U♯ U = 1` when `J² = 1`, composition of isometries, and closure
of the skew operators under commutators. The involution theorem explicitly
requires `J† = J`. A rational 2-by-2 boost preserves an indefinite signature but
is not orthogonal for the positive metric.

`KreinExponential.lean` uses mathlib's actual matrix exponential and its unit
conjugation theorem. It proves that the exponential of a Krein-skew matrix
preserves the indefinite form, including a concrete real-parameter spinorial
boost generator with off-diagonal entries 1/2.

`KreinIncidence.lean` recovers the positive pairing by inserting `J` a second
time: `[x,Jy] = x†y`. The positive squared norm is distinct from the indefinite
quadratic value. This is not a construction of a physical scattering operator,
a positive physical-state quotient, or a self-adjoint boundary-value problem.

## 3. Wheeler / Kerr: the realization has not been supplied

No metric quotient or field-equation solution identifying a Kerr disk with a
Klein crosscap is introduced. No gyromagnetic ratio, electron charge, form
factor, or soliton stability is inferred from the finite algebraic results.
Those require separately specified geometric and dynamical constructions.

## 4. Cartan / torsion: the realization has not been supplied

No Nieh-Yan-to-Chern-character comparison, Pin bordism classification,
regularized anomaly calculation, or focusing/stability theorem is asserted.
The previously checked Smith-group primary decomposition and obstruction to a
surjection onto `ZMod 16` remain unchanged.

## 5. Penrose / incidence: the Hermitian real-slice calculation

`KreinIncidence.lean` defines `metricDual J x : Module.Dual ℂ (n → ℂ)` by
`y ↦ x† J y`. This is complex-linear in `y` and antilinear in `x`. It proves
invariance under Krein isometries and invariance of nullity under nonzero complex
scaling. The exact witness `x = (1,i)`, `J = diag(1,-1)` satisfies
`x†Jx = 0`, has positive squared norm 2, and satisfies `xᵀJx = 2`.

This does not identify the full complex ambitwistor space with that real slice,
construct a projective manifold, or prove an amplitude-reconstruction theorem.

## Flavor: an independent, actual unitary-matrix result

`MixingInvariant.lean` defines the imaginary quartet
`Im(a*d*conj(b)*conj(c))`, proves its invariance under independent unit phases on
both rows and columns, and proves two-dimensional vanishing from row
orthogonality. An exact rational-complex 3-by-3 unitary witness has quartet
`5184/78125`, while the identity matrix has quartet zero.

Consequently three-dimensional mixing permits, but does not force, a nonzero
quartet. The module neither chooses a generation count nor equates the quartet
with an octonionic associator.

## Verification

The existing isolated `InfoGeometry.Canonical.SpinorialCore.All` target imports
all five new modules along with the original nine owners. The axiom audit is
extended from 14 to 36 selected declarations. The toolchain and mathlib revision
are unchanged. Consult the final build metadata accompanying the delivered
source bundle for the checked commit and workflow result.
