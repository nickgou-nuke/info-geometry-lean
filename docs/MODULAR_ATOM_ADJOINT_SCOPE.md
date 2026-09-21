# Modular atom: adjoint compatibility

`Synthesis/ModularAtom.lean` reuses `Cl11Atom` from
`Canonical/PrimeCl11ModularAtomCore.lean` and `KasparovKreinData` from
`Physics/KreinDiracKasparovSpinorBilinear.lean`. No replacement class is added.
The former already supplies the split-square identity for `c * d`.

The bridge proves that conjugation by `c` negates that parity element.
With `star c = c` and `star d = -d`, the parity element is star-self-adjoint
but **Krein-skew-adjoint** for metric `c`. The metric identification with the
existing Krein data is an explicit compatibility hypothesis.
The genuine Krein adjoint reverses multiplication and preserves commuting
pairs in both directions.

These statements do not identify the adjoint with Tomita modular conjugation,
construct modular flow, or identify an algebra with its commutant. Neither
the general tensor-product isomorphism in the supplied narrative nor its
physical interpretations follows from these finite algebraic lemmas.

In the supplied class, `krein_adj` is an overridable field default, not a
definitional constraint on every instance. It also omits `star`. The bridge
instead uses the owner's actual definition `eta * star operator * eta`.

Compilation is pending behind the existing full build. The focused target is
`InfoGeometry.Synthesis.ModularAtomTests`; no compilation success is claimed.
