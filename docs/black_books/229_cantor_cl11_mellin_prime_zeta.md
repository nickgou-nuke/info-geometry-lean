# Chapter 229: The Cantor–Mellin Prime Gas — From Binary Profiles to Zeta Channels

## 1. Principle and guardrail

This chapter records a witness-gated architecture, not an RH proof corridor.

A finite binary word

- is an address (Cantor/cylinder side),
- is an occupation profile (Clifford/Fock side),
- becomes an arithmetic state after prime labeling.

The theorem-safe pipeline is:

```text
binary word / address
  -> finite occupation profile
  -> E(ε) = Σ ε_i log p_i = log N(ε)
  -> exp(-β E(ε)) = N(ε)^(-β)
  -> finite boson / fermion / parity-supertrace channels
  -> zeta / zeta-ratio / inverse-zeta channels (only with analytic witnesses)
```

This chapter does not prove:

- RH,
- analytic continuation,
- unconditional infinite Euler products,
- zero-location theorems from finite bit-lattice data.

## 2. Finite prime-bit Mellin identity

Given a finite binary profile ε with prime labels p_i:

- integer readout: N(ε) = ∏ p_i^{ε_i}
- logarithmic energy: E(ε) = Σ ε_i log p_i

So E(ε) = log N(ε), hence

exp(-β E(ε)) = N(ε)^(-β).

In this repo, this finite identity is the owner lane of:

- lean/InfoGeometry/Arithmetic/PrimitiveBinarySuperZetaBridge.lean

and is explicitly scoped away from RH/infinite-analytic claims.

## 3. Three finite trace channels (must stay separated)

The prime-gas surface has three distinct channels:

1) Bosonic trace:
   finite reciprocal-product channel (zeta channel in analytic limit)

2) Ordinary fermionic trace:
   square-free/product channel (zeta/zeta(2β) in analytic limit)

3) Parity supertrace:
   inverse-zeta/Weyl-denominator analogue channel

In this repo, this separation boundary is enforced by:

- lean/InfoGeometry/Canonical/PrimeGasPartitions.lean
- lean/InfoGeometry/Canonical/WeylCharacterEquivalence.lean

Critical correction:

- bosonic trace is the zeta channel,
- ordinary fermion trace is the zeta-ratio channel,
- parity supertrace is the inverse-zeta denominator channel.

## 4. Discrete Mellin/modular scaling lane

Discrete logarithmic/rapidity sampling and modular scaling are handled in:

- lean/InfoGeometry/Canonical/DiscreteMellinModularBridge.lean
- lean/InfoGeometry/Canonical/DiscreteModularMellinShift.lean

This gives the finite/discrete transport socket for Mellin-style scaling without
upgrading finite identities into analytic continuation claims.

## 5. Cantor/Clifford address interpretation

Local architecture allows reading the same finite binary data as address-layer
and occupation-layer data.

Caveat for indexed-main discussions:

- if Cantor/Cuntz files are not visible in the current remote index view,
  treat those as local/branch inputs unless confirmed under committed names.

When present locally, they remain interpretation/routing lanes, not independent
analytic proof authorities.

## 6. Zero socket (explicitly external)

Zero claims are witness-gated:

```lean
structure SpectralZeroLocationWitness where
  zeroCarrier : Type*
  zeroLaw : Prop
```

Any downstream zero theorem must import such a witness explicitly.
No finite profile theorem may silently imply zero locations.

## 7. Lean synthesis surface

Composed bridge file:

- lean/InfoGeometry/Canonical/CantorCliffordMellinPrimeGasBridge.lean

These are composition/routing surfaces that:

- bundle finite profile + Mellin + channel-separation witnesses,
- preserve no-RH/no-zero-derivation guardrails,
- keep analytic/zero claims external.

## 8. Reference hygiene note (Wakeham 2016)

Context note for
https://hapax.github.io/assets/2016-02-22-primons/ :

- This is useful heuristic/expository motivation for primon-gas and Möbius
  supertrace intuition.
- It is not an owner-proof source for Lean promotion in this repository.
- Theorem authority remains with repository owner lanes and explicit witness
  packets.

In particular, Wakeham (2016) should be cited as commentary/motivation, while
formal closure remains in:

- lean/InfoGeometry/Arithmetic/PrimitiveBinarySuperZetaBridge.lean
- lean/InfoGeometry/Canonical/PrimeGasPartitions.lean
- lean/InfoGeometry/Canonical/WeylCharacterEquivalence.lean
- lean/InfoGeometry/Canonical/DiscreteMellinModularBridge.lean

Final slogan:

The zeta channels are Mellin shadows of prime-labeled Clifford/Cantor
occupation profiles, and zero claims remain witness-gated analytic inputs.
