# Finite Jordan–Wigner transmutation: corrected native formalization

## Contract

For an arbitrary associative `Ring A`, a family of normalized square-zero pairs
`d B : Fin N → A` commuting at distinct sites produces dressed CAR generators
and split-signature Majorana generators. No commutativity of `A`, characteristic
restriction, finite-dimensional ambient representation, or invertibility of two
is assumed. Star conclusions additionally require `[StarRing A]` and
`∀ j, B j = star (d j)`.

The universal-algebra layer works over any central coefficient ring
`[CommRing R] [Algebra R A]`. Every arbitrary ring is covered by taking `R = ℤ`;
no real/complex scalar structure is imposed on the general theorem.

The user's ordinary `Finset.prod` cannot define the string under `[Ring A]`:
it requires a commutative multiplicative monoid. The replacement uses native
`Finset.noncommProd` on `Finset.Iio j`, supplied with the proved pairwise
commutation of local parities. Because those factors commute, no arbitrary
ordering convention affects the product.

## Owners

- `lean/InfoGeometry/Core/BosonParityString.lean`
  - Local input relations, actual parity actions and `Γ = 1 - 2 B d`.
  - Native noncommutative products, commutation, square-one, and string signs.
  - Both square-zero laws and all same-/mixed-type CAR relations.
  - Preservation of local products and parity.
  - Reconstruction of the string from the **output** commutators, followed by
    recovery of both original modes (`recover_modes`). No division by two.
- `lean/InfoGeometry/Core/BosonMajoranaFermionTransmutation.lean`
  - Reuses `DiracSuperalgebra.majoranaPlus` and `majoranaMinus`.
  - String formulas, doubled chiral identities, squares `+1`/`-1`, all
    requested anticommutators, and `γ⁻ γ⁺ = Γ`.
  - Self-adjoint parity/string, adjoint creation/annihilation, self-/skew-adjoint
    Majoranas under explicit duality.
  - Connection to the existing four-equation `IsMoorePenroseInverse` owner.
  - Naturality of products, dressed modes and Majoranas under native unital
    ring homomorphisms, including transport of the input relations.
- `lean/InfoGeometry/Core/AnticommutingSum.lean`
  - Finite square and mixed-CAR sum formulas, without cancellation of two.
  - Native basis extensions satisfy the required quadratic identities on
    **all vectors**, not just on basis generators.
- `lean/InfoGeometry/Core/BosonCliffordExterior.lean`
  - Actual native `ExteriorAlgebra R (Fin N → R) →ₐ[R] A` maps for each of
    the annihilation and creation families.
  - Actual native `CliffordAlgebra Q →ₐ[R] A` for the weighted split form
    `Q(x,y) = ∑ xᵢ² - ∑ yᵢ²`.
  - Basis-generator evaluation, uniqueness from those generators, and
    naturality of the whole algebra homomorphisms under native `AlgHom`s.
- `lean/InfoGeometry/Core/BosonCARRepresentation.lean`
  - Actual native `CliffordAlgebra (QuadraticForm.dualProd R (Fin N → R)) →ₐ[R] A`.
  - Uses the native dual module and `Q(φ,v) = φ(v)`, valid in characteristic two.
  - Both CAR families are the images of the two isotropic sectors.
  - Generator evaluations, uniqueness from the two bases, and full-algebra
    naturality are proved.
- `lean/InfoGeometry/Core/BosonFermionRegression.lean`
  - Actual input systems at **every finite N**, acting as native endomorphisms
    on functions on bit configurations, over any commutative coefficient ring.
  - Nonzero local modes over nontrivial coefficients.
  - Characteristic-two coincident Majoranas but nonzero dressed modes.
  - A nonzero matrix input system satisfying the additional star hypothesis.
  - Distinct neutral-Clifford CAR images in characteristic two, despite
    coincident Majoranas.
  - Equality of the generic real split form with the existing
    `Algebraic.SplitSignature.splitQuadraticForm` owner.

`lean/InfoGeometry/Core/All.lean` imports the regression entrypoint, which
imports all five owners. Existing categorical/matrix Jordan–Wigner constructions
are preserved; these examples do not replace the general ambient carrier.

## Interpretation corrections

Square `+1` means involutive, not generally unipotent. Square `-1` is a
split-signature Clifford relation; without scalar structure it should not be
called a real or complex representation. Non-nilpotency additionally requires
a nontrivial ring. In characteristic two the signs coincide, and the doubled
chiral formulas cannot be inverted to recover modes from Majoranas alone.

The inverse proved here reconstructs an input system from its dressed outputs.
Naturality is proved for ring homomorphisms and for the lifted algebra
homomorphisms; no additional category presentation is asserted. The actual
exterior and Clifford representations are now constructed, not merely inferred
from generator labels. Faithfulness, surjectivity onto the ambient algebra, a
central-extension construction, physical spin–statistics transmutation, and
continuum passage are not asserted.

## Verification

Pinned Lean v4.34.1, 2026-10-23. Serialized through the shared build lock:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Core.All
```

PASS, 3818 jobs. Log: `/tmp/boson-native-core-final.log`.
All six task Lean files are warning-free; existing dependency warnings remain,
including the real split-form owner's deprecated import.
No full-superproject default-target build is claimed.

`tools/infra/axiom_check.lean` replayed and transitively audited every declaration
in the six task module artifacts: **52 + 33 + 8 + 28 + 18 + 14 = 153**, all PASS.
Log: `/tmp/boson-native-axioms-final.log`. Allowed foundations only:
`propext`, `Classical.choice`, `Quot.sound`.
Source-aware admission/unsafe scans and staged whitespace checks also pass.
Independent A-A and QA-A replay on 2026-10-24 confirmed the same six source
hashes and all 153 declarations. Receipt:
`/tmp/qa-a-jw-signed-final-h6mysqex/result.json`.

SHA-256 (relative to `lean/InfoGeometry/Core/`):

```text
8b428d4b6af4108aec1eb7367e2e5bb61e84b43bf230edcca53a777e29b3f284  BosonParityString.lean
5a58d060e0b569db8f04b8f0d96f3463ae85fb98816bd68b9f7a99c5571a5f42  BosonMajoranaFermionTransmutation.lean
c4c565e790ab8496e1ed8ff1c1798fe0951903d88b1704ca713a8e0df8f31fd2  AnticommutingSum.lean
8054acdf9f9d35a2edec4d538bcb3034144eb0904069c9b9f0dcaaa4f9122e3f  BosonCliffordExterior.lean
a6689b484fe5f58ba7c4694bf591d9715642db217d1752c262067156819cbdf0  BosonCARRepresentation.lean
760fcdd64939a6803d8e1ec2888bea3167d17f8489fbdada51cecdfda7531d4d  BosonFermionRegression.lean
```

## Final independent replay, 2026-10-24

Two additional noncommutativity lemmas bring the six-owner count to 155. The updated regression owner has 16 axiom-clean declarations.
The five rechecked owners passed with 81 declarations total. Exact Core.All and
InfoGeometry.All builds passed (9011 and 26980 jobs respectively), with stable
seven-source/pin hashes and no scoped warnings. Existing imported warnings remain.
Receipt: `/tmp/qa-a-catto-retry2-j1uswpr6/result.json`. Aggregate compilation is not an all-imported-declaration
axiom audit or clean-release certification.

Current selected source hashes:

```text
dbaedda7dd9de84e39a68b9fde31379881b74c80f643b9353d381dc505cf72b3  lean/InfoGeometry/Canonical/CattoGurseySplitBasis.lean
f96eaddc904397bd2caf18e06490d2547675898abeb818cd9b8d85b95367ddad  lean/InfoGeometry/Canonical/CattoGurseyBlockGrading.lean
6ca073eca2f944438c242a075f59899b33b59b85a9b83dd7377d98cdbba7bd3f  lean/InfoGeometry/Superalgebra/CattoGurseyOctonionicHadronicSuperalgebra.lean
2d6caf71e4674dc8788b7adffdadf91040790f8d310597480ba2bc5f761e7133  lean/InfoGeometry/Core/BosonFermionRegression.lean
cc902922dd30965ef0ddfa2ed68f501ecdefa1ab6bbc03faeed89c81604ce8c9  lean/InfoGeometry/Core/NilpotentCartanRegression.lean
7f6fcf1befcfab57bb3a4ffe11f0855fb4248302e178171e4c2c8044406f16ac  lean/InfoGeometry/Core/All.lean
fbe04fa6993ead97420c2393e0fe11716accfe5f3a34dad5691a0762c2e11fa1  lean/InfoGeometry/All.lean
```

## Native finite pairing implementer

`OperatorAlgebra.FinitePairingImplementer` derives the pair-occupancy support
and finite circular conjugation directly from ten primitive two-mode CAR laws.
For `T = q*p - P*Q` and `Pi = (q*p)*(P*Q) + (P*Q)*(q*p)`, it proves
`T*T = -Pi`, support idempotence/absorption, and the inverse defect of
`1 + (c-1) • Pi + s • T`. Normalization `c*c+s*s=1` produces a native unit
with both inverse laws. Four separate theorems compute the actual generator
sandwiches, with no division by two or assumed output actions.
The construction is algebraic; it does not assert star preservation, a full
Spin/Pin classification, or an analytic implementability theorem.

The promoted owner passed independent A-A and QA-A: all 29 declarations are
axiom-clean and warning-free. Receipt:
`/tmp/qa-a-pairing-promoted-lsctdd8_/result.json`.
The same replay checked the final Boson regression owner (20 declarations,
including reused named rational matrices), so the six Boson owners now total
159 declarations. The changed BlockGrading header was also replayed (12).
Current promoted source hashes:

```text
2e4fae77b0abe6a007bca34f598cbcc851b582fbf89fe943cde538e57852aa2f  lean/InfoGeometry/OperatorAlgebra/FinitePairingImplementer.lean
e6e98675624cbe71c632bffbee8220e2ef49d1c3f07e498754c44d0a7ab74a23  lean/InfoGeometry/Core/BosonFermionRegression.lean
8b0549bf2306d5b00d7e92fe2f252ea43dcec99cae348e269480025e5cc09a9b  lean/InfoGeometry/Canonical/CattoGurseyBlockGrading.lean
```
