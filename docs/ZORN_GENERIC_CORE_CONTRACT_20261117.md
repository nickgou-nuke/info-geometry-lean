# Projected Zorn dissipation, an entropy coordinate, and a cored profile

## Intake and authority

The initiating attachment is preserved byte-for-byte in
`docs/ZORN_GENERIC_CORE_INTAKE_20261117.md` (SHA-256
`e86035703fb4a51469223dc1b5b5b2ff94b9a82a51d1feaf6d32c68cbdb5ad85`).
It proposes algebraic and analytic repairs to the cosmological and Zorn
associator discussions, together with interpretations and verification claims.
The preserved text is intake, not a source of mathematical axioms.

Base: `08c34e03f610b452e03422037949196dc7d92d6d` in
`nickgou-nuke/info-geometry-lean`. Lean and Mathlib pins are unchanged.
This task adds a branch separate from the published operator-exponential work.

## Exact prerequisites from open draft PRs

The following source owners were retrieved at immutable heads and checked
against their Git blob IDs before integration. The prior PRs remain separate
review surfaces; their prose status does not establish compiler acceptance.

| Source | Immutable head | Owners reused |
|---|---|---|
| [PR #382](https://github.com/nickgou-nuke/info-geometry-lean/pull/382) | `f09221ddd5ddaa75a77e4e765da975e33dffafdd` | `Physics/CanonicalScalarStress`, `Physics/ScalarKineticBalance`, `Physics/SphericalMassProfile` |
| [PR #384](https://github.com/nickgou-nuke/info-geometry-lean/pull/384) | `6a0971cfb93e614ecccd29a44274f9bbf98706ae` | `Algebra/ZornAssociatorGram` |

All four owner names above are relative to `lean/InfoGeometry/` and have the
`.lean` extension. They are included because their PRs are not merged into the
base. Compiler repairs, if needed, will be documented in the verification note.
The existing effective-pressure theorem is reused directly, without a new
alias masquerading as a new result.

## Mathematical contract

### 1. Project the probe variables in the actual Zorn algebra

Carrier: the existing eight-dimensional real `ZornVectorMatrix`, with its
actual nonassociative product, multiplicative quaternion embedding, signed
basis, and positive coefficient pairing. The split multiplicative norm is not
used as a positive form.

`Algebra/ZornQuaternionProjectedGram.lean` constructs the linear retraction
and orthogonal projection onto the existing quaternion range. It retains all
64 ordered signed-basis pairs and projects both probe slots in the associator.
It proves symmetry, nonnegativity, and the exact quadratic and bilinear kernels
as the quaternion range, together with its real dimension four.

The single ordered pair of quaternion units `(i,j)` detects all four
complementary coordinates. In the existing right-product convention,
`[q * ell, i, j] = 2 * ((q * k) * ell)`. The parentheses and multiplication order
are part of the statement. An `E11` witness and the ambient/projected contrast
at quaternion `i` establish that the two positive forms have different kernels.

### 2. Convert the Gram form to a covector-to-vector operator

A bilinear form has variance `Z → Z*`; a GENERIC mobility has variance
`Z* → Z`. `Algebra/ZornGramDissipation.lean` constructs the dual equivalence
`e : Z ≃ₗ[ℝ] Z*` from the positive coefficient pairing and its finite basis.
It defines `D_B = e⁻¹ ∘ B ∘ e⁻¹` and proves the actual evaluation formula
`phi (D_B psi) = B (e⁻¹ psi) (e⁻¹ phi)`.

The ambient and projected forms therefore give genuine symmetric positive
covector operators. Their kernels and quadratic zero sets are transported
through this constructed duality, not assumed through an unnamed metric.

### 3. Adjoin a nonzero entropy differential

`Thermo/GenericEntropyExtension.lean` works over any real module `V` with
arbitrary operators `L,D : V* →ₗ[ℝ] V`. The assumptions are skewness of `L`,
symmetry and positivity of `D`, an energy differential `h`, and temperature
`T > 0`. No commutation, finite dimension, or invertibility of `D` is assumed.

On `V × ℝ`, it constructs `E(v)=(v,0)`, `C(v)=(v,-h(v)/T)`,
`Ltilde=E L E*`, and `Mtilde=T⁻¹ C D C*`. The existing native
`GenericMetriplecticFlow.System` is populated with proofs of both strong
degeneracies, skewness, symmetry, and positivity. The entropy differential
`dS(v,s)=s` is nonzero. If `L` is injective, the extended reversible kernel is
exactly its span.

The exact rates are `zdot=Lh-T⁻²Dh` and `sdot=T⁻³ h(Dh)`. At `h=0`, the full
flow vanishes while the friction map remains defined on every covector.
The temperature denominators are explicit. There is no division by an
energy-gradient norm.

`Thermo/ZornEntropyExtension.lean` supplies the integration construction: an
explicit injective skew reversible map on the actual Zorn vector space,
combined with both Gram mobilities and exact entropy-production zero sets
through the scalar and quaternion kernels. This dependency requires
both the Gram-to-dual construction and the entropy-coordinate construction.

These are pointwise linear systems. A state-dependent Poisson Jacobi identity,
contact geometry, evolution existence, and integrated Landauer inequalities
require additional constructions and are not inferred from the `System` type.

### 4. Derive a finite core from an explicit mass function

`Physics/CoredSphericalMassProfile.lean` reuses the original profile owner.
For `Mc(r)=2 eta s r^3/(r+s)^2`, it proves its native `HasDerivAt` derivative,
defines density using that derivative divided by `4 pi r^2`, and proves on
positive radii

`rho_c(r)=eta s (r+3s)/(2 pi (r+s)^3)`.

For `s>0`, the positive-radius central limits are
`Mc(r)/r^3 → 2 eta/s` and `rho_c(r) → 3 eta/(2 pi s)`.
At infinity, `r^2 rho_c(r) → eta s/(2 pi)` and the spherical circular-speed
expression tends to `2 G eta s`. Density positivity also requires `eta>0`.

The raw quotient at zero is not identified with its nonzero limiting value.
This profile is prescribed; no field equation, uniqueness, or empirical fit is
claimed.

### 5. Retain an explicit singular native spinor

`Clifford/SingularSpinorCurrent.lean` uses the existing native
`HestenesCl14.Cl14 = CliffordAlgebra Q14` on `Fin 4 → ℝ`, signature `(+---)`,
and its even subalgebra. For `psi=1+gamma1*gamma0`, its theorem targets are nonzero even membership,
`psi*reverse(psi)=0`, and the actual current sandwich
`psi*gamma0*reverse(psi)=2*(gamma0+gamma1)`, which is nonzero and squares to zero.
This explicit counterexample does not assume a package of Fierz identities.

It does not establish all-spinor Fierz classification, a particular Lounesto
subclass, an observer-independent positive energy density, or a quantum field
energy inequality.

## Corrections to the intake

| Intake claim | Exact disposition |
|---|---|
| Equal temporal/spatial quadratic contributions are radiation; zero mean stress is dust. | The proved statements are trace relations. Perfect-fluid isotropy and a dust model need further hypotheses; the zero-stress equivalence requires nonzero coupling. |
| Every pair of noncollinear stress dyads fails to commute. | False: orthogonal nonzero vectors provide commuting dyads. Retain the actual existing noncommuting witness. |
| `M~r^alpha` can be differentiated into the density asymptotic. | Derivative control is additional. The new result differentiates the exact rational mass. `O(r^3)` alone is not sufficient for a finite central density. |
| The extended friction matrix is denominator-free or polynomial in temperature. | It contains powers of `T⁻¹`, with `T>0`; it avoids only energy-gradient denominators. |
| Projecting basis pairs amounts to selecting two projected basis elements equal to `i,j`. | The projected eight vectors need not be a basis. Native bilinear basis extensionality extends all 64 tests to arbitrary projected probes before choosing `i,j`. |
| A Gram form can be inserted directly as a GENERIC operator. | An explicit duality changes both variances. The adapter constructs and verifies that conversion. |
| Skewness proves all Poisson/contact/global GENERIC claims. | The constructed type proves pointwise algebraic laws. Jacobi, manifold structures, and global dynamics are separate. |
| The proposed repairs uniquely complete the physical theory because a finite poset has a top. | No such uniqueness implication follows. Only actual Lean imports and proved maps form the mathematical dependency graph. |
| A pending build lock is a permanent mathematical obstruction. | It is an execution state. Fresh compiler and axiom results determine verification status. |

## Validation contract

Use the pinned Lean runtime and pinned initialized Mathlib with the maintained
`tools/quality/check_clifford_dirac.py` source-closure and complete declaration
audit. Compile and audit every new and imported prerequisite owner. Require
zero warnings for changed owners and only `propext`, `Classical.choice`, and
`Quot.sound` in the audited axiom footprint. Preserve initial failures and
repairs separately from final acceptance.

Run independent semantic review, source/debt checks, the installed pre-commit
hook, and the unchanged pre-push gate on the final exact commit. Report the
root Lake integration outcome separately from focused native acceptance.
The verification note records observed commands, source identity, counts,
warnings, and remaining limitations; this contract alone is not proof evidence.
