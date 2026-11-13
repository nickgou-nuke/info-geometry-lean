# Two-sided localization and endogenous Peirce operators

## Provenance and validation state

The exact user intake is preserved in
`docs/intake/SANDWICH_LOCALIZATION_20261113.txt` (27,735 UTF-8 bytes;
SHA256 `274ccf61f1feae41668aa6dbc6873b42804207957d63aec009e533a137a43c2b`).
The original uploaded name was `Pasted text(20261113-111516).txt`.

Dependency base: PR #334, `formalize/peirce-kernel-localization`, immutable
commit `b76d9e1e6da2ba8c1d7505ca791ef81c57d0db92`. This extension does not
assume that PR #334 or PR #352 has merged. Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` are unchanged.

At proof commit `436cdbed57deb267d6e90c2040d8ad5db57d52bf`, all nine selected
mathematical owners and their complete 38-module repository-source import closure
compiled successfully with the pinned toolchain. The native ownership audit checked
355 distinct declarations, covering all 162 named theorem/lemma declarations,
including all 15 private theorems. The union of transitive axiom dependencies was
exactly `propext`, `Classical.choice`, and `Quot.sound`. Independent semantic
readback confirmed that all nine integrated sources were byte-identical to the
reviewed snapshots.

This is acceptance of the exact focused mathematical sources. Whole-repository
acceptance remains withheld: the broader root gates have not passed. The
[verification report](SANDWICH_LOCALIZATION_VERIFICATION.md) records the immutable
execution identity, source hashes, coverage, warnings, and root-gate state at its
stated observation time.

## Formal intent

Construct a two-sided additive localization of the original arbitrary
associative ring, with a faithful ambient embedding under regularity and the
actual localized centralizer acting on both sides,
and connect its involution and Cayley action to the already owned Peirce seed.
Construct the corrected residual bridge as a polynomial in the original cut
and single coupling. Prove the generic elliptic twist identities and their
explicit real 8 by 8 instance.

The generic carrier is `[Ring B]`; involution results add `[StarRing B]`.
Neither ambient commutativity nor a diagonal representation is imposed.
The concrete matrix carrier is `Matrix (Fin 8) (Fin 8) ℝ`, separately labeled.
All noncommutative numerator orders are retained.

## Source-grounded owners and contracts

### 1. Native two-index additive localization

Owner: `InfoGeometry.Algebra.SandwichLocalization`.

For an arbitrary `s : B`, use Mathlib's `DirectLimit` of the additive groups
indexed by `ℕ × ℕ`, with transition

`x ↦ s^(j₁-i₁) * x * s^(j₂-i₂)` for `i ≤ j`.

The construction itself needs no regularity. It inherits native additive group
and integer-module structure. Explicit stage formulas prove addition,
denominator enlargement, eventual equality, and the universal property for
compatible additive cocones. Under left and right injectivity of multiplication
by `s`, every stage map is injective, and equality is exactly

`[k,x,l] = [k',y,l'] ↔ s^k' * x * s^l' = s^k * y * s^l`.

This is the faithful form of the submitted cross relation. The raw relation
is not declared an unconditional equivalence relation for singular denominators.

### 2. Native localized bimodule actions

Owner: `InfoGeometry.Algebra.SandwichLocalizationActions`.

The scalar ring is the existing
`CentralPowerLocalization.Away (denominator s)` on the native subring
`Subring.centralizer {s}`. It uses the original Mathlib Ore quotient from PR #334.
Centrality is imposed only inside this scalar centralizer.

The actual actions are constructed ring homomorphisms to `AddMonoid.End`,
yielding `Module (Scalars s) (Space s)`, a right module via
`Module (Scalars s)ᵐᵒᵖ (Space s)`, and `SMulCommClass`. Their joint formula is

`[a,u] ▷ [k,x,l] ◁ [b,v] = [k+a, u*x*v, l+b]`.

No multiplication of two arbitrary ambient fractions is introduced.

### 3. Balanced tensor quotient and bimodule equivalence

Owner: `InfoGeometry.Algebra.SandwichBalancedTensor`.

Write `C=Centralizer s` and `Q=Scalars s`. Since `C` may be noncommutative,
start with the native integer tensor product `T=(Q ⊗[ℤ] B) ⊗[ℤ] Q`.
Take the native quotient by the integer-submodule span of both balancing
relations, for every `c : C`:

* `((q*ι(c)) ⊗ x) ⊗ r - (q ⊗ (c*x)) ⊗ r`;
* `(q ⊗ (x*c)) ⊗ r - (q ⊗ x) ⊗ (ι(c)*r)`.

Here `ι` is the existing native localization ring homomorphism. Both maps of
the resulting equivalence are constructed explicitly. Evaluation sends
`[q ⊗ x ⊗ r]` to `q ▷ of(x) ◁ r`; its inverse sends `[k,x,l]` to the class
of `[k,1] ⊗ x ⊗ [l,1]`. The balancing relations and localization bonds prove
both inverse laws. No regularity is needed, including for singular denominators.

The native `ℤ`-linear equivalence also transports left `Q` and right `Qᵐᵒᵖ`
module structures to the quotient. Explicit elementary-tensor formulas prove
that these are exactly the outer-factor actions, with the right coefficient
in the order `r*b`. The actions commute, and the same equivalence is separately
packaged as native left and right scalar `LinearEquiv`s. This establishes the
actual balanced bimodule identification. For a self-adjoint denominator,
a native involution on the quotient reverses the three tensor factors and
exchanges the two scalar actions. The equivalence preserves that involution.
No ambient fraction multiplication or commutativity assumption is introduced.

### 4. Involution and Cayley equivalence

Owner: `InfoGeometry.Algebra.SandwichLocalizationStar`.

Assume `star s = s`. The actual quotient involution is
`star [k,x,l] = [l,star x,k]`; it exchanges the two scalar actions.
For an actual numerator `a` with `Commute s a` and both ordered identities
`star a*a=s²` and `a*star a=s²`, construct an `AddEquiv` with formula

`[k,x,l] ↦ [k+1, a*x*star a, l+1]`.

Both inverse laws and star preservation hold on every quotient element.
The equivalence is proved to agree with the two-sided action of the internally
constructed unitary scalar. It is not claimed to be a bimodule `LinearEquiv`;
its action on scalar coefficients generally involves conjugation.

### 5. Exact boundary of the specified one-sided formulas

Owner: `InfoGeometry.Algebra.OneSidedLocalizationBoundary`.

For a subring `R` containing `s`, ordered multiplication of the submitted raw
one-sided representatives respects their cross relation if and only if
`R ≤ Subring.centralizer {s}`. With a self-adjoint denominator, the corresponding
numerator-star congruence has the same exact criterion. These statements do not
require regularity. Star-closure of `R` is separate from relation congruence.
They do not rule out a differently transported involution on another carrier.

### 6. Actual Peirce specialization and defects

Owners: `InfoGeometry.OperatorAlgebra.PeirceSpine.SandwichCayley` and
`InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceDefectIdentities`.

Reuse `conePlus`, `coneMinus`, `genV`, `genSig`, `genJ`,
`cayleyKernelNumerator`, and the existing norm and regularity theorems.
Set `s=1+genV P A (star A)` and `a=1-V+2J`. The actual Cayley equivalence is
constructed without an on-shell hypothesis. Three-square star faithfulness
proves two-sided regularity and hence the faithful ambient embedding.

The universal polynomial defects retain their exact coefficients:

* `(2V-1)²-1 = 4(V²-V)`;
* `(1+V)(2-V)-2 = -(V²-V)`;
* `Σ³-Σ = (V²-1)Σ`;
* both ordered norm defects of `1-V+J` equal `V²-V`.

Thus the integral numerator is unitary on shell; it anticommutes with and
conjugates the signed cycle to its negative. No general eigenvalue exclusion
follows merely from a nonzero defect.

### 7. Corrected endogenous bridge and elliptic twist

Owner: `InfoGeometry.OperatorAlgebra.PeirceSpine.EndogenousKernelBridge`.

Reuse `evenGrade`, the seed corners and the on-shell orthogonality theorems.
With `D=evenGrade P A` and `e=1-V`, the actual corrected bridge is

`G=e*(D*A*D)*e-e*D³*e=e*D*(A-D)*D*e`.

It belongs to the native two-generator subring `Subring.closure {P,A}`.
Its cut-even component vanishes. On shell it is supported on both sides by `e`.
The actual constructed `endogenousCharge` also belongs to that subring.
On shell it obeys `[Σ,Q]=Q`, has its ordered through-kernel square formula, and satisfies
`[Σ,Q²]=2 • Q²`. These are equations over an arbitrary ring, not a claim that
all integer weights remain distinct in positive characteristic.

For an element `I` commuting with the two seeds, with `I²=-1`,
the actual sum `I*N₋-N₊*I` squares to `V`. Self-adjoint cut/coupling and
skew-adjoint `I` give self-adjointness of this sum. The compressed square
vanishes on the residual corner on shell. No scalar imaginary unit replaces `I`.

### 8. Finite noncommuting real matrix instance and counterexamples

Owner: `InfoGeometry.OperatorAlgebra.PeirceSpine.KernelBridgeMatrixWitness`.

The full carrier is `Matrix (Fin 8) (Fin 8) ℝ`, with actual matrix-unit
definitions for `P8`, `A8`, `D8`, `G8` and `elliptic8`. The seed cut and
coupling are proved noncommuting. The generic bridge and charge specialize to

`G8=E24+E35+E42+E53` and `Q=E04+E15+E46+E57`, with
`Q²=N₊=E06+E17≠0`.

The finite owner proves elliptic star/square and seed commutation, the twisted
arrow sum's self-adjointness and square, and the projected commutator
`-(E41-E50)≠0`. It gives the support traces and the integral unitary's
signed-cycle reversal and partial cut flip. Adding the specific full bridge
to `A8` fills the support; this is an example-specific conclusion.

The native subring generated by `P8`, `Atilde8`, and `elliptic8` is contained
in the actual elliptic centralizer. The matrix unit `E00` is excluded, proving
that this generated subring is proper in the full matrix ring. More precisely,
`E06` is a nonzero degree-two element but fails to centralize `elliptic8`, so
it is absent from that generated subring. Thus the valid nonzero square
`Q²=N₊` does not establish reconstruction of the whole degree-two sector.

A rational off-shell seed `Aoff=(3/5)A8+(4/5)G8` retains self-adjointness and
elliptic commutation, has defect `-(144/625)I8`, and has the nonzero adjoint
eigenvectors `E04` and `E40` with weights `+1` and `-1`. A separate finite
calculation proves that a metric-centralizing lower arrow changes the
degree-one charge to degree minus one, refuting the claimed automatic
single-degree module closure.

## Corrections and excluded claims

| Statement or formalization boundary | Exact mathematical disposition |
|---|---|
| Off shell, the degree ±1 eigenspaces do not exist | False. Eigenspaces are always defined and can be nonzero. Over the real carrier, tripotence supplies a particular five-degree decomposition; its failure does not exclude individual eigenvalues. |
| A single degree is a module over the whole metric centralizer | Not automatic. Multiplication by a degree −2 element can move a degree +1 vector to degree −1. |
| Failure of naive one-sided star rules out any star on a left localization | Too strong. The exact naive congruence criterion is proved. An internally invertible denominator allows transport of the ambient star. |
| Every odd perturbation destroys the whole residual corner | False in general. Collapse is an explicit full-rank matrix instance, not a universal theorem. |
| `e*D*A*D*e` is always the odd bridge | The subtraction `e*D³*e` is needed in general. The shorter expression can hold in the finite instance. |
| The nonzero square reconstructs the entire degree +2 sector | The actual `E06` is a nonzero degree-two element outside the seed-generated subring. The finite equation `Q²=N₊≠0` is preserved, while the stronger reconstruction inference fails. |
| Spin-triplet pairing universally violates Pauli antisymmetry | False without specifying the full orbital/spin pairing data. The source proves explicit operator identities. |
| Ring structure exists iff on shell or after C*-completion | False. Central algebraic denominators already give ordinary ring localization off shell. No universal ring-extension impossibility is claimed. |
| The displayed balanced bimodule tensor product | Constructed as an integer tensor quotient with both full-centralizer balancing relations, explicit inverse maps, and native compatible left/right module structures. This works without imposing commutativity on `C₀`. |

The intake distinguishes its generic ordered-square identity from its finite
`Q²=N₊≠0` instance; this distinction is retained. Its Clifford terminology is
not treated as an explicit assertion that the seeds generate every real
matrix. The proper-subring and missing-corner lemmas delimit exactly what
can be inferred from the actual generators.

“Cubic” describes the compressed word `D*A*D`; after expanding `D` and `e`,
it does not assert total polynomial degree three in the original seed.

KMS equilibrium, thermal holonomy, Fisher–Rao diffusion, Goldstone modes,
physical helicity, a superconducting condensate, Andreev scattering,
anomaly cancellation and global Morita equivalence require additional objects
and theorems. The matrix identities do not establish those interpretations.

## Verification contract

* Compile the exact new owners and their repository-source import closure using
  the fixed Lean/Mathlib revisions.
* Enumerate actual owned environment declarations, including private and
  generated declarations, and audit their transitive axiom dependencies.
* Preserve the source hashes, compiler diagnostics and audit records.
* Run independent semantic review and distinct execution QA.
* Run the staged proof gate and source scans; distinguish their lexical scope
  from kernel validation.
* Attempt maintained root gates separately and report a dependency/build block
  as such. Do not infer a full repository build from the focused package.

The authoring coordinator and candidate author do not provide their own final
independent acceptance. Existing source scanners, root gates and dependency pins
are retained unchanged.
