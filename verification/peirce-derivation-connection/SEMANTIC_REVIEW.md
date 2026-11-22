# Independent semantic review: Peirce derivation connection

Date: 2026-11-22.

Reviewer: `/root/paper_mathematics`, independent of the implementation author and the execution QA agent.

Disposition: **PASS** for the exact frozen source identified below. No material semantic findings remain.

## Reviewed artifact identity

Repository root: `/workspace/scratch/58c07266fdb0/info-geometry-lean`.

| Artifact | Repository-relative path | SHA-256 |
| --- | --- | --- |
| Owner | `lean/InfoGeometry/OperatorAlgebra/PeirceDerivationConnection.lean` | `ae651b99bb56edaebca105e673a1b08514a7991251adc2bda9246684b29b231f` |
| Declaration audit | `lean/InfoGeometry/OperatorAlgebra/PeirceDerivationConnectionAudit.lean` | `b0c2e8446cd0f5af7ff69f97bc30d3429ff8df8dd7f451304a1d2fe38adff1a7` |
| Contract | `docs/PEIRCE_DERIVATION_CONNECTION_CONTRACT.md` | `b94e53704f839142fade7314379d4762ec651e2b4dd5ae975267bed3ca42a98a` |

All three hashes were independently read from the files when preserving this record. The audit source was inspected and lists all nine public owner declarations. This is not a claim that its `#print axioms` commands were executed by this reviewer.

## Actual carrier and action

The common algebraic setting is a commutative scalar ring `R`, an associative ring `A`, and an `R`-module structure on `A`. The action is the existing `K : LieActionLane R A`, with the existing predicate `hK : IsLeibnizAction K`. Write `delta_x = K.operatorAction x`.

The action supplies both:

- ordinary two-sided Leibniz: `delta_x(a*b) = delta_x(a)*b + a*delta_x(b)`;
- the representation identity: `delta_[x,y](a) = delta_x(delta_y(a)) - delta_y(delta_x(a))`.

For `p : A` with `hp : p*p = p`, the section carrier is the existing native submodule `peirceRange p = {s | p*s=s}`. The definition composes the existing `rangeProjection`, the action endomorphism, and the existing subtype inclusion:

`derivationConnection K p hp : K.L →ₗ[R] Module.End R (peirceRange p)`.

Its value at a direction `x` and section `s`, viewed in `A`, is `p * delta_x(s)`. The direction map is linear; it is not asserted to be a Lie homomorphism.

The final source removes unnecessary scalar compatibility assumptions precisely where they are unused:

| Declaration group | Additional multiplicative scalar compatibility |
| --- | --- |
| Tangency and raw section curvature | Neither `IsScalarTower R A A` nor `SMulCommClass R A A` |
| Connection, evaluation, native operator curvature, compressed-Gram evaluation, fixed-projector flatness | `SMulCommClass R A A`; no `IsScalarTower R A A` |
| Native right-multiplication Leibniz identity | Both `IsScalarTower R A A` and `SMulCommClass R A A` |
| Inner specialization | `R = Int`, with the canonical module and scalar compatibility instances for any ring `A` |

The contract states a sufficient common context for the complete API; individual declarations have the weaker hypotheses above. There is no faithfulness, finite-dimensionality, star, positivity, characteristic-zero, invertible-two, or topology premise. The general curvature theorem does not require the action to fix `p`.

## Curvature, signs, and proof logic

For `nabla_x = derivationConnection K p hp x`, the theorem proves the equality of actual native endomorphisms:

`nabla_x * nabla_y - nabla_y * nabla_x - nabla_[x,y]`

equals the existing `leftCornerAction` with coefficient

`projectorCurvature p (delta_x p) (delta_y p) = p * ((delta_x p)*(delta_y p) - (delta_y p)*(delta_x p)) * p`.

Multiplication of endomorphisms is composition, with the right factor applied first. The coefficient has the positive sign displayed above. The bracket correction is essential and comes from the existing Lie-action law.

The substantive proof is derived, not assumed:

1. Differentiate `p*p=p` to obtain `p*(delta_x p) + (delta_x p)*p = delta_x p`.
2. Reuse the existing tangent theorem to obtain `p*(delta_x p)*p=0`.
3. Expand the projected derivatives by Leibniz and cancel the ambient second derivatives using the representation identity.
4. Differentiate `p*s=s`; the resulting section formula and zero sandwich reduce the residual terms to the two ordered products in the coefficient.
5. Use native extensionality to obtain the operator identity, then the existing compressed-Gram theorem for its alternate readout.

The proof's `noncomm_ring` step preserves the order of noncommuting factors and uses associative ring identities. The `abel` steps rearrange only additive expressions. No curvature hypothesis is introduced.

`derivationConnection_flat_of_fixed` is a sufficient-condition theorem: when every direction fixes `p`, it first rewrites by the established operator curvature theorem and then simplifies the coefficient to zero. It does not assert that this condition is necessary.

## Reuse and public interface

The nine public declarations are:

1. `derivationConnection`
2. `derivationConnection_apply`
3. `operatorAction_idempotent_tangent`
4. `projected_derivation_curvature`
5. `derivationConnection_leibniz`
6. `derivationConnection_curvature`
7. `derivationConnection_curvature_apply_eq_compressedGram`
8. `derivationConnection_flat_of_fixed`
9. `derivationConnection_inner`

The existing section carrier, projection, right multiplication, left corner action, tangent criterion, curvature coefficient, compressed-Gram coefficient, Lie action, and Leibniz predicate are reused. There is no replacement differential algebra or theorem-bearing structure.

The evaluation lemma is an appropriate transparent definitional API equation. The inner compatibility theorem compares the new connection with the existing projected inner-derivation connection as native endomorphisms on the same carrier. It explicitly specializes to `innerLieActionLane : LieActionLane Int A`, so it does not claim an arbitrary-scalar inner comparison. Its proof by extensionality and definitional equality is appropriate.

## Nonvacuity and its verification boundary

An independent mathematical witness fits the final assumptions. Let `A = Matrix (Fin 2) (Fin 2) ℝ`, take integer scalars for the lane, and use `innerLieActionLane A`. Set `p=E_11`, `x=E_12`, and `y=E_21`.

Then `delta_x(p)=-E_12`, `delta_y(p)=E_21`, and the curvature coefficient is `-p`. Therefore curvature sends the section `p` to `-p`, which is nonzero; indeed it acts as minus the identity on `pA`.

The inner action is nonfaithful: the identity matrix is a nonzero direction with zero action. Thus the witness also confirms that the nonfaithful scope is substantive.

This is a mathematical calculation supporting semantic nonvacuity. No Lean example theorem or executable test of this witness was added or run by this reviewer. The frozen owner itself does not include a nonzero example theorem.

## Differential and interpretation boundaries

Each `delta_x` is an ordinary degree-zero derivation of `A`. The exterior Chevalley-Eilenberg differential is a different degree-one operator on alternating forms. The curvature formula includes the Lie bracket correction appropriate to that calculus; it does not identify the square of an ordinary derivation with exterior curvature.

The construction is the algebraic Grassmann connection. A primary reference is Alain Connes, *C\* algebras and Differential Geometry*, English translation (2001) of the 1980 note, PDF page 3, Definitions 2-3 and the Grassmann connection calculation: <https://arxiv.org/pdf/hep-th/0101093>. There the connection is `nabla_X^0=e*delta_X`, curvature is the commutator of connection operators minus the connection in the bracket direction, and its coefficient is `e*(de wedge de)`. The implementation isolates the algebraic identity; it does not claim the paper's analytic C*-dynamical conclusions.

No metric positivity, Lorentzian or physical equation, octonion multiplication, G2 identification, KMS structure, or analytic modular result follows from this owner alone. The contract keeps these interpretation boundaries explicit. The clarified nonzero-underlying-space qualification for indefiniteness in the claim ledger is correct.

## Revision control and review role

The initial semantic review accepted source hash `74e3c9294a98fbf070ea205a213d4c188cbf6764b91e987687bb42fa25ff5f72`. The next review accepted hash `d2cda351e30b37b1e61744417f8d0e7d0d1815cd1734f867731a11779bba8974`, after explicit binding of the intended Leibniz hypothesis, commutator qualification, and elimination of unused elaboration material. In-memory reversal verified that these were exactly the changes.

The frozen source reviewed here differs from the second snapshot only by the reported unused-instance omissions and the flatness proof's direct reuse of the operator curvature theorem. In-memory reversal reconstructed the second hash exactly. All displayed mathematical formulas and the intended scope remain accepted.

No `axiom`, `sorry`, `admit`, `unsafe`, or `opaque` declaration occurs in the new owner. This source-level observation does not substitute for transitive axiom inspection or kernel replay.

The reviewer made no repository edits and ran no Lean compiler, Lake build, kernel replay, or tests. Reading source, hashing files, and comparing revisions in memory were the only verification operations. This scratch record preserves the completed semantic PASS. Execution evidence and acceptance gates belong to the independent QA receipt and must be bound to the same frozen bytes.
