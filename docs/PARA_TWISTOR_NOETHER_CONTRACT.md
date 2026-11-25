# Quadratic, Lorentz incidence, and operator symmetry contract

## Provenance and snapshot

The unedited user proposal is `docs/intake/para-twistor-noether-20261124/proposed-formalization.txt`.
Its uploaded filename is `Pasted text(20261124-080112).txt`; its SHA-256 is
`852ce066bbcf3e261495003480cab349184e6e724c05b43dcc76ca19c965094c`.
Implementation starts at `fe24e350b08fdea04f74c0748ef9fd9417c47529` on
`codex/para-twistor-noether-20261124`. Lean is pinned to 4.34.1 and Mathlib to
`d13f23b723b8a846827a245b89c10fc7d3f11612`; neither pin changes.

The raw proposal is intake, not a verification record. The four narrative
parts describe different carriers. Their proximity does not supply a map
between them. The implementation keeps each result in its existing owner layer.

## Claim ledger and owner decisions

| Intake claim | Exact carrier and hypotheses | Decision / owner |
| --- | --- | --- |
| Split involution, neutral pairing, alternating form, isotropic summands | A real module and its algebraic dual, with projectivity for the established nondegeneracy theorem | Reuse `Clifford.NeutralPhaseSpaceCore` and `Canonical.NeutralDualPairSplitting`; these already prove stronger algebraic results than the coordinate identities. No duplicate para-structure. |
| Quadratic Fenchel residual | Arbitrary finite real square matrices `G`, `GInv`, with `GInvᵀ = GInv`, `G * GInv = 1`; positivity only for inequalities and maximization | Extend `OperatorAlgebra.OperatorDirichlet.MatrixLegendre` with a supplied-inverse residual and attained native `IsGreatest` / `sSup` result. Symmetry of `G` need not be separately assumed. |
| Plücker relation and determinant pairing | Native exterior coordinates of four real vectors | Reuse `Projective.ExteriorKleinCoordinateIncidence.det_rows_eq_incidence` and its existing coordinate/exterior compatibility. No duplicate Plücker carrier. |
| Nonzero intersection of two 2-planes iff determinant zero | Each generating pair must be linearly independent | Reuse `ExteriorKleinTwoPlaneIncidence` and its nondegenerate-frame hypotheses. The unrestricted prose claim is false: repeated first-frame vectors give zero determinant without a nonzero intersection. |
| Real Lorentz graph incidence | Spacetime and spinors are `Fin 4 → ℝ`; graph submodules live in their real product | Compose the existing `GullDoranPseudoscalarBridge.realSigma1/2/3` with a native linear soldering map, then reuse `Twistor.RealTwistorIncidence`. Prove determinant = Lorentz quadratic squared, faithfulness, dimension four, and null separation iff nonzero graph intersection. |
| Peirce symmetric triple closure and repeated-entry associator | Any associative ring; idempotent `P`; the two outer inputs lie in the same off-diagonal corner | Reuse `PeirceSpine.Bergman.jordanTriple`, the existing corner support/zero-product laws, and `Core.JordanAssociatorRing`. Prove polarized support for arbitrary middle input and both corners. |
| Pairing preservation and infinitesimal skewness | Any nontrivial associative real algebra, linear vector lift, nonzero scalar anticommutator factor, and explicit intertwining equations | Add separate generic implications. They do not need lift injectivity. Separate native endomorphism constructions derive linearity when the lift is injective. |
| Matrix trace zero-rate identity | Finite real matrices, `H * K = K * H` | Reuse cyclicity and `Core.JordanMultiplicationClosure.trace_adjoint_identity` in a consumer. This is an algebraic zero-rate identity. |

## New owner targets

- `OperatorAlgebra/OperatorDirichlet/MatrixLegendreResidual.lean`
- `Twistor/RealLorentzTwistorIncidence.lean`
- `OperatorAlgebra/PeirceSpine/PeirceTriple.lean`
- `Clifford/AnticommutatorSymmetry.lean`
- A focused consumer/check module and reproducible validation records.

Every public theorem must have a complete proof. General matrix results retain
all matrix entries and off-diagonal products. The Lorentz construction reuses
the established real Pauli generators; it does not introduce another gamma
matrix family. The vector/endomorphism and graph interfaces are native Mathlib
`LinearMap`, `Submodule`, and finite-dimensional rank interfaces.

The required old owners transitively import broad tactics. New files do not
add `import Mathlib`, and the complete exterior-incidence chain is not imported
merely to restate an already owned theorem. Owner reuse is documented here;
only imports needed for the new implications enter their proof dependencies.

## Proved dependency order

1. Existing matrix square completion plus native inverse uniqueness implies
   the supplied-inverse quadratic residual. Positive semidefiniteness implies
   the inequality; the inverse provides an attaining point, hence the actual
   greatest value and supremum.
2. Existing real Pauli matrices define a linear faithful soldering map. Its
   determinant identity gives a nonzero kernel exactly at Lorentz-null points.
   The existing graph/kernel equivalence then gives graph incidence.
3. Existing Peirce support laws give polarized triple support. Existing
   associative Jordan identities plus corner square-zero give the associator.
4. Unit cancellation and the existing commutator Leibniz identity transport
   the supplied scalar anticommutator relation. Nontriviality and the nonzero
   scalar allow reflection back to the pairing. Injectivity is used only to
   derive linearity of the intertwined functions.

There is no asserted causal edge joining the quadratic, projective, Peirce,
and symmetry constructions without an explicit connecting map.

## Scope boundaries and corrections

- A finite neutral vector-space form is not a constructed para-Kähler
  manifold. Integrability and closed differential forms remain outside this PR.
- The quadratic result establishes a Fenchel maximum and residual. A Bregman
  interpretation requires its corresponding derivative/gradient bridge.
- Plücker 2-planes in real dimension four and the real Lorentz graph 4-planes
  in dimension eight are separate carriers.
- The source's `realSolderingAdj4` is a cosoldering matrix. The actual 4-by-4
  adjugate is multiplied by the Lorentz quadratic factor.
- The uploaded graph proof reverses its final equality unnecessarily. The
  native graph/kernel proof avoids that invalid step.
- The associative symmetric triple is not a bundled Kantor system or a
  super-Grassmannian construction.
- Ordinary unit conjugation is distinct from the existing twisted Clifford
  Lipschitz action. Forward closure does not alone construct a group action
  or prove surjectivity.
- Algebraic skewness is not an exhibited smooth Killing vector field. A
  cyclic trace zero-rate equation is not a proved time-dependent conservation
  law, a Souriau momentum map, or a type-III trace construction.

## Acceptance plan and role separation

The parent and `repo_scout` author candidates. `math_audit` independently
reviews theorem meaning and dependencies. `acceptance_qa` independently
validates the final frozen snapshot without authoring it.

Acceptance requires exact pinned dependencies, a maintained shared-lock
wrapper, explicit target builds, fresh warnings-as-errors elaboration of
changed Lean sources, an environment-based declaration/axiom audit permitting
only `propext`, `Classical.choice`, and `Quot.sound`, semantic counterexamples
and positive consumers, and unchanged staged/publication gates. A focused
pass is not a whole-repository certificate. Evidence and any unmet publication
gate will be recorded separately after execution.
