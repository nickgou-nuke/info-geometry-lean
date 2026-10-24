# Source alignment for the historical synthesis intake

This record concerns mathematical statements, not claims of historical
priority, stagnation, or completion of twentieth-century research programs.
The supplied prose is not a source for those historical assertions.

## Reuse and corrected scope

1. `Core/JordanAssociatorRing.lean` already proves
   `symm_quadratic_sandwich`, `commutator_symm_operator`, and
   `symm_operator_commutator`. For the unnormalized product `xy+yx`,
   `[M_S,M_T](X) = [[S,T],X]`, not `[[T,S],X]`. These are associative-ring
   identities, not a classification of F4 or E6. The normalized real Jordan
   associator in `Core/JordanAssociator.lean` has factor 1/4.
2. `Singular/DrazinReflexiveDefect.residue_eq_nilpotent` already identifies
   `X-XDX` with the native Drazin nilpotent part under `IsDrazinInverse X D k`.
   `Canonical/Drazin.IsDrazinInverse.fittingNilpotentPart_eq_nilpotent` bridges
   the Fitting notation, and `fittingNilpotentPart_pow_succ_eq_zero` proves
   nilpotence. Mere commutation only gives factorization; it does not supply
   the reflexive and power laws needed for nilpotence.
3. The shell theorem `drazinShellProj_mul_a_mul_drazinShellProj_eq_zero_of_le`
   in `Canonical/DrazinShellCascade` assumes a `PowerMPFamily` for the nilpotent
   part, in addition to a Drazin witness. Existence of such a family is not
   asserted in every star ring. No categorical functor is established just
   by displaying shell formulas.
4. Square-zero corners do not make every Jordan associator vanish.
   `Canonical/DrazinInterShellJordan.interShell_jordan_associator` gives
   the normalized associator `(D∘D)∘B-D∘(D∘B)=-(1/2)•D` for the MP dual.
   The distinct endpoint-projector associator must not be confused with this
   corner/dual associator.
5. `OperatorAlgebra/TracialCARDensity` already supplies `density_mul_ann`,
   `ann_mul_density`, `annihilatorKMS`, and `density_divisionFreeKMS` for the
   native CAR pair and tracial functional. Substitute weights `u*u` and `v*v`.
   These are algebraic weighted-functional identities. Positivity,
   normalization, analytic strip conditions, and Tomita--Takesaki theory do
   not follow from an arbitrary commutative coefficient ring.
6. The Zorn operator construction remains the source-aligned CAR/color
   closure documented in `ZORN_COLOR_OPERATOR_CLOSURE_VERIFICATION.md`:
   gl3 acts on a fermionic Heisenberg superalgebra with central odd brackets.
   It is not the proposed raw-CAR gl(3|1) classification. An operator lift
   preserves proved square and anticommutator relations; it is not a
   multiplicative embedding of the nonassociative algebra. The associator
   defect alone is not a proof of the Nambu fundamental identity.

For the submitted boost formula, multiplication on both sides by `u+vΓ` and
`u-vΓ` can be stated without normalization. Calling it conjugation by an
inverse requires a proved unit relation, such as `u²-v²=1` with `Γ²=1` and
central coefficients. A ring automorphism obtained this way is not thereby
a star automorphism or a positive-state transport theorem.

These owner statements were inspected directly during intake. This record
does not add a monolithic theorem assembling unrelated claims, duplicate
existing carriers, or certify the entire dependency graph. Their exact
hypotheses and separately verified constructive alternatives remain the
authority. Further synthesis requires explicit maps and compatibility proofs.
