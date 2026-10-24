# Exact live-owner scope followup

Owner: lean/InfoGeometry/Canonical/UnifiedGeometryOperatorSignificance.lean
Observed SHA256: 24c16301e66697bcca93bdff065a7adbee913b50b2f98d7d5cb80316e43f7ed8 (matched first/last read).
Disposition: REQUEST_CHANGES, with a false theorem statement blocking mathematical acceptance. Read-only source audit; no build result claimed, no active process touched. GNS acceptance is separate.

## Blocking sign error is in source statements

At lines 464–468, jordanAssociator_eq_double_lieBracket claims assoc(T,X,S)=[[T,S],X]. Native Core/JordanAssociatorRing.symm_associator_eq_double_commutator instead gives [X,[T,S]]. The wrong sign is repeated in five_pillar_geometry_operator_synthesis (line 504) and pillar4JordanCartanE6 (line 710 onward). A `noncomm_ring` script does not establish a false equation.
Concrete refutation over 2×2 integer matrices: T=E00, S=E01, X=E11 gives [T,S]=E01, actual associator −E01, claimed RHS +E01. These differ over integers. The preceding jordanProd_commutator_eq_associator is correctly oriented: [L_S,L_T]X=[[S,T],X]=[X,[T,S]].

## Further exact scope corrections

- Header line 18 has the wrong residual factor X(1−XD). Actual theorem lines 116 onward correctly proves X(1−DX)=(1−XD)X=X−XDX. Calling this residual nilpotent needs additional hypotheses: X=1,D=0 gives residual 1 in a nontrivial ring.
- Γ²−Δ=0 is not Φ₂(Γ)=0; Φ₂ has support-relative form Γ+Δ. No Φ₆ construction appears in the displayed master theorem despite the header list.
- The factorization/swap formulas are ring algebra. Exact order four is not asserted by their types and fails for d=B=0 (the ambient element is 1). Here only one ordered inverse equation is exposed; the accepted Algebra/UnipotentReflexivePairFactorization supplies both ordered inverse laws and a fourth-power identity with explicit assumptions. No projective action, pole inversion geometry, or Bruhat/Moufang classification is constructed by naming these expressions.
- kmsModularWeight_intertwines_d/B are valid division-free weighted corner equations. R is an arbitrary commutative ring, u,v arbitrary (including zero), with no positivity/order or invertible density premise and no state. The weight also vanishes on the harmonic complement. These equations do not construct Tomita–Takesaki dynamics or a KMS state. Do not conflate them with accepted FiniteSeedRepresentedKMS.
- The supplied self-adjoint support assumptions support the projection algebra, but do not imply B=star d, a Kahler manifold, Ehresmann connection, analytic Hodge theory, or E6=F4⊕p. The Jordan identity on an associative ring alone cannot certify exceptional Lie/Jordan structure.
- Meta registration proves only each explicitly encoded claim; names such as alternativeLiftAndJordanE6 and .proved do not enlarge it. unifiedPillarRules independently discharges targets while ignoring the prerequisite argument, so the hand-authored schedule is not evidence of a discovered mathematical dependency chain or the advertised synthesis.

## Native reuse / handoff

Reuse Core/JordanAssociatorRing, Algebra/PeirceParityClosure, Singular/MoorePenrose, Core/DiracSuperalgebra and Algebra/UnipotentReflexivePairFactorization before maintaining duplicate products, supports and conjunction packets. Preserve the foreign active owner; parent/writer must coordinate any fixes. Rebaseline after changes, run independent exact-source AA and serialized QA. No compiler outcome is inferred from this audit.
