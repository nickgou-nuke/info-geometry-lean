# Corrected Peirce/operator archetypes

## Contract

Replace the proposed `UnifiedGeometryOperatorSignificance` narrative, not the
existing owner definitions, with the following separate mathematical layers.
There is no universal five-pillar geometry theorem here. In particular, a
conjunction of identities does not construct maps between exceptional groups,
analytic operator algebras and differential geometry.

### 1. Associative inverse decomposition and Peirce corners

Drazin nilpotence requires the Drazin hypotheses. The identity
`x - x*d*x = x*(1-d*x)` alone is a ring expansion, not a spectral theorem.
For orthogonal idempotents p,q, `(p*x*q)^2=0`; sums of such corners can have
nonzero mixed products and higher nilpotency index. No universal shell
filtration or disappearance of mixed associators is claimed in this extension.
The Drazin and filtration corridors remain separate from the pair construction.

### 2. Reflexive square-zero pairs and regular-module projections

Explicit assumptions: d*d=0, B*B=0, d*B*d=d, B*d*B=B.
Existing owner: `Canonical.ReflexiveNilpotentFlows.support_table`.
It supplies idempotence and mutual annihilation of dB, Bd and 1-dB-Bd.
New owner: `Canonical.PeirceWeightedTrace.complement_fixed_iff`:

    (1-dB-Bd)*x=x iff d*x=0 and B*x=0.

This is an exact common-kernel characterization on the regular module. It is
not an elliptic Hodge theorem. Self-adjointness of the products is explicit in
`support_complement_selfAdjoint`; no inverse or adjoint existence is assumed
implicitly. The support projection is not called the Hodge Laplacian.

### 3. Active-corner polynomial identities and ambient units

Owners: `Canonical.GrassmannianBundleCyclotomicOrientability` and
`Canonical.ReflexiveNilpotentFlows`.
Use involutivity for Gamma^2=Delta, not Phi_2. Phi_2(t)=t+1.
Phi_3, Phi_4 and Phi_6 are polynomial identities with Delta as the active
corner identity. They do not establish Kähler integrability or geometric
triality. The Weyl triple product and its two-sided inverse give an actual
ambient unit. Fourth power one means order dividing four, not exact order four.

### 4. Algebraic scalar actions and weighted tracial identities

`ReflexiveNilpotentFlows` owns unipotent, diagonal and rotor composition laws.
Weyl conjugation exchanges the diagonal parameters; it does not identify
negation of an involution with inversion of that involution.

`PeirceWeightedTrace.supportWeight a b d B = a*(Bd)+b*(dB)` (scalar action)
extends the existing full-support CAR density calculation to arbitrary active
support. Its four eigenproduct equations prove division-free intertwining.
`weighted_trace_boundary` reuses
`OperatorAlgebra.TracialCARDensity.eigenproductKMS` and its existing `weighted`
linear functional. No positivity, normalization, topology, analytic strip,
modular operator or Tomita–Takesaki theorem is asserted. Squared weights a=u²,
b=v² are ordinary specializations, not additional axioms.

### 5. Special Jordan products in an associative envelope

Owner: `Core.JordanAssociatorRing`, namespace `Core.JordanAssociator`.
`symm_operator_commutator` proves

    [M_s,M_t](x) = [[s,t],x],  M_s(x)=sx+xs.

`symm_associator_eq_double_commutator` fixes the associator convention.
`symm_operator_reversed_bracket_iff` characterizes when the wrong reversed
sign accidentally agrees, including characteristic two. These results require
no nilpotent pair and are logically independent of layers 2–4. They do not
identify E6 or F4. Reuse these owners rather than duplicating them under
exceptional-algebra names.

### 6. Alternative algebras and their associative operator representations

This is a distinct carrier layer. Alternativity permits square and polarized
anticommutator identities for left multiplication, not preservation of arbitrary
products. The associator measures the failure of multiplicativity. A Clifford
representation need not be injective. An octonionic associator is not called a
Nambu bracket without the required identities. No unconditional gl(3|1),
Cl(3,4) embedding, or exceptional-group identification follows from the pair
identities. Existing Zorn/CAR and obstruction owners must be used for any
further specialization; this change does not replace them.

## Verification boundary

`Canonical.PeirceWeightedTraceAudit` audits the new declarations and the
Jordan sign/trace dependencies directly. The target build checks imported
owners in its dependency cone; it is not a repository-wide build or a proof of
the stronger geometric interpretations excluded above.
