# Projective Mathlib Canonicalization Plan

This note documents the current implementation plan for the projective
canonicalization corridor.

It is a planning and discussion artifact for collaborators. It does not replace
Lean source as the truth surface.

This is not a greenfield plan. Several of the relevant owner surfaces already
exist in the repository and must be treated as existing foundations to
consolidate, not as new ontology to invent.

## Non-Negotiable Redline

The original theory spine stays exactly as it is:

1. `count`
2. `projective rays`
3. `doubled/Krein primitives`
4. translated mathlib realization of the same seed
5. Clifford/isometry consequences
6. transport, anomaly, thermo, and capstone consumers

This means:

- mathlib is not allowed to replace the projective root
- the doubled/projective layer remains the foundational axiom surface of the theory
- the mathlib lane is a parallel isomorphic presentation
- comparison and transport files must make the isomorphism explicit

The governing law is:

- one seed
- two roots
- explicit isomorphism
- no rerooting

This is law, not preference.

Read against the current codebase, the law is mandatory as:

- semantic ownership direction
- owner/translator/coherence discipline
- explicit comparison at the language junctions

It is not a raw prohibition on mathlib in bedrock files, because the current
owners already use mathlib as implementation substrate.

It is also not a doctrine that one presentation is metaphysically primitive and
the other is tolerated.

The correct reading is:

- the repo preserves two mathematically equivalent presentations
- the redline governs semantic ownership and theorem passage
- mathlib is used aggressively as assembler language wherever it improves proof
  length, infrastructure, and canonicality
- what is forbidden is semantic displacement, not mathlib usage

## What Mathlib Already Gives

Mathlib already supplies the canonical language for:

- projectivization `ℙ K V`
- actions of linear automorphisms on projective space
- quadratic forms
- isometries
- Clifford algebras
- graded tensor products

In local repo terms, the relevant entry points are:

- [Projectivization/Basic.lean](../.lake/packages/mathlib/Mathlib/LinearAlgebra/Projectivization/Basic.lean)
- [Projectivization/Action.lean](../.lake/packages/mathlib/Mathlib/LinearAlgebra/Projectivization/Action.lean)

## What Is Already Present In The Repo

The current repo already uses mathlib projectivization as a canonical surface in
multiple places.

Existing projective surfaces:

- [lean/InfoGeometry/Convex/ProjectiveRays.lean](../lean/InfoGeometry/Convex/ProjectiveRays.lean)
- [lean/InfoGeometry/Krein/State.lean](../lean/InfoGeometry/Krein/State.lean)
- [lean/InfoGeometry/Twistor/NullProjective.lean](../lean/InfoGeometry/Twistor/NullProjective.lean)

Existing doubled/Krein owner surfaces:

- [lean/InfoGeometry/Krein/DoubledSpace.lean](../lean/InfoGeometry/Krein/DoubledSpace.lean)
- [lean/InfoGeometry/Krein/KreinSpace.lean](../lean/InfoGeometry/Krein/KreinSpace.lean)

Existing split-`Cl(1,1)` realization hinge:

- [lean/InfoGeometry/Quantum/RealSplitClifford.lean](../lean/InfoGeometry/Quantum/RealSplitClifford.lean)

Existing projective descent surfaces:

- [lean/InfoGeometry/Projective/Dynamics.lean](../lean/InfoGeometry/Projective/Dynamics.lean)
- [lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean](../lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean)

So the main missing surface is not a new foundation. It is a tighter coherence
file that makes the existing owners meet explicitly.

## Mandatory Ownership Discipline

The current codebase already fixes the owner order for this lane:

- [lean/InfoGeometry/Krein/DoubledSpace.lean](../lean/InfoGeometry/Krein/DoubledSpace.lean) is an owner
- [lean/InfoGeometry/Krein/KreinSpace.lean](../lean/InfoGeometry/Krein/KreinSpace.lean) is an owner
- [lean/InfoGeometry/Convex/ProjectiveRays.lean](../lean/InfoGeometry/Convex/ProjectiveRays.lean) is a quotient owner
- [lean/InfoGeometry/Krein/State.lean](../lean/InfoGeometry/Krein/State.lean) is a quotient owner
- [lean/InfoGeometry/Quantum/RealSplitClifford.lean](../lean/InfoGeometry/Quantum/RealSplitClifford.lean) is a realization translator
- [lean/InfoGeometry/Projective/Dynamics.lean](../lean/InfoGeometry/Projective/Dynamics.lean) is a descent translator
- [lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean](../lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean) is a bridge/coherence surface

This does not mean mathlib may only appear “later.”

It means:

- owner files keep theory ownership
- translator files expose one presentation in the other language
- coherence files prove the two presentations agree
- no file may silently let one presentation swallow the other

## What Remains Repo-Owned

The following are still genuine repo foundations and are not to be displaced:

- the doubled carrier
- the Krein package
- the projective dynamics on doubled rays
- the red-line count/projective foundation

Current owner surfaces:

- [lean/InfoGeometry/Krein/DoubledSpace.lean](../lean/InfoGeometry/Krein/DoubledSpace.lean)
- [lean/InfoGeometry/Krein/KreinSpace.lean](../lean/InfoGeometry/Krein/KreinSpace.lean)
- [lean/InfoGeometry/Convex/ProjectiveRays.lean](../lean/InfoGeometry/Convex/ProjectiveRays.lean)
- [lean/InfoGeometry/Krein/State.lean](../lean/InfoGeometry/Krein/State.lean)
- [lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean](../lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean)

## Current Reading

The correct interpretation is:

- the projective language is the assembler of the theory
- mathlib is the canonical formal implementation language of one parallel presentation
- the projective and mathlib lanes are not competitors
- they are isomorphic realizations of the same seed after gauging

## Current Canonicalization Gain

Recent `SplitQ11` and head-Clifford work has strengthened the lower algebraic
owner surface, but it must continue to be read as a translated consequence of
the doubled/projective root, not as a new foundation.

The real gain is:

- local Clifford, phase-flip, projector, and equivariance claims now have a
  cleaner mathlib-native owner surface

The standing risk is:

- allowing the translated Clifford surface to masquerade as the theory root

This plan exists to prevent that failure.

## Implementation Strategy

### Phase 1: Freeze the Comparison Law

Create one dedicated comparison file whose sole job is to state that the
foundational projective/doubled seed realizes the split `Cl(1,1)` atom in the
mathlib language.

This file must depend on the projective/doubled root, the existing split
realization hinge, and the existing projective descent, not the other way
around.

Candidate role:

- projective/doubled owner below
- existing mathlib realization hinge adjacent
- explicit theorem-level comparison

### Phase 2: Standardize On The Already-Canonical Projective Surface

Use the already-present mathlib `Projectivization` surfaces consistently
wherever the quotient excludes the vacuum, while keeping the repo’s projective
layer as the theory owner.

That means:

- keep repo names for the projective redline
- prove those names coincide with the mathlib projectivization presentation
- delete duplicate projective wrappers only when the replacement preserves the
  original dependency direction
- preserve the old pointed quotient where the distinguished vacuum class is part
  of the structure

### Phase 3: Do Not Re-Own The Split `Cl(1,1)` Atom

Do not introduce a second owner for the claim that doubled-space `J`, `K`, and
`ε` realize the split Clifford atom. That owner already exists in
`RealSplitClifford.lean`.

The new coherence file may depend on that hinge, but it should not re-own it.

This is the place where the two roots are compared:

- foundational root: projective/doubled/Krein
- translated root: mathlib quadratic-form and Clifford language
- hinge owner: existing real split Clifford action

### Phase 4: Descend Ambient Operators to Projective Space Canonically

The projective layer should expose:

- descended `J`
- descended `ε`
- descended `I = Jε`
- positive, negative, and null sectors
- polarization sectors induced by `ε`

These are already substantially present. The new work is to package them as one
coherence surface and compare them to the split-`Cl(1,1)` presentation.

They must continue to be presented as descended actions of the ambient doubled
operators, not as new projective primitives unrelated to the carrier.

### Phase 5: Lift Projectors and Cartan Split Carefully

Upstairs on the linear/Krein carrier we have:

- `P₊ = (Id + ε)/2`
- `P₋ = (Id - ε)/2`
- `P₊ + P₋ = Id`
- `P₊ - P₋ = ε`

Downstairs on projective space, these do not descend as linear operators.
What descends is:

- the `±` eigensectors
- the null stratification
- the projective involutions
- the Cartan split induced from ambient involutions

So the projective canonicalization must package sector structure, not pretend
that projective space is itself linear.

### Phase 6: Move Anomaly and Equivariance Above the Comparison Surface

Projector mismatch, Drazin/Penrose obstruction, phase-flip residuals, and
similar anomaly language should be stated only after the two presentations are
already compared.

That keeps:

- the foundation clean
- the translation explicit
- the anomaly genuinely derived

## Proposed File Roadmap

The next planned file order is:

1. `lean/InfoGeometry/Canonical/ProjectiveSplitQ11Realization.lean`
2. `lean/InfoGeometry/Projective/SplitKreinDatum.lean`
3. `lean/InfoGeometry/Canonical/ProjectiveCartanPolarizationBridge.lean`
4. `lean/InfoGeometry/Canonical/ProjectiveEquivarianceBridge.lean`

Intended roles:

- `ProjectiveSplitQ11Realization`: strict translator/coherence file above
  existing owners
- `SplitKreinDatum`: projective packaged structure
- `ProjectiveCartanPolarizationBridge`: ambient/projective split bridge
- `ProjectiveEquivarianceBridge`: anomaly and phase-flip consequences

## Narrow Scope Of The First File

The first file should prove four things and nothing more:

1. the repo-owned projective quotient maps canonically into the mathlib
   projective surface on the doubled carrier
2. the ambient doubled involutions and actions descend compatibly on both sides
3. the existing doubled `J`, `K`, `ε` package realizes the split `Cl(1,1)` atom
   through the already-owned hinge surface
4. the two descended presentations are theorem-level coherent

This file should not:

- re-own `DoubledSpace`
- re-own `J`, `ε`, or `I`
- re-own the split `Cl(1,1)` atom
- introduce graded tensor or transport claims
- act like a capstone

It is a comparison file, not a new root.

The first file therefore has a strict jurisdiction:

- compare already-owned projective/doubled structure with the already-owned
  split-`Cl(1,1)` realization
- stop before anomaly, transport, tensor, or thermo language
- make the bilingual junction explicit in one place

## Naming Discipline For The First File

The theorem names should stay literal and comparative. Candidate shapes:

- `projectiveRay_toMathlibProjectivization`
- `projectiveRay_equiv_mathlibProjectivization`
- `doubled_ops_descend_projectively`
- `realSplitClifford_realizes_Q11`
- `projective_split_Q11_realization_coherent`

## Acceptance Gates

The plan is only acceptable if all of the following remain true:

- the redline remains
  `count -> projective rays -> doubled/Krein primitives -> translated Clifford realization`
- [lean/InfoGeometry/Audit.lean](../lean/InfoGeometry/Audit.lean) stays green
- representation-depth adjacency is preserved
- the doubled/Krein/projective root still appears as bedrock in the DAG reports
- new mathlib-facing files read as owner/translator/coherence surfaces, not as
  replacement foundations
- the first realization file remains small and does not absorb tensor,
  transport, or anomaly machinery

## Rejection Criteria

Any new theorem in this corridor should be rejected if:

1. it states the mathlib/Clifford presentation as primitive when the
   doubled/projective statement is the actual owner
2. it introduces a projective operator not as a descended action of the doubled
   operators
3. it causes the new realization/coherence file to be imported back into
   `DoubledSpace.lean`, `KreinSpace.lean`, `ProjectiveRays.lean`, or
   `Krein/State.lean`
4. it skips the comparison pattern:
   foundational repo-native statement,
   mathlib realization statement,
   coincidence/coherence theorem
5. it treats mathlib usage itself as architecturally suspect rather than asking
   whether theory ownership has been displaced

## Code-Faithful File Order

The practical file order for this lane is:

1. keep `Krein/DoubledSpace.lean` and `Krein/KreinSpace.lean` as owners
2. keep `Convex/ProjectiveRays.lean` and `Krein/State.lean` as quotient owners
3. keep `Quantum/RealSplitClifford.lean` as realization translator
4. keep `Projective/Dynamics.lean` as descent translator
5. add `Canonical/ProjectiveSplitQ11Realization.lean` as coherence file
6. only then allow higher transport, anomaly, and thermo files to depend on the
   bridge

This file order is about theorem ownership and comparison surfaces. It is not a
ban on using mathlib infrastructure earlier in the implementation.

## What Collaborators Should Check

When discussing this plan, the key questions are:

1. Does every new theorem preserve the original dependency direction?
2. Is mathlib being used as implementation language rather than ontology?
3. Are comparison maps explicit whenever two presentations are identified?
4. Are projective structures downstairs being stated as descended structures
   rather than linear artifacts?
5. Are anomalies and projector mismatches derived only after the comparison
   surface exists?

## Bottom Line

The projective redline is to be followed literally.

The intended end state is not:

- old projective root removed
- new mathlib root installed

The intended end state is:

- original projective root preserved
- mathlib presentation made fully explicit
- the two shown to be isomorphic from the same seed
- both languages kept alive, with explicit junctions between them

That is the canonicalization target.
