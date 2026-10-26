# Phase-flow / Zorn-BdG CAR comparison

Base: 2d3a6ed286fde7098d152b83c9c75580b98865d0 (26 October 2026).
Status: proof candidates until the scoped compiler and imported-environment audit pass.

## Carriers and owners

Reuse `SplitClifford.CARPair`, `concreteCARAnnihilation` and `concreteCARCreation`,
`phaseFlow` and `phaseConjugation`, `rightRegularCARPair`, and `fockBdGEquiv`.
No duplicate CAR predicate, nilpotent split, phase flow, or Zorn multiplication is added.

For a genuine CAR representation on a module V, let E = ker(ann).
The explicit splitting is E x E -> V, (x,y) -> cre(x)+y, with inverse
v -> (ann(v), v-cre(ann(v))). This proves dim(V)=2dim(E).

For each selected Zorn mode i, the eight-dimensional carrier therefore has a
four-dimensional multiplicity kernel. Choose a linear equivalence from the
native Euclidean four-space to that kernel using `LinearEquiv.ofFinrankEq`.
Only this multiplicity-coordinate choice is noncanonical. The total carrier
map is the explicit CAR splitting above, not an arbitrary eight-dimensional
isomorphism. It identifies the existing doubled lowering/raising actions with
the actual Zorn right-regular annihilation/creation pair.

The transported grading is cre ann - ann cre; the phase axis is ann - cre.
The target phase flow is cos(theta) I + sin(theta) (ann-cre).
The source uses the existing convention R(-theta) T R(theta).
At theta=pi/4, annihilation -> (epsilon+K)/2 and creation -> (epsilon-K)/2.
Their ordered products are gradePlusProj and gradeMinusProj respectively.

The same target phase action intertwines via the existing fockBdGEquiv with
cos(theta) I + sin(theta) (exterior contraction_i - exterior wedge_i).
The doubled-to-Fock comparison is composition with fockBdGEquiv.symm.

## Scope boundaries

These are linear representation equivalences and intertwining identities.
They are not multiplicative equivalences to the nonassociative Zorn algebra.
No Zorn norm or isometry is asserted for the dimension-based multiplicity choice.
Each i chooses one mode; no one-dimensional CAR pair is claimed to encode the
three independent modes simultaneously without the multiplicity action.
No vacuum, modular state, Unruh-DeWitt detector, Fermi-Dirac occupation,
Berezinian, entropy, or unbounded-generator theorem is introduced.
Conjugation preserves squares; it does not turn a square-one Majorana into a
nilpotent. All constants, signs, and carrier dimensions remain explicit.

## Verification

The new wrapper reuses the current strict scoped checker without editing it.
It preserves exact root Lean/Mathlib pins, imports, and dependency source.
All four new modules must compile together and pass public Lean.collectAxioms
with only propext, Classical.choice and Quot.sound. No exemptions are added.
An unresolved existing import or failed owner blocks certification, not a
license to strip that dependency. This is not a full root-Lake/All.lean build.
