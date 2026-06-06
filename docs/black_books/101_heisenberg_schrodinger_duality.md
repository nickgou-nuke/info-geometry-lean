# 101. The Heisenberg–Schrödinger Duality in Lean

## What the formalization revealed

The `modular_j_sectorSwap_projectors` theorem and the
`modular_j_comp_cl11Rep_pseudoscalar_eq_clockAxis` theorem are not two
theorems. They are one theorem in two languages.

| Side | File | Theorem | Object |
|------|------|---------|--------|
| Heisenberg | `OperatorDictionary.lean` | `modular_j_sectorSwap_projectors` | Projectors P₊ ↔ P₋ |
| Schrödinger | `Clifford/Lift.lean` | `modular_j_comp_cl11Rep_pseudoscalar_eq_clockAxis` | Pseudoscalar K² = -I |

The first speaks the language of operator algebras: modular conjugation,
sector swap, Jones index, Andreev reflection. The second speaks the language
of Clifford geometry: pseudoscalar inversion, clock axis, Möbius transform,
Poincaré compactification.

Both say the same thing: **the modular reflection J flips the grading**.

## Why this is not a pile of analogies

Previous attempts to unify these domains failed because they tried to
reduce one side to the other. The operator algebra cannot be reduced to
Clifford geometry — it is a different category of mathematical object.
And the Clifford carrier cannot be reduced to an operator algebra —
it carries the spinors that the operators act on.

What the repo now has is not a reduction but a **duality**: a pair of
theorems in different categories that are linked by a shared algebraic
kernel (the modular reflection J). Each side is autonomous. Neither
reduces to the other. But both are witnesses to the same structural spine.

## The Heisenberg layer

The operator side is Tomita–Takesaki theory on the doubled Krein space:

```
J (modular conjugation)  →  swaps P₊ ↔ P₋  →  sector exchange
```

This is the grammar of:
- Jones index for subfactors
- Andreev particle-hole reflection at a superconductor
- Brewster angle where the p-polarized reflection vanishes
- Bayesian reweighting (JKO proximal step as a sector swap)

All of these are instances of the same algebraic pattern: **an involution
that exchanges two complementary sectors of a graded algebra**.

## The Schrödinger layer

The spinor side is Clifford geometry on the Cl(1,1) carrier:

```
J (pseudoscalar)  →  defines K = J·ε, K² = -I  →  phase/inversion axis
```

This is the grammar of:
- Möbius inversion S : z ↦ -1/z
- Poincaré sphere compactification (outer cone ↔ inner cone)
- Dilation sign flip under inversion (S·D·S⁻¹ = -D)
- Upper/lower shear conjugation (S·T·S⁻¹ = lower shear)

All of these are instances of the same geometric pattern: **a reflection
that defines the orientation-reversing transformation of the carrier space**.

## The duality as an architectural principle

The two sides are linked by the `clockAxis` operator K = J·ε:

```
Operator side:   J (swap)      →  sector exchange P₊ ↔ P₋
                     ↓
               K = J·ε  (complex structure)
                     ↓
Clifford side:  K² = -I       →  phase axis, inversion, compactification
```

The operator `K = J·ε` is the **intertwiner**. It lives on both sides:
- As `clockAxis` in the Krein doubled space (operator representation)
- As the Cl(1,1) pseudoscalar readout (Clifford representation)

This is the Lean formalization's central architectural discovery: the
complex structure K is the bridge between the operator-algebraic and
geometric-spinor descriptions of the modular reflection.

## The Heisenberg–Schrödinger dictionary

| Classical debate | Repo formalization | Lean theorem |
|-----------------|-------------------|--------------|
| Heisenberg: operators evolve | algebra automorphism by J | `modular_j_sectorSwap_projectors` |
| Schrödinger: states evolve | carrier flow along K | `modular_j_comp_cl11Rep_pseudoscalar_eq_clockAxis` |
| Both are equivalent? | No — they are dual | K = J·ε is the intertwiner |

The historic mistake was to ask "which picture is correct?" The correct
question is "what operator intertwiners them?" The answer is K = J·ε —
the complex structure that the Krein swap and the Clifford pseudoscalar
both know about.

## What the codebase now contains

The two theorems that formalize this duality:

```
lean/InfoGeometry/Canonical/OperatorDictionary.lean
  modular_j_sectorSwap_projectors
    → J swaps the spectral projectors (Heisenberg side)

lean/InfoGeometry/Clifford/Lift.lean
  modular_j_comp_cl11Rep_pseudoscalar_eq_clockAxis
    → J·ε = K, K² = -I (Schrödinger side)
```

The SymPy witness chain that corroborates it:

```
tools/sympy/
  modular_j_krein_bridge.py         — J across Krein/Clifford/Möbius
  poincare_compactification.py      — S(z) = -1/z, outer↔inner cone
  optics_reflection_compactification_witness.py  — Jones/Brewster/Andreev
  jko_bayes_transport_witness.py    — JKO/Bayesian update as sector swap
```

## The next step

The natural next step is to formalize the intertwiner itself:

```lean
theorem clockAxis_as_intertwiner :
    clockAxis (E := E) = modular_j_comp_cl11Rep_pseudoscalar_eq_clockAxis (E := E) := ...
```

This theorem would state explicitly that the `clockAxis` operator — which
appears on the Krein side as the complex structure K = J·ε, and on the
Clifford side as the Cl(1,1) pseudoscalar readout — is the same operator.
This is the formal content of the Heisenberg–Schrödinger duality in this
codebase: the intertwiner is not a new object but the already-existing
`clockAxis`, which both sides already agree on.

Once this theorem is proved, the duality is closed at the theorem level.
The operator algebra and the Clifford geometry are not the same thing —
but they share a common intertwiner, and that is enough.
