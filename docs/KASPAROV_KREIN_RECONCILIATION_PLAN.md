# Real Hilbert / Double Real Krein Reconciliation Plan

Status: source-grounded implementation plan; not a theorem certificate.

## 1. Scope and truth boundary

The primary lane is real:

```
E over ℝ
  → DoubledSpace E
  → HilbertDoubled E (only when a ULift carrier is required)
  → KreinSpace / KreinGradedModule
  → RealSplitCl11Action
  → RealSplitKreinKasparovCycle
```

The source of truth is the kernel-checked owner code. Documentation, graph
searches, generated transcripts, physical interpretations, and oracle answers
may locate a declaration or suggest a contract, but they do not prove one.

This plan does **not** assume a complex Hilbert carrier, a standard analytic
Kasparov module, a genuine right `B`-module, an infinite-dimensional index, or
an analytic colimit theorem. Each requires a separate construction and proof.

## 2. Existing owners

| Responsibility | Owner |
|---|---|
| Real fundamental symmetry, Krein pairing, Krein adjoint | `lean/InfoGeometry/Krein/KreinSpace.lean` |
| Real doubled carrier and sheet operators | `lean/InfoGeometry/Krein/DoubledSpace.lean` |
| `ULift` real Hilbert wrapper and carrier equivalences | `lean/InfoGeometry/Krein/HilbertBridge.lean` |
| Real grading and symmetric Clifford action | `lean/InfoGeometry/Krein/Clifford.lean` |
| Real split `Cl(1,1)` record and doubled seed | `lean/InfoGeometry/Quantum/RealSplitClifford.lean` |
| Primitive bounded real split-Krein cycle | `lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean` |
| Compatibility abbreviation and finite index surface | `lean/InfoGeometry/KK/KasparovCycle.lean` |
| Resolvent-backed bounded phase scaffold | `lean/InfoGeometry/KK/RealSplitKreinBoundedTransform.lean` |
| Finite Clifford projection | `lean/InfoGeometry/Canonical/RealDoubledCliffordFiniteSpine.lean` |
| Real doubled mirror/block operators | `lean/InfoGeometry/Canonical/RealDoubledKreinMirror.lean`, `lean/InfoGeometry/Algebra/ChiralDoubledRealBlock.lean` |
| Real phase readout adapter | `lean/InfoGeometry/Canonical/BipolarRealDoubledKreinBridge.lean` |
| Two-sheet filtered-colimit interface | `lean/InfoGeometry/Categorical/TwoSheetKreinFilteredColimit.lean` |

`KasparovCycle` is an abbreviation of `RealSplitKreinKasparovCycle`; it is
not a second owner. The bounded-transform file stores a compact-resolvent phase
and requires oddness, Krein-skew-adjointness, and square-defect compactness as
fields. It does not prove the analytic formula `D (1 + D²)^(-1/2)`.

## 3. The five structures that must remain distinct

For `DoubledSpace E`, never identify these by name or analogy:

| Structure | Role |
|---|---|
| `KreinSpace.J` / `KreinSpace.jCLM` | Fundamental symmetry used by `kreinInner` and `kreinAdjoint`; on the canonical doubled instance this is the sign-flip implementation. |
| `DoubledSpace.modular_j` | Sheet swap; used by `doubledCarrier` and the real split `Cl(1,1)` seed. |
| `DoubledSpace.spectral_epsilon` | Sheet sign flip; the other real split `Cl(1,1)` generator and the canonical Krein symmetry on the doubled instance. |
| `KreinGradedModule.gradeCLM` | Independent grading operator `Γ`; it is neither `modular_j` nor `spectral_epsilon` by default. |
| `RealSplitCl11Action.J`, `.eps`, `.K` | Record fields for the split action, with `.K := J.comp eps`; they are not typeclass projections. |

`complex_i` and `clockAxis` are real-linear operators with square `-id`.
Their names describe a complex-like axis on a real carrier; they do not change
the scalar field to `ℂ`.

`doubledCarrier` packages `J := modular_j` and `ε := spectral_epsilon` as
an `InvolutiveSelfDualCarrier`. That package is not definitionally a
`KreinSpace`. A theorem relating the two packages must state and prove the
intertwining map explicitly.

## 4. Mathlib boundary

Use existing Mathlib structures as the generalized layer:

- `NormedAddCommGroup`, `InnerProductSpace ℝ`, `CompleteSpace`, and
  `NormedSpace ℝ` for real Hilbert carriers;
- `ContinuousLinearMap` and `LinearIsometryEquiv` for bounded maps and carrier
  equivalences;
- `ContinuousLinearMap.adjoint` for Hilbert adjoints;
- `IsCompactOperator` for compact defects;
- finite-dimensional modules and `Module.finrank` only under explicit finite
  hypotheses.

The repository's `KreinSpace`, `KreinGradedModule`, and
`RealSplitKreinKasparovCycle` remain the owners of the extra structure. Do not
invent parallel classes merely to resemble complex Hilbert or standard KK
terminology.

## 5. Reconciliation laws

### 5.1 One owner per concept

New modules import an owner and prove an instance or transport theorem. They do
not redeclare a doubled carrier, Krein adjoint, grading, split Clifford action,
or bounded cycle.

### 5.2 Every change of carrier has an explicit map

Use an actual real equivalence, for example `H₁ ≃ₗᵢ[ℝ] H₂` or a proved
continuous-linear equivalence. A substantive transport theorem must preserve,
with explicit equations:

1. addition and real scalar multiplication;
2. composition of bounded operators;
3. the selected fundamental symmetry and Krein pairing;
4. Hilbert and Krein adjoints;
5. grading and odd/even predicates;
6. split `Cl(1,1)` fields `J`, `eps`, and `K`;
7. representations `π` and `ρ`, phase `F`, compact defects, and finite index
   when a cycle is transported.

An identity map or a proposition field that assumes the target statement is not
an isomorphism or soldering form.

### 5.3 Finite remains finite

Matrix and Clifford certificates may instantiate a finite real carrier. They do
not establish analytic, infinite-dimensional, colimit, equivariant, or standard
Kasparov theorems without additional owner-level hypotheses and proofs.

## 6. Exact target contracts

The following are implementation targets, not declarations already present.
They must be checked against imports and proved without placeholders.

### 6.1 Real Krein transport

For real Hilbert carriers with `KreinSpace` instances, given a real linear
isometry `eH : H₁ ≃ₗᵢ[ℝ] H₂` and an explicit intertwining equation

```lean
eH.toLinearIsometry.toContinuousLinearMap.comp
    (KreinSpace.jCLM (H := H₁))
  = (KreinSpace.jCLM (H := H₂)).comp
      eH.toLinearIsometry.toContinuousLinearMap
```

prove non-vacuous consequences:

```lean
∀ u v : H₁,
  KreinSpace.kreinInner (H := H₂) (eH u) (eH v)
    = KreinSpace.kreinInner (H := H₁) u v
```

and transport of `KreinSpace.kreinAdjoint` under conjugation. The
intertwining equation alone is not evidence for the adjoint theorem; the
Hilbert-adjoint calculation must be proved.

### 6.2 Double real `Cl(1,1)` packet

For `H := DoubledSpace E`, prove or reuse:

```
modular_j² = id
spectral_epsilon² = id
modular_j ∘ spectral_epsilon = -(spectral_epsilon ∘ modular_j)
complex_i² = -id
```

The existing `doubledSpaceCl11Action` must be related field-by-field:

```
cl11.eps = spectral_epsilon
cl11.J   = modular_j
cl11.K   = complex_i
```

No statement in this packet may identify `modular_j` with
`KreinSpace.jCLM` or with `gradeCLM` unless a separate theorem supplies
that equality.

### 6.3 Grading transport

For `KreinGradedModule` instances and a real isometry `eH`, state the
explicit intertwining equation for `KreinGradedModule.gradeCLM`. Prove
separately that the conjugated operator is even iff the original is even, and
odd iff the original is odd. Do not collapse both into an untyped “grading
preserved”.

### 6.4 Cycle transport

Only after the carrier, symmetry, grading, and split-action packets close may a
future owner introduce a cycle transport constructor. Its hypotheses must bind
all of `A`, `B`, `H₁`, `H₂`, the real algebra instances, the carrier
isometry, the three symmetry packages, `cl11`, `π`, `ρ`, `F`, oddness,
Krein-skew-adjointness, and every compact defect. Finite index preservation
requires an explicit finite-dimensional hypothesis.

The current cycle's `ρ` remains a second even representation; do not call it a
right module without constructing the module law.

## 7. Execution order

### Phase 0 — inventory

Search all owner and consumer files for `KreinSpace`, `DoubledSpace`,
`modular_j`, `spectral_epsilon`, `gradeCLM`, `RealSplitCl11Action`, and
cycle transport. Record declarations, imports, instances, and dependents. “Not
found in this search” is not a repository-wide absence claim.

### Phase 1 — real carrier slice

Reuse the existing `HilbertBridge` equivalences between `DoubledSpace E` and
`HilbertDoubled E`. Add only missing real symmetry, grading, and operator
intertwining lemmas. Do not rebuild the wrapper.

### Phase 2 — doubled real Krein slice

Close the `J`, `ε`, `K`, projector, and Krein-pairing laws using the existing
`DoubledSpace`, `PolarizedSector`, and
`DoubleRealKreinProjectorPairing` owners. Keep sheet swap and sign flip
separate in every theorem statement.

### Phase 3 — real Clifford and finite instances

Use `RealDoubledCliffordFiniteSpine`, `RealDoubledKreinMirror`, and
`ChiralDoubledRealBlock` as instances of the canonical real carrier. Do not
replace the owner layer with matrices. Use
`BipolarRealDoubledKreinBridge` only for an explicitly proved real phase
readout.

### Phase 4 — cycle boundary

Transport the real split action, representations, phase, compact defects, and
index only after Phases 1–3 are kernel-checked. Keep the bounded-transform
analytic gap visible in the type and documentation.

### Phase 5 — categorical extension

Use `TwoSheetKreinFilteredColimit` only from a real stage diagram and proved
stagewise compatibility. Do not infer a continuum theorem from finite matrices.

## 8. Verification gates

For every source slice:

1. inspect active compiler processes; never run concurrent builds;
2. run narrow `lake env lean` on the owner and direct bridge;
3. run the repository's locked Lake wrapper for the actual target;
4. run `git diff --check` and the applicable semantic-vacuity, proxy, axiom,
   and frontier checks;
5. inspect `#print axioms` for every new declaration;
6. search all consumers of changed declarations;
7. stage edits immediately with `git add -A`.

No `sorry`, `admit`, custom axiom, unsafe proof, `True` wrapper,
conclusion-restating hypothesis, or identity-valued substantive bridge is
accepted. Never run `lake clean`, delete `.lake/build` or `.lake/packages`,
or kill an active compiler task without authorization.

## 9. Completion criterion

The reconciliation is complete only when the requested real carrier theorem(s),
double-real-Krein identities, and cycle-level compatibility theorem(s) have
kernel-checked proofs; all affected consumers compile; the new declarations
have an acceptable axiom report; and the staged diff contains only intentional
source and plan changes. Any unresolved analytic Kasparov, right-module,
infinite-dimensional index, or colimit claim must remain explicitly labelled
as closure debt rather than being promoted by interpretation.

## 10. Implemented first slice

The first executable slice is now owned by

`lean/InfoGeometry/Krein/RealDoubledHilbertBridge.lean`.

It defines the real Krein isometry from `DoubledSpace E` to the existing
`HilbertDoubled E` wrapper and transports the canonical real split
`Cl(1,1)` action through the existing continuous-linear equivalence.  The
transported derived axis has a kernel-checked square-minus-one theorem.  This
slice deliberately adds no complex carrier, no new cycle structure, and no
identity-valued theorem wrapper.
