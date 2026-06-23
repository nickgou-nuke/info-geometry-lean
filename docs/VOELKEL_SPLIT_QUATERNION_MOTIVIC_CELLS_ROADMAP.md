# Voelkel Split-Quaternion Motivic Cells Roadmap

**Source:** Konrad Voelkel, *Motivic Cell Structures for Projective Spaces over
Split Quaternions*, PhD thesis, Freiburg, 2016.

**Local file:** `/home/goutev/Downloads/collection_for_formalization/thesis.pdf`

**Alexandria artifact record:**
`artifacts/alexandria/external/voelkel_split_quaternion_thesis.md`

**PDF metadata:** 75 pages; MSC2010 `14F42,17A75,20Gxx`; keywords
`quaternions`, `octonions`, `motivic`, `cellular`, `hopf`; license metadata
reports `CC BY-NC-ND 3.0 Germany`.

**Status:** source-ingestion and formalization roadmap; no new theorem authority.

## Scope

This note records the theorem-shaped material from Voelkel's thesis that is
most relevant to the repository's split-composition-algebra, Klein quadric, and
motivic-cell lanes.  It is intentionally a roadmap, not a replacement for a
Lean proof.

The main formalization target is the split quaternionic projective-space cell
theorem:

```text
HP^n has an unstable motivic cell structure built inductively over HP^(n-1).
In particular HP^1 is the motivic sphere S^(4,2).
```

The thesis also supplies useful finite algebra targets for split composition
algebras, Zorn vector matrices, half-invertibility, projectors, affine-bundle
charts, and the OP1/OP2 obstruction boundary.

## Source Anchors

Use these thesis landmarks as the citation spine for future Lean owners:

- **Definition 4.1.7:** `D P^n = {A | A^2 = A, tr A = 1}` in hermitian
  matrices over a split composition algebra.
- **Definition 4.1.14 / 4.1.16:** the `D`-sphere and projection
  `p : D S^n -> D P^n`, `v |-> v v^*`.
- **Lemma 4.3.1:** split-complex `CP^n` facts and Jouanolou-torsor picture.
- **Lemma 4.4.1:** split-quaternionic `HP^n` facts, including the open
  embedding into a Grassmannian and complement geometry.
- **Theorem 4.4.6:** `HP^1` over a field is the motivic sphere `S^(4,2)`.
- **Theorem 4.4.8:** `HP^n` over a field has an unstable motivic cell
  structure obtained inductively from `HP^(n-1)`.
- **Lemma 4.5.2:** the OP1 associator vanishing calculation under explicit
  half-inverter/projector coordinate hypotheses.
- **Theorem 4.5.4:** `OP1` over a field is the motivic sphere `S^(8,4)`.
- **Conjectures 2 and 3:** OP2 and the fully explicit inductive cell structure
  remain open/conjectural in the source and must not be promoted to closed Lean
  theorems.

## Already Relevant Repo Anchors

- `InfoGeometry.Projective.SplitOctonions.ZornMatrix`
- `InfoGeometry.Projective.KleinQuadricTime`
- `InfoGeometry.Projective.KleinQuadricMonodromy`
- `InfoGeometry.Projective.SplitOctonions.*`
- `InfoGeometry.Canonical.FierzKleinFoundation`
- `InfoGeometry.Canonical.OperatorErlangenFierzKlein`

The current Zorn matrix lane already cites Voelkel Chapter 3 and formalizes
finite diagonal associativity facts in the same spirit as Lemma 3.1.13.

## Stable Source Targets

These are the source statements worth turning into Lean owners, in increasing
order of dependency.

### Composition Algebra Coordinates

1. Zorn vector matrix conventions for split composition algebras.
2. Norm formula in the chosen half/other-half coordinates.
3. Diagonal associativity identities for split octonions.
4. `half(x)=0 -> half(x*y)=0`.
5. Half-invertibility construction when a half-coordinate is invertible.
6. Free/transitive additive action on half-inverters for split complex and
   split quaternion cases.

### Projective Space Over Split Composition Algebras

1. Hermitian matrix model `D P^n = {A | A^2=A, tr A=1}`.
2. Dimension readout `dim(DP^n)=d*n` as a later algebraic-geometry target.
3. Identification of `CP^1`, `HP^1`, `OP^1` with even split affine quadrics.
4. Projection `p : DS^n -> DP^n`, `v |-> v v†`.
5. Surjectivity of `p` on local-ring points and chart sections.
6. Retraction and vector-bundle stratum `V_n -> DP^(n-1)`.

### Motivic Cell Targets

1. Homotopy purity interface for closed immersion/complement data.
2. Thom-space cellularity under trivialized local charts.
3. Split complex projective spaces have unstable motivic cell structures.
4. Split quaternionic projective spaces have unstable motivic cell structures.
5. `HP^1` is `S^(4,2)` in motivic homotopy.
6. `OP^1` is `S^(8,4)`.

### Open Octonionic Boundary

1. `OP^2` has expected cells `0`, `S^(8,4)`, `S^(16,8)` from motive/K-theory
   evidence.
2. A missing affine subspace/affine-bundle construction prevents the same proof
   strategy from closing for `OP^2`.
3. The suspension `Σ OP^2` has an equivariant-completion route via `E6/P1` and
   `F4/P1`, but this is not the same as an unstably cellular `OP^2` theorem.

## Suggested Lean File Split

### `InfoGeometry.Projective.SplitCompositionHalf`

Finite algebraic facts about the half/other-half coordinate system:

- half projection definitions;
- norm pairing readout;
- half-stability under multiplication;
- half-inverter data and additive-parameter readbacks.

This should be mostly finite algebra over a commutative ring, with explicit
assumptions where split quaternion/octonion cases diverge.

### `InfoGeometry.Projective.SplitCompositionProjectiveSpace`

Hermitian projector model:

- record-level definitions for `HermitianProjector`;
- trace-one/idempotent readbacks;
- finite chart predicates;
- projection `sphereToProjective`.

Avoid proving algebraic geometry claims such as dimension or smoothness until
the exact local ring/variety framework is available.

### `InfoGeometry.Projective.SplitQuaternionMotivicCells`

Motivic-cell interface:

- plain structures for the data required by homotopy purity;
- conditional theorems saying the cell theorem follows from explicit premises;
- source theorem names in comments, not hidden proof fields.

This file should not claim a completed motivic homotopy theorem unless the
homotopy-purity and Thom-space machinery has been formalized or explicitly
imported as theorem parameters.

## Interface Theorem Shapes

### Half-Inverter Readback

```lean
structure HalfInverterData (D R : Type*) where
  y : D
  x : D
  norm_x_eq_one : Norm x = 1
  half_yx_eq_e1 : half (y * x) = e1
```

Target theorem:

```lean
theorem half_inverter_readback
    (H : HalfInverterData D R) :
    Norm H.x = 1 /\ half (H.y * H.x) = e1 := ...
```

### Projector Projection Readback

```lean
structure SphereProjectorData where
  v : Sphere D n
  A : HermitianMatrix D (n+1)
  A_eq_vvdagger : A = vvdagger v
```

Target theorem:

```lean
theorem sphere_projection_is_idempotent
    (D : SphereProjectorData) :
    D.A * D.A = D.A := ...
```

This theorem is finite algebraic only.  Surjectivity of the projection is a
separate chart/local-ring theorem.

### Conditional Motivic Cell Owner

```lean
structure SplitQuaternionCellPremises where
  homotopyPurity : Prop
  bigCellContractible : Prop
  normalBundleThomCellular : Prop
  attachingMapIdentified : Prop
```

Target theorem:

```lean
theorem split_quaternion_projective_space_cell_structure
    (P : SplitQuaternionCellPremises)
    (hP : P.homotopyPurity /\ P.bigCellContractible /\
          P.normalBundleThomCellular /\ P.attachingMapIdentified) :
    SplitQuaternionCellStructure n := ...
```

The conclusion must be a real formal object only after the repository owns a
definition of motivic cell structure.  Until then, use an explicit proposition
parameter rather than a fake record field.

## Open Debt

1. **Motivic homotopy foundations.**
   The repository does not yet own the Morel-Voevodsky homotopy-purity theorem,
   Thom-space cellularity, or Dugger-Isaksen motivic cellularity in a way strong
   enough to prove Voelkel's main theorem directly.

2. **Algebraic-geometry infrastructure.**
   Dimension, smoothness, local-ring point surjectivity, affine bundle charts,
   and Grassmannian embeddings need explicit schemes/varieties infrastructure
   or imported theorem parameters.

3. **Split quaternion chart proof.**
   The key `HP^n` proof depends on half-inverters and affine-bundle
   trivializations.  These are good finite algebra targets, but the global
   geometric gluing still needs an owner.

4. **OP2 remains conjectural in the source.**
   Do not promote an unstable motivic cell structure for `OP^2`; the thesis
   presents this as an open conjectural lane.

5. **Physical/Klein/time interpretation gate.**
   Voelkel's thesis supports split composition algebra and motivic cell
   geometry.  It does not prove the repository's DIII horizon, MZM, log-time,
   or black-hole interpretation layers.

## Verification Plan

For any Lean file created from this roadmap:

```bash
lake env lean lean/InfoGeometry/Projective/<NewFile>.lean
lake build InfoGeometry.Projective.<NewFile>
rg -n "sorry|admit|axiom|: True := by|theorem .*: True|_valid|_certificate|law_holds" \
  lean/InfoGeometry/Projective/<NewFile>.lean
```

If a theorem uses motivic homotopy, algebraic geometry, or global topology, it
must depend on explicitly named theorem parameters until those foundations are
formalized in the repository.
