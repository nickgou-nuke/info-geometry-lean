# Native closure specification for `Aut(𝕆_s(ℝ)) ≃* G₂^{split}(ℝ)`

Status: open native Lean closure debt.

This document is not a proof certificate and does not promote the external
computer-algebra outputs into Lean theorems.  It records the exact mathematical
content required to replace the current `ClassificationCertificate.autEquivG2`
field with a native theorem.

## Hash-selected owner

The ASTAQLHASH audit selected the used owner
`ClassificationCertificate.classification_certificate_packet` by the literal
`valueFingerprint.shapeHash` class
`2371447881021695534`.

The unsupported field is:

```lean
ClassificationCertificate.autEquivG2 : Aut ≃* G2
```

The packet's other readbacks are conditional consequences of this field or
independent algebraic facts.  No renaming, alias, projection, or field removal
repays this debt.

## Exact evidence actually recomputed

All lanes below were executed from the repository sources.

| lane | verified result | authority boundary |
|---|---|---|
| SymPy | Zorn derivation matrix `512 × 64`, rank `50`, nullity `14`; exact bracket closure; center nullity `0`; structure constants denominator `1` | computational rational linear algebra only |
| Sage | same rank/nullity; `G₂` has `12` roots, `6` positive roots, Weyl order `12`; Chevalley Lie dimension `14` | computational root/Lie ledger |
| GAP | dihedral Weyl ledger has order `12` | Weyl-group order only; not real automorphism-group classification |
| Singular | rank/nullity ledger passes | scalar ledger only |
| Macaulay2 | rank/nullity ledger passes | scalar ledger only |
| Macaulay2 Dmodules | Weyl commutators; six positive-root forms; holonomicity of the constant-coefficient Cartan-chart module | D-module chart sanity check, not group integration |
| Clifford | `Cl(5,5)` dimension `1024`, pseudoscalar square `1` | signature sanity check |
| Galgebra | positive and negative generator squares agree with the declared split signature | signature sanity check |
| Coq | arithmetic packet and explicit status `characteristic_zero_derivation_evidence` | explicitly does not prove native group equivalence |
| Isabelle/HOL | arithmetic packet and explicit status not `NativeGroupEquivalence` | explicitly does not prove native group equivalence |
| Lean | native `rot01Real` derivation and exact packet readbacks compile | one derivation witness, not dimension/classification |

The exact SymPy CA artifact is:
`tools/infra/real_split_g2_classification/artifacts/real_split_g2_exact_ca_certificate.json`.

## The theorem that must replace the field

The final theorem must have a concrete, non-certificate statement.  The
repository must first define a real split `G₂` group, rather than using an
uninterpreted `G2` type:

```lean
structure SplitRealG2 where
  carrier : Type
  group : Group carrier
  lieAlgebra : LieAlgebra ℝ carrier
  -- concrete root/Chevalley data, not a proposition field
```

The final theorem should then be an actual construction:

```lean
noncomputable def realSplitOctonionAutEquivG2 :
    RealSplitOctonionAut ≃* SplitRealG2 :=
  ...
```

The ellipsis cannot be filled by the current evidence.  It requires the
following native owner chain.

## Required native owner chain

### 1. Concrete real Zorn algebra

The canonical carrier must expose the full real algebra structure and the
conjugation/norm identities:

```lean
@[simp] theorem detZ_mul (X Y : ZornMatrix ℝ) :
  detZ (X * Y) = detZ X * detZ Y

theorem conjugate_mul (X Y : ZornMatrix ℝ) :
  conjugate (X * Y) = conjugate Y * conjugate X

theorem mul_conjugate (X : ZornMatrix ℝ) :
  X * conjugate X = detZ X • (1 : ZornMatrix ℝ)
```

These must be proved from the canonical Zorn product in Lean.  The current
`SplitOctonionAutomorphism.lean` defines `detZ` but does not yet provide this
real native identity chain.

### 2. Automorphisms preserve norm natively

After the conjugation identities exist, prove—not assume—that every algebra
automorphism preserves the norm:

```lean
theorem RealSplitOctonionAut.preserves_detZ
    (φ : RealSplitOctonionAut) (X : ZornMatrix ℝ) :
    detZ (φ X) = detZ X := by
  ...
```

The proof must use preservation of `1`, multiplication, and the uniqueness of
the scalar coefficient in the conjugation identity.  A
`PreservesDetZ` structure field is not an acceptable substitute.

### 3. Derivation Lie algebra as a genuine finite-dimensional subspace

Define the real-linear derivation space as a `LieSubalgebra`, not a natural
number constant:

```lean
def splitOctonionDerivations : LieSubalgebra ℝ
    (ZornMatrix ℝ →ₗ[ℝ] ZornMatrix ℝ) := ...
```

The carrier predicate must state linearity and the Leibniz identity.  Prove
closure under the commutator natively:

```lean
theorem derivation_commutator_mem
    {D E : splitOctonionDerivations} :
    ⁅D, E⁆ ∈ splitOctonionDerivations := by
  ...
```

The existing `bracket_closed` theorem is useful algebraic evidence, but it is
currently stated over function-shaped data and does not establish the finite
real linear subspace dimension.

### 4. Export and verify the exact 14-dimensional basis

The SymPy/Sage nullspace basis must be exported as exact rational matrices,
with a stable row/column convention.  For each exported matrix `B i`, Lean
must prove:

```lean
theorem basis_is_derivation (i : Fin 14) :
  IsDerivation (basisDerivation i) := by
  ...

theorem basis_independent :
  LinearIndependent ℝ basisDerivation := by
  ...

theorem every_derivation_span :
  ⊤ ≤ Submodule.span ℝ (Set.range basisDerivation) := by
  ...
```

Only after these two directions are kernel-checked may Lean prove:

```lean
theorem derivation_finrank :
  Module.finrank ℝ splitOctonionDerivations = 14 := by
  ...
```

The current files contain one native rotation witness (`rot01Real`) and the
external integer `g2_dim := 14`; that is not this theorem.

### 5. Native bracket table and Killing form

Define the bracket coordinates from the exported basis and prove the exact
structure constants in Lean.  Then define the Killing form from the adjoint
maps and prove:

```lean
theorem killing_rank : Module.finrank ℝ splitOctonionDerivations = 14 := by ...

theorem killing_inertia :
  inertia (killingForm splitOctonionDerivations) = (8, 6, 0) := by ...
```

The external `(8,6,0)` result is evidence for this target; it is not a proof
of it.  A natural-number field in `ExactComputerAlgebraPacket` cannot establish
inertia.

### 6. Native split `𝔤₂` identification

A 14-dimensional Lie algebra with the observed Killing inertia is not, by
itself, enough to identify the Lie algebra as split `𝔤₂`.  Lean must construct
the root decomposition and verify the Chevalley relations:

```lean
def splitG2LieAlgebra : LieAlgebra ℝ (Fin 14 → ℝ) := ...

def derivationLieEquivSplitG2 :
    splitOctonionDerivations ≃ₗ⁅ℝ⁆ splitG2LieAlgebra := ...
```

Required native sublemmas include the two simple-root generators, the six
positive roots, the six negative roots, the rank-two Cartan space, and all
bracket relations.  The Sage/GAP root count and Weyl order guide this
construction but do not supply its Lean proof.

### 7. Lie algebra of the automorphism group

The missing bridge is not merely a dimension equality.  Construct the Lie
subgroup/manifold structure on `RealSplitOctonionAut` and prove:

```lean
theorem lieAlg_realSplitOctonionAut_equiv_derivations :
  LieAlgebra.ofReal (LieAlgebra.of ... RealSplitOctonionAut)
    ≃ₗ⁅ℝ⁆ splitOctonionDerivations := ...
```

This requires a native smooth/finite-dimensional automorphism-group surface.
No current repository artifact supplies this.

### 8. Global integration and group equivalence

Finally prove the global statement, including the kernel and connectedness
issues:

```lean
noncomputable def realSplitOctonionAutEquivG2 :
    RealSplitOctonionAut ≃* SplitRealG2 := ...
```

The proof must establish:

1. the exponential/local integration map;
2. surjectivity onto the real split group;
3. the kernel is trivial (or account for the exact central quotient);
4. the correct connected component/global topology;
5. no identification with the finite group `G₂(2)` of order `12096`.

The current CA and proof-assistant evidence does not address these points.

## Honest current replacement boundary

The strongest theorem that can currently be promoted natively is the existing
finite derivation witness and the exact algebraic closure facts already proved
in the owner files. The following claims must remain open:

- `Aut(𝕆_s(ℝ)) ≃* G₂^{split}(ℝ)`;
- derivation-space dimension `14` as a Lean theorem;
- native Killing-form inertia `(8,6,0)`;
- native identification `Der(𝕆_s) ≅ 𝔤₂^{split}`;
- Lie-group integration from derivations to automorphisms.

This is the complete mathematical content needed to close the hash-selected
hole. The external engines have completed their evidence lanes; the remaining
work is a genuine native algebra/Lie-group formalization, not a certificate
readback.
