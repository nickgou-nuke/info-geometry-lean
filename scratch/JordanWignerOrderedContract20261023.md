# Ordered Jordan–Wigner candidate: owner gap and consumer boundary

Source: `scratch/JordanWignerOrdered20261023.lean`, SHA256
`cbde9b0bd6f70e2b68b5ebd9bd56dc3a380ccb2de2e24539675e1f6e120935f3`.
**Uncompiled proposal**, not kernel acceptance. This contract adds no Lean code,
new carrier, master bundle, witness structure, or promotion claim.

## Existing owners and precise delta

- `Algebra.PeirceDeWittChiralSplit.grading` and `grading_sq`: native grading of
  complementary idempotents. Candidate uses this definition and square theorem.
- `Core.PeirceGrading.reflection`, `reflection_sq`: native division-free
  reflection `2*p-1`; not a new parity carrier to reconstruct.
- `Core.DiracSuperalgebra`: square-zero MP-pair supports, Majorana and involution
  identities. These do not themselves give arbitrary-site ordered prefixes from
  commuting local pairs.
- `Clifford.JordanWignerCAR` and `Clifford.Cl11JordanWignerCARBridge`: genuine
  finite matrix/tensor tower CAR, including indexed mixed CAR.
- `Physics.ColorCARJordanWigner`: actual three-mode tensor-carrier CAR.
- `Physics.JordanWignerMultiDyads`: categorical dyad recurrence and site-zero /
  zero-versus-successor results; not this primitive ring-family interface.

The source-confirmed gap, consistent with James's mapping relayed by parent, is
an arbitrary-ring ordered-prefix sign derivation and dressed CAR from on-site
nilpotence/normalization plus off-site commutation. This is not an absence claim
about JW, finite CAR, or categorical towers generally. Existing owners remain.

## Primitive hypotheses and parity convention

For arbitrary `[Ring R]`, `d B : Fin N → R`, assume for each i:

```text
d_i*d_i = 0
B_i*B_i = 0
d_i*B_i + B_i*d_i = 1                       (hn)
```

At distinct sites every choice of d/B commutes with every choice at the other
site. Candidate expresses precisely those four commutations using Bool `site`;
it does not assume the dressed CAR as a premise. No star, characteristic-zero,
nontriviality or division-by-two assumption enters the ring construction.

Put `p_i = d_i*B_i`. The candidate derives idempotence, then uses native parity

```text
P_i = grading(p_i) = p_i - (1-p_i) = 2*d_i*B_i - 1.
```

Under hn, `1-p_i = B_i*d_i`, hence **P_i = d_i*B_i - B_i*d_i**.
The first equality with `2*p_i-1` is a ring identity; the support-difference
identification uses hn. No swapped-sign convention is implicit. These identities
are mathematical interpretation of the native definition, not separately named
or kernel-checked new lemmas in the sandbox. Characteristic two is allowed;
square-zero is asserted independently of the weaker self-anticommutator law.

Ordered prefix: `K_0=1`, `K_(k+1)=K_k*P_k`, in increasing site order. The Nat
extension uses factor 1 beyond N, but every dressed Fin N site uses only earlier
valid indices. No ordinary Finset.prod and no ambient commutativity assumption.
Define `D_i=K_i*d_i`, `C_i=K_i*B_i` (candidate `dressed ... false/true`).

## What the candidate actually proposes

Named lemmas derive prefix square/commutation/sign, on-site product preservation,
full dressed CAR and separate square-zero:

```text
D_i*D_j + D_j*D_i = 0
C_i*C_j + C_j*C_i = 0
D_i*C_j + C_j*D_i = if i=j then 1 else 0
D_i*D_i = 0;  C_i*C_i = 0.
```

Adjoints are a separate section: `[StarRing R]` and explicitly `B_i=star(d_i)`.
Then parity/prefix are self-adjoint and `star(D_i)=C_i`, `star(C_i)=D_i`.
The letter B alone never means adjoint, MP inverse, positivity or Hilbert adjoint.

## Inverse distinction — do not overread the current lemma

`inverse_dressing` currently says **K_original,i * dressed_i = local_i**.
It is involutive multiplication by a fixed original involution K_i. Its docstring
must not be interpreted as a fully established inverse using only dressed data.
The original prefix is an explicit part of that theorem's inputs/definition.

`dressed_same_product` supplies the necessary intermediate identities
`D_i*C_i=d_i*B_i` and `C_i*D_i=B_i*d_i`. Therefore the mathematical route to a
solely-dressed-data inverse is:

1. Define recovered parity `P'_i=grading(D_i*C_i)` (equivalently
   `2*D_i*C_i-1`, or `D_i*C_i-C_i*D_i` using dressed normalization).
2. Prove `P'_i=P_i` from the on-site product lemma.
3. Define its increasing ordered prefix K'_i and prove `K'_i=K_i` by recurrence.
4. Conclude `K'_i*D_i=d_i` and `K'_i*C_i=B_i`.

Those explicit reconstruction statements are **not yet declared in this
candidate**. They are a small prospective extension, not an accomplished full
inverse API. Do not apply the commuting-site CAR theorem to the already dressed
family: its off-site hypotheses are commutation, whereas dressed sites
anticommute. An inverse starting from arbitrary CAR data additionally needs its
own proof of recovered local commutation and both round trips; no general
bijection or algebra equivalence is asserted here.

## Consumer boundary

Consumers may instantiate the generic ring with an existing native operator,
matrix or tensor carrier only after supplying its actual primitive local laws.
A finite matrix carrier is an instance, not a replacement for categorical owners.
No theorem here identifies a generic family with any existing finite tower or
passes it to an inductive colimit without an explicit compatibility map.

No Spin/Pin classification, thermal state, Bogoliubov star automorphism, locality
classification, continuum limit or representation equivalence follows from these
statements. Promotion requires parent source review and later locked kernel QA;
this contract and the JW proof candidate remain uncompiled.
# Integration disposition (2026-10-23)

The parent removed the uncompiled live `Core/JordanWignerOrdered.lean` candidate after independent source review found overlapping concurrent owners `Core/BosonParityString.lean` and `Core/BosonMajoranaFermionTransmutation.lean`. This scratch candidate is retained as provenance only. The latter owners now also contain recoveredString/recover_modes, using output local commutators; their source correspondence is not a kernel acceptance claim. Do not promote both dressing implementations.

