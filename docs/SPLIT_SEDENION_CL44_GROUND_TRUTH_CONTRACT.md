# Ground-Truth Contract: split-sedenion ↔ Cl(4,4) minimal left ideal

> Status: `current authority` for this work item.
> Scope: what the repository **actually proves** about transporting the split-sedenion
> multiplication, conjugation, and norm onto the Cl(4,4) minimal left ideal.
> Rule: Lean owner source decides. Names in prose, reports, or transcripts do not.

Produced under `docs/REPO_DEEP_SEARCH_PROTOCOL.md`. Every claim below carries a
`file:line` provenance tag. Anything marked **NOT PROVED** is an open gap, not a
result.

---

## 0. Correction log (read this first)

Two claims circulated in a status report were **false as stated** and are corrected
here. Both errors came from *name-based* search rather than concept-based search —
the exact failure mode the protocol warns about.

| Claimed | Reality |
|---|---|
| "Certifies the 16D minimal-left-ideal equivalence `cl44MinimalLeftIdealSplitSedenionEquiv` (`LeftIdeal primIdem ≃ SplitSedenion ℝ`)" | **That exact name does not exist.** The content exists as `cl44MatrixLeftIdealSplitSedenionEquiv` at `Cl44MinimalIdealSplitSedenionEquivBridge.lean:236`. |
| "the 3 so(2,1) generators have linearly independent matrix entries ⇒ joint 17-parameter injectivity" | **The argument is invalid.** See §5. |

A second false negative occurred during discovery: a `head -8` truncation on a
multi-file grep hid `fin8ToZorn_add` / `fin8ToZorn_smul`, making them look absent.
They exist. **Truncated greps are not searches.**

---

## 1. Carriers and their owners

| Object | Definition | Owner |
|---|---|---|
| `Cl44` | `Matrix (Fin 16) (Fin 16) ℝ` | `Synthesis/Cl44PrimitiveIdempotentIdeal.lean:33` |
| `primIdem` | `E₀₀` | same file |
| `LeftIdeal f` | `Submodule ℝ Cl44` | same file |
| `ZornSplitOctonion R` | structure `a : R`, `u : Fin 3 → R`, `v : Fin 3 → R`, `b : R` | `Canonical/ZornSplitOctonionFin8Bridge.lean:231` |
| `SplitSedenion R` | `ZornSplitOctonion R × ZornSplitOctonion R` | `Synthesis/Cl44LeftIdealSplitSedenionSynthesis.lean:531` |
| `zornAdd`, `zornSmul` | componentwise add / scalar | `Canonical/SplitOctonionParaKahlerNullCone.lean:149,157` |
| `zornMul`, `zornNorm` | Zorn split-octonion product and quadratic | `Canonical/ZornSplitOctonionFin8Bridge.lean:324,332` |
| `sedenionMul/Conj/Norm` | Cayley–Dickson on the pair carrier | `Synthesis/Cl44LeftIdealSplitSedenionSynthesis.lean:573,564,579` |

### ⚠️ Duplicate-name hazard

A **second, unrelated** structure also named `ZornSplitOctonion` exists at
`OperatorAlgebra/GenericZorn.lean:22`, with flat fields `a b x0 x1 x2 y0 y1 y2`.
It is a *different carrier*. All work in this contract uses the
`ZornSplitOctonionFin8Bridge` one (fields `a, u, v, b`). Do not mix them.

---

## 2. What IS proved (owner-verified)

- `leftIdealEquiv : LeftIdeal primIdem ≃ₗ[ℝ] (Fin 16 → ℝ)` — a genuine `LinearEquiv`.
  `Synthesis/Cl44PrimitiveIdempotentIdeal.lean`. **Note this one is already linear.**
- `spinor16SplitSedenionEquiv : (Fin 16 → ℝ) ≃ SplitSedenion ℝ` — plain `Equiv`.
  `Cl44MinimalIdealSplitSedenionEquivBridge.lean:165`
- `cl44MatrixLeftIdealSplitSedenionEquiv : LeftIdeal primIdem ≃ SplitSedenion ℝ` —
  plain `Equiv`, defined as `leftIdealEquiv.toEquiv.trans spinor16SplitSedenionEquiv`.
  `Cl44MinimalIdealSplitSedenionEquivBridge.lean:236`
- Additivity of the composite: `cl44MatrixLeftIdealSplitSedenionEquiv_add`, same file.
- `fin8ToZorn_add`, `fin8ToZorn_smul`, `zornToFin8_zornAdd`, `zornToFin8_zornSmul`
  (generic over `R`). `Canonical/SplitOctonionClifford33Soldering.lean:304,313,292,298`
- `fin8ZornEquiv : (Fin 8 → R) ≃ ZornSplitOctonion R`
  `Canonical/ZornSplitOctonionFin8Bridge.lean:295`

## 3. Rank #3 — induced sedenion algebra: **module structure and bilinearity proved**

`Synthesis/Cl44InducedSplitSedenionAlgebra.lean` is the sole definition owner for the
transported operations. `Synthesis/Cl44MinimalIdealInducedSedenionProductBridge.lean` imports
that owner, adds module structure, and proves:

| Declaration | Line |
|---|---|
| `idealSedenionMul`, `idealSedenionConj`, `idealSedenionNorm` | `Cl44InducedSplitSedenionAlgebra.lean` |
| `idealSedenionAdd`, linear equivalence promotion | section 1 |
| `idealSedenionMul_add_left/right`, `idealSedenionMul_smul_left/right` | section 2 |
| `idealSedenionConj_involutive` | section 2 |
| `exists_idealSedenion_nonzero_associator`, `exists_idealSedenion_zero_divisors` | sections 2–3 |
| transported conjugate-norm zero criterion | section 1 |
| 14-parameter derivation transport | section 3 |
| spinor-carrier product transport and witnesses | section 4 |

So the *transport* and the listed finite witnesses are kernel-proved. The operation on the
principal ideal is defined through the carrier equivalence. It is **not** raw matrix
multiplication, nor does this establish a native `CliffordAlgebra` equivalence or minimality.
The induced-product bridge proves that the transported product is ℝ-bilinear. The raw
matrix product remains distinct from this transported multiplication.

## 4. Linear carrier structure: supplied by the induced-product bridge

The induced-product bridge equips its selected Zorn carrier and pair carrier with
componentwise `AddCommGroup` and `Module` instances, proves additivity and scalar homogeneity
of the pair product, and promotes the transport to a separate `LinearEquiv`. The original
carrier equivalence remains a plain `Equiv`. These are claims about the named carriers and
instances in the cited owner files; this contract makes no repository-wide absence claim.

### Precedent that makes this closable

`Canonical/SplitOctonionParaKahlerNullCone.lean` already builds the identical
instance stack for the sibling carrier `ParaKahlerVec R`:

```
instAddParaKahlerVec        :1144    instZeroParaKahlerVec   :1147
instNegParaKahlerVec        :1150    instSubParaKahlerVec    :1153
instSMulParaKahlerVec       :1156    instAddCommGroupParaKahlerVec :1203
instModuleParaKahlerVec     :1222
```

This provides precedent for the module-structure layer used by the bridge.

**Not proved:** compatibility of the transported product with raw matrix multiplication, or a native `CliffordAlgebra` representation and minimality theorem.

## 5. Joint 17-coordinate product action: proved with separate carriers

`socleDerivation X x = (0, X.mulVec x.2)` (`SplitSedenionDerivationAnomaly.lean:520`).

On the doubling unit $\ell=(0,[0,1,1])$ one learns only $X\cdot(0,1,1)^\top = 0$.
The kernel of $X\mapsto X(0,1,1)^\top$ on $\mathrm{Mat}_3$ is **3-dimensional**
(verified numerically: every matrix with row $i$ equal to $(0,t,-t)$ annihilates the
probe). Hence

$$\texttt{socleDerivation}\ X\ \ell = 0 \quad\centernot\Longrightarrow\quad X = 0,$$

so a single probe cannot separate the socle coordinates. The current bridge instead uses
coordinate readouts for both action components and proves injectivity of
`jointG2So21Action` via `readJoint17Params_jointG2So21Action`. The codomain is a product of
operator families on two different carriers: `SplitSedenion ℝ` and the 4D socle coordinate
algebra. Therefore this is a 17-coordinate injective product action, not a direct sum of
derivation spaces or a 17-parameter derivation on one common algebra. A shared-carrier
identification and compatible derivation proof remain open.

## 6. Twistor and Zorn coordinate bridge: proved at carrier level

`Cl55TwistorSplitSedenionColorBridge.lean` proves a carrier equivalence between
`Twistor55 ℝ` and `SplitSedenion ℝ`, and a coordinate-carrier equivalence between
`ZornSplitOctonion ℝ` and `GunaydinGurseyMultiplet ℝ`. Its norm identity is a coordinate
decomposition. These results do not prove an SU(3)/gauge representation or transport a
Cl(5,5) action/product through the equivalence. The sheet-swap theorem proves fourth iterate
identity and square-equals-negation; exact order four requires a nonzero witness.

---

## 7. VERIFIED-FALSE TARGETS — do not attempt these

These were numerically refuted over 4,000 random `R`-algebraic inputs using a
transcription of the repo's own definitions, cross-validated against two
kernel-proved theorems (§7.1). Errors of order 10² are not rounding artifacts.

### 7.1 `sedenionNorm` is **not** multiplicative — `sedenionNorm_mul` is FALSE

```
sedenionNorm (sedenionMul X Y) =? sedenionNorm X * sedenionNorm Y
   with sedenionNorm = N₁ − N₂ :  max err 9.0e+01   *** FALSE ***
   with sedenionNorm = N₁ + N₂ :  max err 1.5e+02   *** FALSE ***
```

**No `sedenionNorm_mul` exists in the repo, and none should be created.**

The reason is structural: `sedenionMul`
(`Cl44LeftIdealSplitSedenionSynthesis.lean:573`) is not the standard Cayley–Dickson
product arrangement, so the usual composition identity does not apply. The owner's
own docstring is already honest about this — `sedenionNorm` is described as a
**"split quadratic expression"** $N(a,b)=N_{\mathbb O_s}(a)-N_{\mathbb O_s}(b)$,
not as a multiplicative norm. Any downstream claim of "the split sedenions form a
composition algebra" is **unsupported by this carrier**.

Contrast: `zornNorm_mul`, $N(xy)=N(x)N(y)$ on the 8D factor, **is** proved
(`ZornSplitOctonionFin8Bridge.lean:337`). Multiplicativity is a property of the
Zorn split-octonion factor only, and does **not** lift to the pair carrier.

### 7.2 The exact form of the adjoint identity (already proved — reuse, do not re-derive)

`sedenionMul X (sedenionConj X) = (zornSmul (sedenionNorm X) zornOne, zornZero)`,
i.e. the first component is $(N, 0, 0, N)$ — **not** $(N,0,0,0)$.
`Cl44MinimalIdealInducedSedenionProductBridge.lean:468`.
Note the RHS carries `sedenionNorm`, not `zornNorm X.1`, so it is not the classical
orthogonal-involution identity either.

### 7.3 The generic Cayley–Dickson γ-parameter framework is ALREADY OWNED

`SplitSedenionDerivationAnomaly.lean:81` defines the λ/γ-parameterized
`cdMul γ (a,b) (c,d) = (a*c + γ • (d⋆*b), d*a + b*c⋆)` with `cdLift`. A further
34 files reference "CayleyDickson". **Building a new CD λ-framework would be a
duplicate-carrier violation.** Extend the existing owner instead.

## 8. Twistor and Günaydin–Gürsey coordinates: owner convention

The twistor/split-sedenion map is a carrier equivalence using the repository-owned
`fin8ToZorn` chart. The Günaydin–Gürsey map must likewise be the composition of
`zornToFin8` with `gunaydinGurseySplit` from
`Cl55SuperGrassmannianKKTSynthesis.lean:255`; direct grouping of Zorn fields does not
preserve the owner's Fock index order or its Jordan–Wigner sign. The bridge uses that owner
composition and proves its inverse and additive law. Its exact norm-coordinate formula is
`zornNorm_eq_gunaydin_gursey_coordinates`; it does not identify the quadratic expression
with a singlet determinant minus an unsigned triplet dot product.

```
twistor55ToSplitSedenion                          splitSedenionToTwistor55
twistor55SplitSedenionEquiv                       twistor55ToSplitSedenion_add
twistor55ToSplitSedenion_splitSedenionToTwistor55
splitSedenionToTwistor55_twistor55ToSplitSedenion
```

The bridge's equivalences are carrier-coordinate results. They do not establish an SU(3)
action or a gauge representation. The Andreev sheet map's fourth iterate is identity and
its square is componentwise negation; exact order four additionally needs a nonzero witness.

## 9. FORMALIZED REFUTATIONS — corrections to §5, including two of mine

A sandbox lane formalized two negatives. **Both correct claims made earlier in this
document, including by the orchestrator.** They supersede the prose in §5.

### 9.1 TWO probes are also insufficient — three are required (corrects §5 and me)

§5 established that ONE probe leaves a 3-dimensional kernel. I then instructed a worker
to use **two** probes. That instruction was **wrong**:

```
two_probes_do_not_separate :
  mulVec nonSeparatingMatrix (0,1,1) = 0  ∧  mulVec nonSeparatingMatrix (1,1,0) = 0
  ∧ nonSeparatingMatrix ≠ 0
```
with `nonSeparatingMatrix = !![-1,1,-1; -1,1,-1; -1,1;-1]`.

So $\ker[X\mapsto(Xv^{(1)},Xv^{(2)})]$ is also 3-dimensional. The map is injective only
on **three** probes — the three $\Lambda^2$ basis vectors — via `mulVec_three_basis_eq_zero`.

The landed owner `G2Sl2SeventeenParameterProductActionBridge.lean:197` obtains
two-probe injectivity **only after restricting to the 3-dimensional `so21LinearComb`
subspace**. That restriction is real; the unrestricted two-probe claim is false.

### 9.2 The joint family is NOT a derivation, and cannot be — Rank #1 is closed negatively

The premise of the whole Rank #1 plan was that a 17-parameter
$\mathfrak g_{2(2)}\oplus\mathfrak{sl}(2)$ acts on `SplitSedenion ℝ` by derivations.
**This is impossible in this carrier**, with an explicit counterexample
(`socleDerivationLift_not_leibniz`): for `X = sl2GenK13`,
`A = (lambda1Probe 0, zornZero)`, `B = (zornZero, lambda1Probe 1)` the left-hand side of the
Leibniz rule carries `-e₀` while the right-hand side is `sedenionZero`.

Two supporting facts that *are* proved, so the failure is precisely located:
- the $\mathfrak g_{2(2)}$ family **is** additive in its parameters
  (`sedenionG2Derivation_add_left`);
- the sum-of-two-derivations law **is** valid because the Leibniz defect **is** additive
  (`sedenion_derivations_add`);
- the soclé Leibniz law holds for **exactly the 3-dimensional span of the generators**,
  packaged as `IsSo21Adjoint` — not for a generic `X`.

**Consequence:** the image of `sedenionSocleDirectSum` cannot be identified with the genuine
$\mathfrak g_{2(2)}\oplus\mathfrak{sl}(2,\mathbb R)$ acting on `Der(S⁻)`, because the soclé
summand is not a derivation at all. Closing that would require embedding the 4-dimensional
$(2,1)$-signature algebra ($\cong \mathrm{Cl}(1,2)$) into `ZornSplitOctonion` as a
**derivation-preserving subalgebra** — a separate, larger construction.

The 17-coordinate *injectivity* survives as a coordinate statement (§5), but the
"derivations acting on the algebra" reading is **refuted**.

## 10. Not established anywhere in Lean (asserted in prose only)

Unchanged from earlier audits, restated for scope honesty: hyperfinite Type II₁
faithful state, Sato weights, Chern–Simons, Pinsker/Araki, Ryu–Takayanagi, Andreev
bound-state spectrum, Josephson current, "in-context memory does not dissipate".
These have **zero** Lean content.
