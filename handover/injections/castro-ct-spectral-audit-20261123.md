# Castro CT audit: theorem contract and review boundary

## Status and provenance

This is a **source-reviewed draft; kernel verification remains pending**.
It is a separate change from the Dzhunushaliev/Myung/Zorn audit in
[PR #430](https://github.com/nickgou-nuke/info-geometry-lean/pull/430).
The baseline is `fe24e350b08fdea04f74c0748ef9fd9417c47529`.

The supplied proposal concerns Carlos Castro Perelman's
[2007 paper](https://empslocal.ex.ac.uk/people/staff/mrwatkin/zeta/castro2007RH.pdf),
whose header records a March revision. The relevant source locations are
equations (2.1)–(2.8), (2.21), (2.25)–(2.26), and (2.29)–(2.36).
The earlier [Elizalde–Moretti–Zerbini paper](https://arxiv.org/abs/math-ph/0109006)
is historical context, not a response to the later 2007 paper.

The proposal was split into reusable native declarations. Its obsolete draft
with a false antilinear implication was not imported. Results below describe
the statements and their mathematical source review, not completed Lean checks.

## Owner alignment

| Owner | Actual content | Explicit hypotheses and limits |
| --- | --- | --- |
| `Physics.CastroFirstOrderFactorization` | Differentiation of the exponential ansatz, printed first-order expressions, exact composite defect, and algebraic partner `1 - D1` | Native functions `ℝ → ℂ`; local or global differentiability as stated; no operator domain or adjointness construction |
| `OperatorAlgebra.AntilinearPairingAudit` | Native semilinear pairing identities, linear-twist reality criterion, global symmetry equivalence, and explicit indefinite countermodel | Generic commutative star ring; `NoZeroDivisors` for cancellation; native `Fin 2 → ℂ` only for the finite countermodel |
| `Spectral.QuadraticParameterReality` | Five new factorization/conjugation/fiber lemmas on the existing quadratic parameter | Both quadratic roots retained; existing real-axis/critical-line criterion reused |
| `Arithmetic.CastroPerelmanCTAudit` | Actual Gaussian theta positivity and modular potential, ansatz reflection, affine scaling, and scalar argument collapse | Native Mathlib theta kernel; real scaling parameters; nonzero denominator where required; no Mellin or inner-product identification |

The polynomial remains `Physics.HarishChandraCasimir.casimirEigenvalue`.
No second definition of `s * (1 - s)` is introduced. Existing
`Spectral.QuadraticParameterReality.real_iff_critical_of_im_ne_zero` retains
the nonreal-parameter premise. Existing `Arithmetic.ZetaDihedral` owns the
commuting reflections and their critical-line fixed locus; this patch does not
duplicate that action or identify a generic four-point orbit with a fixed point.

The positive spectral results already have owners:
`Krein.BenderMannheimPTPaisUhlenbeckResonance.wigner_antilinear_time_reversal`
handles a nonzero unbroken symmetry eigenline, and
`Krein.eta_biorthogonal_pairing` / `Krein.eta_nonreal_eigenvector_null` handle
the Hilbert-space linear-metric setting. The new arbitrary sesquilinear-form
lemma does not assume the Hilbert structure of those results.

## Exact mathematical content

### 1. Differentiate before making a spectral claim

For `W : ℝ → ℂ`, define

\[
\psi_{s,k,W}(u)=\exp((-s+k)u+W(u)),\qquad
D_1f=-f'+(W'+k)f,\qquad D_2f=f'+(W'+k)f.
\]

Native `HasDerivAt` calculus gives `D1 psi = s psi`. Under global
differentiability, this is an equality of functions before the next derivative
is taken. Consequently,

\[
D_2D_1\psi_s=s(-s+2k+2W')\psi_s,
\]
\[
D_2D_1\psi_s-s(1-s)\psi_s
=2s\bigl(W'-(1/2-k)\bigr)\psi_s.
\]

The exponential is nonzero. At each point the quadratic equation is therefore
equivalent to `s = 0 ∨ deriv W u = 1 / 2 - k`. The global theorem keeps the
same zero-mode exception. No second derivative of `W` is assumed.

The separate expression `inversionDual` is defined algebraically as
`1 - D1`; its composite with `D1` has value `s(1-s)` on the ansatz. This is
not yet a theorem that coordinate inversion conjugates `D1` to this expression.
That additional operator identity needs the modular derivative relation.
It also supplies no selfadjointness or spectral-reality theorem.

The paper changes from lowercase to uppercase notation around (2.8), then
refers the conjugation law back to (2.2). The obstruction here is precisely
for the explicit (2.2) ansatz under the printed operators; a different uppercase
family would require a separate definition and proof.

### 2. Keep conjugate-linear and linear twists distinct

For a native sesquilinear form `B`, an antilinear map `K`, and `Hv = E v`,

\[
B(Hv,Kv)=\bar E B(v,Kv)=B(v,KHv).
\]

With `HK = KH`, the same conjugated coefficient appears in `B(v,HKv)`.
Thus the diagonal twisted equation is automatic on an eigenvector, including
one with a nonreal eigenvalue. It cannot produce `(conj E - E) B(v,Kv) = 0`.
For a **linear** twist `η`, the corresponding adjointness equation and nonzero
`B(v,ηv)` do imply `star E = E` over a ring without zero divisors.

The global qualification matters: when `K` is surjective and commutes with `H`,
global twisted symmetry is equivalent to ordinary symmetry for `B`. A positive
definite original form would therefore retain its spectral consequences.

The finite countermodel uses

\[
H=\operatorname{diag}(i,-i),\quad
K(z_0,z_1)=(\bar z_1,\bar z_0),\quad
B(u,v)=\bar u_0v_1+\bar u_1v_0.
\]

Its form is Hermitian, nondegenerate, and indefinite. The maps commute, `K²=1`,
and global twisted symmetry holds. For `v=(1,0)`, the source proves `Hv=i v`,
`B(v,v)=0`, and `B(v,Kv)=1`. The symmetry does not preserve this eigenline.
This does not contradict the existing unbroken-symmetry reality theorem.

### 3. Use the genuine theta kernel and retain both spectral branches

The theta owner uses `HurwitzZeta.evenKernel 0`, its convergent Gaussian sum,
and its native modular equation. With

\[
W_\ell(u)=\tfrac12\log G(e^{\ell u}),
\]

it proves `W_ell(-u) = W_ell(u) + ell*u/4`. The constraint
`ell = 4*(2*k-1)` then implies reflection of the actual exponential ansatz.
The theorem is a global sufficient law; equality at `u=0` cannot determine
the scaling constraint. Differentiability and nonconstancy of this concrete
theta potential are not asserted by this patch.

For the existing quadratic parameter `E`, the new fiber theorem is

\[
E(t)=\overline{E(s)}\iff t=\bar s\ \lor\ t=1-\bar s.
\]

Both branches are necessary. In particular `E(1-conj s)=conj(E(s))` is
unconditional and imposes no critical-line restriction.

For nonzero real `ell`, the label argument

\[
p(s_1,s_2)=\frac2\ell(2k-(\bar s_1+s_2))
\]

equals `1/2` at `(s,1-conj s)` under the scaling constraint. The final theorem
substitutes this into an **arbitrary scalar function** `Z`. It proves no
completed-zeta evaluation or nonzero value at `1/2`.

## Analytic obligations kept separate

The signed factor `2/ell` is retained only as the paper's label-kernel
convention. A change of variables in an ordinary integral, with transformed
bounds ordered from zero to infinity, supplies an absolute Jacobian for real
nonzero `ell`. Removing the theta zero
mode is also a distinct operation. No convergent Mellin equality is claimed
in this patch.

Analytic continuation alone neither constructs nor rules out every possible
sesquilinear pairing. A pairing on the intended function space still needs
well-definedness, suitable domains, and the asserted operator symmetry; positivity
is another obligation. No claim about these properties, spectral completeness,
zeta-zero correspondence, or RH is promoted here.

## Validation and independent roles

The focused command is:

```bash
python3 verification/castro-ct/check.py
```

It reuses the existing `verification/real-matrix-split` package and verifies
its pins against the root: Lean `v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. No dependency update or cache
replacement is part of this change.

Source screening, strict refutation screening, static GATE_4, and the semantic
gate ran successfully. The bounded inventory found **67 explicitly named public
declarations across the four selected owners**, including unchanged declarations
in the existing spectral owner. The semantic gate reported zero errors and six
heuristic `trivial_surface` warnings on small explicit equalities; these do not
constitute a kernel or axiom check.

The author command reached the maintained wrapper and waited for the shared
build lock; its queued invocation was stopped without a compiler-worker receipt.
A successful focused build, fresh warning-as-error elaborations,
and the generated `#print axioms` audit are still outstanding. The verifier
records a pending status until the exact serial command receipt, allowed axiom
set, and source hashes all pass. No root-package build or local pre-push build
gate is claimed.

The independent source reviewer requested two wording corrections: distinguish
theta-kernel positivity from positivity of a pairing, and distinguish the
algebraic partner from a constructed inversion-conjugation theorem. Both were
applied. A-A gave a mathematical/source-scope PASS on all four integrated
owners and reviewed the handover. A distinct QA-A independently reran
`check.py --source-only` in a separate output directory (exit 0), confirmed
the same 67 declarations and six warning sites, verified matching source
hashes, and ran `git diff --check` (exit 0). QA classified the result as
source-ready for a draft; it did not grant kernel acceptance. Until the
outstanding kernel checks run, this remains a draft.
