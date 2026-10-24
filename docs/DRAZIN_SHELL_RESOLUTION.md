# Action-sensitive extinction and oblique shell resolution

## Source and theorem contract

This is an additive extension of PR #192 at commit
`261ca866ac6c8f90bdb64fbbb3908e49ba81029f`.
Inputs are `Pasted text(20261023-005108).txt` and
`Pasted text (2)(20261023-005718).txt`. The uploaded
`Pasted text (3)(2).txt` is byte-for-byte identical to the second input.
Claims in the inputs that their code compiles are not verification evidence.

Carrier: a general ring with a star-ring structure, and native finite real
matrices for row/column actions and a concrete nontrivial example.
Reuse `Canonical.Drazin.IsDrazinInverse` and its existing `projection`,
`complementaryProjection`, `nilpotent`, power/complement annihilation;
reuse `Singular.MoorePenrose.IsMoorePenroseInverse` and
`Singular.MoorePenrosePowerShells.rangeShell` / `.deathShell`.
No inverse predicate, shell carrier, or Fitting decomposition is duplicated.

For a powerwise MP family g_m, put P_m=N^m*g_m and Q_m=P_m-P_(m+1).
The new targets are reverse/max absorption, right-action range-shell
extinction and recovery, and the corresponding left-action co-range laws.
For Drazin data put E=a*d, F=1-E, N=a*F. Define
H_m=F*P_m*F and S_m=F*Q_m*F. Prove H_i*H_j=H_max(i,j),
S_m=Q_m*F, idempotence and all distinct-shell zero products,
E*S_m=S_m*E=0, sum_(m<k) S_m=F, and E+sum_(m<k) S_m=1.
The power identity F*N^m=a^m*F handles k=0 without claiming N^0=0.
Prove S_m*a^(m+1)=0 and (S_m*a^m)*(g_m*F)=S_m.
For a nonzero x*S_m, prove x*S_m*a^r=0 iff m<r.

Causal proof order: Penrose equations -> nested supports -> action-sensitive
recovery/extinction; Drazin equations -> complementary power identities ->
compressed nested supports -> shell products -> telescoping -> full-operator
extinction. Self-adjointness is checked separately with native
`IsStarProjection`.

## Correction to the earlier action-independent wording

The earlier discussion and `DRAZIN_MP_PARTITION_AUDIT.md` distinguish range
shells from column death layers, but the phrase 'not exact time to absorption'
needs an action convention. Range shells DO encode exact extinction for
right-acting row/covector states. Co-range shells encode it for left-acting
column states. The new matrix theorems use `Matrix.vecMul` and `Matrix.mulVec`
explicitly. Zero shells have no nonzero state whose extinction time can be
assigned; no theorem assumes all shells are inhabited.

Two-sided compression F*Q_m*F supplies an ambient oblique refinement whose
sum is F; this is a new construction, not substitution of F for the ambient
identity in the previous raw-shell telescope. Zero products of distinct
idempotents are algebraic orthogonality. They do not make each ambient
idempotent self-adjoint. A self-adjoint F suffices for star projections.
No assertion says these shells commute with a, diagonalize a, or constitute
an eigenspace spectral resolution. Pure nilpotent components die to zero;
'entering the core' concerns disappearance of a general state's nilpotent
component, not transfer of that component into a nonzero regular state.

## Concrete example

A=[[1,1,0],[0,0,1],[0,0,0]], D=[[1,1,1],[0,0,0],[0,0,0]].
N=[[0,0,-1],[0,0,1],[0,0,0]] is nonzero with N^2=0.
The example supplies an actual MP family for all powers.
S_0=[[0,0,-1/2],[0,0,-1/2],[0,0,1]],
S_1=[[0,-1,-1/2],[0,1,1/2],[0,0,0]].
The checks include S_0 not self-adjoint and S_0*A=0 but A*S_0 != 0.

## Verification boundary

Sources remain candidates until the dedicated pinned workflow passes.
The workflow compiles full unchanged dependency sources plus all four new
modules and audits every new named declaration with `#print axioms`.
Only propext, Classical.choice and Quot.sound are allowed. No dependency
pins or existing Lean files are changed. No full-repository build, all-green
CI, stochastic convergence theorem, attention training change, or claim of
minimal Drazin index follows from this scoped check.
