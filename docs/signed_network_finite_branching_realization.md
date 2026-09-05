# Finite signed branching realization of a Hamiltonian generator

## Status and scope

This is a mathematical construction and proof for the explicitly specified
finite-cell process on a countable configuration space. It is not a report that
the complete stochastic theorem
has been elaborated in Lean. The companion Lean extension formalizes the
ensemble jump generator, native next-event and exponential holding-time laws,
unbiased initialization, local Hamiltonian intertwining, population generator
bounds, and cancellation identities. The infinite path-space construction,
almost-sure nonexplosion, stopped Dynkin formula and its limiting argument,
and the final matrix-exponential identity are not yet Lean declarations in
this extension. No stochastic moment or nonexplosion property is installed as
an axiom or a field of an assumed process.

## 1. Exact theorem

Let C be a finite set, and let L be a finite real matrix with columns indexed
by parent cells and rows indexed by child cells. Assume the algebraic condition

    sum_a L[a,b] = 0  for every b.

For the installed qubit realization, C = Fin 4 and this condition is proved
from the actual Hamiltonian commutator, not assumed separately.

Define w_b[a] = L[a,b], w_b^+[a] = max(L[a,b],0),
w_b^-[a] = max(-L[a,b],0), and

    gamma_b = sum_a w_b^+[a] = sum_a w_b^-[a]
            = (1/2) sum_a |L[a,b]|.

When gamma_b > 0 set

    Q_b(a,d) = w_b^+[a] w_b^-[d] / gamma_b.

When gamma_b = 0 set Q_b = 0. The whole column is then zero. Thus

    Q_b(a,d) >= 0,
    sum_(a,d) Q_b(a,d) = gamma_b,
    sum_d Q_b(a,d) - sum_d Q_b(d,a) = L[a,b].

These identities are the already specified pair coupling. They are not a
new stochastic hypothesis.

A configuration n consists of nonnegative integer counts n_b^+, n_b^-.
Write S_a(n)=n_a^+-n_a^- and N(n)=sum_a(n_a^++n_a^-).
Fix a common, constant sample weight eta >= 0.

There are two marked births for each (b,a,d):

* At rate n_b^+ Q_b(a,d), retain the parent and add a positive child at a
  and a negative child at d.
* At rate n_b^- Q_b(a,d), retain the parent and add a negative child at a
  and a positive child at d.

All children carry the same weight eta. The optional cancellation rule
replaces each cell's counts by

    kappa(n)_a^+ = max(n_a^+ - n_a^-, 0),
    kappa(n)_a^- = max(n_a^- - n_a^+, 0).

Cancellation is applied after a birth, with the next birth rate evaluated
on the remaining configuration. The pruned construction may also cancel the
initial configuration before starting its clock; this leaves the signed
initial expectation unchanged and only reduces its population bound. It does
not identify particle sign with routing direction or a different algebraic sheet.

For either process, if N(n(0)) <= n0 almost surely and
E[eta S(n(0))] = w0, then the process exists for all t >= 0 almost surely and

    E[eta S(n(t))] = exp(t L) w0.

Suppose in addition that a real-linear synthesis F(w)=sum_a w_a A_a obeys

    F(L w) = -(i/hbar) [H,F(w)]

for a fixed Hermitian H and hbar > 0. Then, with rho0=F(w0),

    E[sum_a eta S_a(n(t)) A_a]
      = exp(-i t H/hbar) rho0 exp(i t H/hbar),  t >= 0.

The hypothesis on F is instantiated by the installed explicit qubit frame
and generator below. It is not a requested conclusion repackaged as data.

## 2. Explicit construction of the jump process

The count state space is N^(2|C|), with its discrete sigma-algebra. Its marked
event set is finite. At state n, the total birth intensity is

    q(n) = sum_b (n_b^+ + n_b^-) gamma_b.

Choose a finite Gamma such that gamma_b <= Gamma for every b. A maximum is
available when C is nonempty; the source uses the universally defined finite
bound Gamma = sum_b gamma_b. Then q(n) <= Gamma N(n).

If q(n)=0, the process remains at n forever. This is absorption, not an
infinite sequence of zero-duration dummy events.

If q(n)>0, draw a waiting time with exponential distribution of rate q(n)
and independently draw a mark (sign,b,a,d) with probability

    n_b^sign Q_b(a,d) / q(n).

Apply the marked birth, followed by kappa when cancellation is enabled.
Repeat using the new state. Every transition law is a concrete probability
kernel. Countability of the configuration space gives its measurability.
Iterating these kernels constructs the marked sequence and its holding times;
the Ionescu-Tulcea extension theorem supplies a probability measure on the
infinite sequence space. Define tau_m to be the time of the m-th actual
marked birth. If the process absorbs, all subsequent tau_m are infinity.
The continuous-time count process is constant between successive tau_m.
Initially it is defined up to zeta = lim_m tau_m. The next argument proves
zeta=infinity almost surely; this is not built into the definition.

### Derivation of the stopped expectation identity from the clocks

For completeness, no global Dynkin theorem is needed at this stage. Stop
at the m-th birth and fix k<m. Conditional on the history through tau_k,
let n_k be the current state, q_k=q(n_k), and a_k=(A f)(n_k). On the event
tau_k<=t with q_k>0, independence of the mark and exponential holding time gives

    E[(f(n_(k+1))-f(n_k)) 1_(tau_(k+1)<=t) | history at tau_k]
      = a_k integral_0^(t-tau_k) exp(-q_k u) du.

The conditional expectation of the contribution accumulated during the
same holding interval is

    E[integral_(tau_k)^(min(t,tau_(k+1))) a_k ds | history at tau_k]
      = a_k integral_0^(t-tau_k) P(holding time > u | history) du
      = a_k integral_0^(t-tau_k) exp(-q_k u) du.

Both expressions are zero when tau_k>t; absorption has q_k=a_k=0 and
contributes zero as well. Summing these equalities over k=0,...,m-1
and telescoping proves

    E[f(n(t wedge tau_m))] - E[f(n(0))]
      = integral_0^t E[1_(s<tau_m) (A f)(n(s))] ds.

For a fixed m the accessible count states satisfy N<=n0+2m and form a finite
set. Thus the observables used below and their rates are bounded on the
stopped process, justifying the finite sums and integrals. For the artificial
birth envelope include the birth counter k in the stopped state; its increment
is exactly two. The same calculation applies with pruning by replacing the
jump map with its composition with kappa.

## 3. Nonexplosion without circular use of a global process

Let B(t) count marked births. Even when cancellation occurs, the active
population satisfies

    N(n(t)) <= Y(t),  Y(t) := n0 + 2 B(t).

Use the stopped process at tau_m. It has at most m births and bounded rates,
so all finite-horizon expectation calculations are legitimate before proving
nonexplosion. The marked waiting-time construction, or its elementary stopped
compensator identity, gives

    E[Y(t wedge tau_m)]
      = n0 + 2 integral_0^t E[1_(s<tau_m) q(n(s))] ds
      <= n0 + 2 Gamma integral_0^t E[Y(s wedge tau_m)] ds.

Gronwall's inequality yields the uniform bound

    E[Y(t wedge tau_m)] <= n0 exp(2 Gamma t).

On {tau_m <= T}, the stopped envelope is n0+2m. Therefore

    P(tau_m <= T) <= n0 exp(2 Gamma T) / (n0+2m).

For m >= 1 the denominator is positive. If n0=0 the process is absorbed at
zero and the assertion is immediate. Taking m to infinity proves
P(zeta<=T)=0. Applying this to integer T proves zeta=infinity almost surely.
This covers both the unpruned and immediately pruned constructions, including
marked events whose net state update disappears after cancellation.

Fatou's lemma also gives

    E[Y(t)] <= n0 exp(2 Gamma t),
    E[N(n(t))] <= n0 exp(2 Gamma t).

Because Y is nondecreasing, for every finite T,

    sup_(0<=s<=T) |S_a(n(s))| <= Y(T),

an integrable pathwise dominating variable. This supplies the uniform
integrability needed below. Merely knowing that paths are finite would not
have been enough to exchange expectation and the stopped limit.

## 4. First moments, derived from actual jumps

For a scalar observable f on configurations, the unpruned generator is

    (A f)(n) = sum_(sign,b,a,d) n_b^sign Q_b(a,d)
                    [f(J_sign,a,d(n)) - f(n)].

At coordinate x the increment is sign*(1_(a=x)-1_(d=x)). Hence

    (A S_x)(n)
      = sum_b (n_b^+ - n_b^-)
          [sum_d Q_b(x,d) - sum_a Q_b(a,x)]
      = sum_b L[x,b] S_b(n).

Thus A S = L S. This is an explicit finite sum computation, not a
first-moment assumption. Likewise A N=2q and A(N^2)=(4N+4)q.

For the pruned update, S(kappa(J(n)))=S(J(n)), so A_pruned S=L S as well.
Also S(kappa(n))=S(n), so removing null pairs before the next event leaves
the physical-time linear drift unchanged even though q(n) changes.

The stopped first-moment formula is

    E[eta S(n(t wedge tau_m))]
      = E[eta S(n(0))]
          + integral_0^t E[1_(s<tau_m) L eta S(n(s))] ds.

The terminal random vectors are dominated by eta Y(t). The integrands are
dominated by a fixed finite matrix norm times eta Y(s), whose expectation
is integrable on every compact time interval by the preceding bound.
Dominated convergence and Fubini therefore yield, for m(t)=E[eta S(n(t))],

    m(t) = w0 + integral_0^t L m(s) ds.

This implies continuity of m and then differentiability with m'=L m.
Uniqueness of a finite-dimensional linear ODE gives

    m(t)=exp(t L)w0.

The argument does not identify the laws of the pruned and unpruned processes.
They can have different event rates, event-indexed expectations, genealogies,
and higher moments. The closed physical-time first moment is what agrees.

## 5. Unbiased initialization is constructed

Let w0 be any real finite vector. Set R=sum_a |w0_a|.
For R=0 use the empty ensemble; the represented operator is zero.
For R>0 choose M>=1 independent initial cells B_k with

    P(B_k=a)=|w0_a|/R,

assign sign sign(w0_(B_k)), and give every initial particle and descendant
common weight eta=R/M. Zero entries are sampled with probability zero, so
the choice of sign at zero is immaterial. Then N(n(0))=M and

    E[eta S_a(n(0))]
      = (R/M) M (|w0_a|/R) sign(w0_a)
      = w0_a.

Thus arbitrary real quasiprobabilities are initialized without requiring them
to be integer counts or normalizing signed counts into probabilities. The
companion Lean source constructs the one-seed PMF and proves this expectation
as a Bochner integral. Multiple-seed independence is not yet a separate Lean
declaration in the extension.

## 6. Installed qubit specialization

Take v0=(1,1,1), v1=(1,-1,-1), v2=(-1,1,-1), v3=(-1,-1,1), and

    A_a=(I+v_a dot sigma)/2.

The A_a are Hermitian trace-one phase-point operators, not positive effects.
They satisfy Tr(A_a A_b)=2 delta_ab. For Hermitian rho0, set

    w0_a=Tr(A_a rho0)/2.

These real coefficients synthesize rho0. The new Lean bridge proves
synthesis(analysis(P.pauliMatrix))=P.pauliMatrix for the repository's existing
real Pauli carrier, supplementing the previously present analysis/synthesis
identity in the other direction.

For H=h dot sigma, with h real, the installed generator is

    L[a,b] = v_a dot (h cross v_b) / (2 hbar).

Direct Pauli multiplication gives

    synthesis(L w)=-(i/hbar)[H,synthesis(w)].

The scalar part of a general Hermitian H commutes with rho and cancels from
unitary conjugation, so it does not change this generator. Applying synthesis
to the first-moment ODE yields the Liouville-von Neumann equation with initial
condition rho0. The matrix exp(-i t H/hbar) rho0 exp(i t H/hbar) solves the
same finite-dimensional ODE. Uniqueness proves the target identity.

Every matrix-valued expectation exists: in any fixed finite-dimensional norm,

    ||eta sum_a S_a(n(t)) A_a|| <= eta max_a ||A_a|| Y(t),

and the right side has finite expectation. Individual reconstructed samples
need not be positive density matrices; their expectation equals the unitary
evolution of rho0.

## 7. Exact boundary of the Lean extension

Implemented as explicit source proofs:

* count-valued births with parent-sign inheritance;
* actual nonnegative marked intensities and a zero-rate absorption theorem;
* the total-rate formula and a derived finite linear rate bound;
* the ensemble identity A S=L S and its cancellation versions;
* first and second population-generator identities;
* a normalized native marked-event PMF and finite event iterates;
* an actual next-event expectation integral;
* the native exponential holding-time measure and active product law;
* unbiased one-seed initialization as a probability measure and integral;
* the installed qubit local generator intertwining and random-readout
  cancellation/integrability identities.

Not claimed as Lean-certified here:

* an infinite clocked path measure specialized to these kernels;
* almost-sure nonexplosion of that process;
* its stopped martingale/compensator theorem and limit passage;
* the continuous-time expectation/matrix-exponential conclusion.

The last four are proved mathematically above. Their Lean development must
use the actual constructed kernels rather than introduce a structure field
asserting the desired first moment or a custom nonexplosion axiom.

## Primary references

The finite proof above is given explicitly; the following are related primary
sources and the native probability interfaces used by the code:

* S. Shao and Y. Xiong, A computable branching random walk for the many-body
  Wigner quantum dynamics (2016), https://arxiv.org/abs/1603.00159.
* S. Shao and Y. Xiong, Branching random walk solutions to the Wigner equation
  (2019), https://arxiv.org/abs/1907.01897. First-moment correctness does not
  eliminate the numerical sign problem or exponential variance growth.
* Mathlib v4.28.1, Probability/ProbabilityMassFunction/Constructions.lean,
  Probability/ProbabilityMassFunction/Integrals.lean, and
  Probability/Distributions/Exponential.lean.
* Mathlib, Probability/Kernel/IonescuTulcea/Traj.lean, for the native infinite
  kernel-extension infrastructure (not instantiated by this extension).
