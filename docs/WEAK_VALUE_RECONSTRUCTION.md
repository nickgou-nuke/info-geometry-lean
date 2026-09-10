# Weak-value reconstruction and the two-sheet null locus

This extension implements the mathematical content of the supplied
`Pasted markdown(20260910-130011).md` and the subsequent weak-value proposal.
The repository README names the doubled vacuum, TSVF, and phase-conjugate
geometry as its program. The implementation below uses actual owner
definitions to identify which parts of that program follow mathematically.

The new files retain the original dependency pins and build on the existing
`SarsModularWeakValue`, `Streaming.WeakValueBoundary`, `Krein.DoubledSpace`,
`Krein.KreinSpace`, and `Topology.DiracKahlerMultiplication` owners.

## The field readout

`SpinorHydrodynamicReadout` uses a native complex inner-product space. Its
four-component specialization is `EuclideanSpace ℂ (Fin 2 × Fin 2)`, retaining
separate parity and spin indices and the correct Euclidean norm. It defines

\[
\rho(z)=\|z\|^2,\qquad j_\kappa(z,v)=\kappa\operatorname{Im}\langle z,v\rangle,
\qquad u_\kappa(z,v)=j_\kappa(z,v)/\rho(z).
\]

The same-state momentum expression is proved exactly:

\[
u_\kappa(z,v)=\operatorname{Re}
\frac{\langle z,-i\kappa v\rangle}{\langle z,z\rangle}.
\]

This identifies the positive-density readout with a particular weak expression.
An independently chosen postselection vector changes the denominator and is
additional data. It does not automatically reconstruct the same velocity.

`SpinorReadoutRegularity` proves the actual scalar derivative estimate

\[
\left|\frac{d}{dt}u_\kappa(z(t),v(t))\right|
\leq \kappa\left(\frac{\|v'(t)\|}{\|z(t)\|}
+3\frac{\|z'(t)\|\|v(t)\|}{\|z(t)\|^2}\right)
\]

for differentiable curves, `κ ≥ 0`, and `z(t) ≠ 0`. The spatial covector
readout uses native `fderiv ℝ psi x direction`; its operator-norm estimate is
also proved. These are derivative statements, not stored regularity predicates.
The full spatial Frobenius estimate and a nonlinear PDE reconstruction are
not asserted by the component theorem.

`SpinorReadoutOscillation` constructs the explicit local field

\[
\zeta_N(x,y)=
(\cos(Nx+\pi/4),\ \sin(Nx+\pi/4)e^{iy}).
\]

For fixed `κ > 0`, its density is one; at `y=0`, its actual y-derivative
supplies the current, its reconstructed y-velocity is `κ sin²(Nx+π/4)`,
and the x-derivative of that velocity at zero is `κN`. Hence unit density and bounded velocity permit
arbitrarily large spatial derivatives. This is a family of configurations,
not a time-dependent Navier–Stokes blowup solution. The torus integral and
constant-spectrum matrix calculations in the attachment are not silently
substituted for these proved local statements.

## Exact two-sheet overlap geometry

For the owned doubled carrier `z=(post,pre)`, the three expressions are distinct:

\[
q_\varepsilon(z)=\|post\|^2-\|pre\|^2,
\quad q_J(z)=2\operatorname{Re}\langle post,pre\rangle,
\quad q_{J_i}(z)=2\operatorname{Im}\langle post,pre\rangle.
\]

Here the first two operators are the existing `spectral_epsilon` and
`modular_j`. The phase-swap `J_i(post,pre)=(-i\,pre,i\,post)` is proved to be
`i` times the existing real `complex_i` rotation. It is involutive and
anticommutes with `modular_j`. The exact null-locus theorem is

\[
\langle post,pre\rangle=0
\quad\Longleftrightarrow\quad q_J(z)=0\ \land\ q_{J_i}(z)=0.
\]

`WeakValueKreinBoundary` gives the explicit map from the existing finite state
functions into this doubled L² carrier. It proves that the original
`weakValue?` returns `none` exactly on this simultaneous zero locus.
It also proves a nonzero equal-component state is diagonal-null while its
identity weak value is defined and equal to one. Thus diagonal isotropy alone
is not the denominator-zero condition. A null vector is not a zero eigenvector
of the invertible signature operator.

## Actual pole conditions and barrier

The existing owner already has a Pauli probe with weak value `1/ε`, normalized
selection probability `ε²/(1+ε²)`, and an identity probe with value one.
`WeakValuePoleExamples` reuses those results and proves a real one-sided pole.
A second Hermitian Pauli probe has imaginary numerator `i` and zero real
readout for every nonzero real ε. These examples show why a small denominator
alone does not imply a real velocity pole.

For actual complex functions `n,d`, `WeakValuePoleCriterion` proves that
`d(t0)=0`, `d'(t0)=c≠0`, and continuity of `n` imply

\[
(t-t_0)\operatorname{Re}\frac{n(t)}{d(t)}
\longrightarrow \operatorname{Re}\frac{n(t_0)}c.
\]

If the limiting real residue is nonzero, the theorem supplies an eventual
lower bound `|Re(n/d)| ≥ |Re(n(t0)/c)|/(2|t-t0|)` on a punctured neighborhood
where the denominator is nonzero. The criterion is wired to the existing
Option-valued weak-value owner. The corresponding actual derivative upper
bound uses `‖d‖` and `‖d‖²`; a complex transition amplitude cannot replace the
positive density in the square-root density estimate.

The explicitly defined normalized postselection barrier
`-log(postSuccess ε)` is proved to diverge at the overlap node. It is not the
fiberwise matrix barrier `-log det R` or the fluid enstrophy. A further theorem
constructs a readout with a real pole and identically zero spatial derivative,
so the algebraic pole alone cannot justify the proposed gradient cascade.
Enstrophy divergence would require a proved lower bound on actual spatial
curl over an appropriate region and an integral argument. Divergence of an
upper bound provides no such lower bound.

## Evolution and differential-operator obligations

`KreinFlowConservation` differentiates the quadratic form along a supplied
trajectory of the existing Krein-skew-adjoint generator and derives its
conservation, allowing the generator to depend on time. With the fixed Krein
metric, a non-null state cannot enter that metric's null cone. This does not
forbid an independent transition overlap from vanishing; the exact overlap
geometry must be used. No global quantum trajectory is constructed here.

`DiracKahlerSplitCurvature` reuses the existing flat datum and derives the
negative-square partner and its oddness. Before flatness is imposed, the
generic associative-ring identities retain curvature:

\[
(d\pm\delta)^2=\pm(d\delta+\delta d)+(d^2+\delta^2),\qquad
\{d+\delta,d-\delta\}=2(d^2-\delta^2).
\]

The common invariant domain of unbounded operators remains separate from
these algebraic identities. Connection curvature is not identified with a
Zorn associator by these results.

The source-audited Andreev owners supply finite swap/fixed-subspace and BdG
energy-reversal identities. They do not prove that an overlap pole causes
unit-probability reflection, supplies a non-associative mass gap, controls
vortex stretching, or reconstructs a continuation of the same fluid PDE.
The OpenAI Navier–Stokes terminal theorem is not imported or used to infer
this proposed mechanism. The exact gauge–spinor evolution, forced PDE
reconstruction, and spatial continuation estimates remain to be constructed.

The accompanying draft PR records the native Lean version, the full new
theorem axiom audit, and the symbolic witness checks. All statements above
refer to declared theorem content rather than README narrative alone.
