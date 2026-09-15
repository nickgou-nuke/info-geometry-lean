# Two-state and angular-correlation algebra

This development extracts explicit mathematical models from the proposed chiral
perturbation, magnetic modulation, particle–gamma correlation, and compound-spin
descriptions. It does not equate their definitions with validated nuclear physics.

## Resonance envelope versus time-dependent transition

`Physics/ChiralPerturbation.lean` defines

\[
E(\delta,g)=\frac{g^2}{\delta^2+g^2},\qquad
P(\delta,g,t)=E(\delta,g)
\sin^2\left(\frac{\sqrt{\delta^2+g^2}\,t}{2}\right).
\]

The oscillatory factor reuses `Thorium229.rabiTransitionProb` from the existing
owner, rather than recreating a second Rabi implementation.

The proof targets bound both functions between zero and one. For nonzero
coupling the envelope equals one exactly at zero detuning, but the transition
probability starts at zero, reaches one at the resonant pi pulse, and returns
to zero at the two-pi pulse. An envelope of one therefore does not establish
permanent locking or time-independent transfer.

The stronger bound `transitionProbability_le_envelope` retains the detuning
dependence. At every nonzero detuning, the envelope and hence the transition
probability are strictly less than one, for every coupling and every time.
At unit detuning and unit coupling, the uniform upper bound is one half.

This is a specified two-state formula, not a derivation from a particular
nuclear Hamiltonian, nor proof that nuclear chiral-doublet motion is Dirac
Zitterbewegung. It does not establish a vanishing Bohm potential, CPT invariance,
or the feasibility of a driving field.

## Signed readouts versus directions

`Physics/MagneticModulation.lean` defines the supplied scalar expression as
`signedReadout gap shift sign`. The shift is an energy-like model parameter,
not a magnetic-field value silently added to an energy.

The two signed readouts differ by `2 * gap`, independently of the shift.
Their inequality is therefore already present at zero shift. Opposite signs
require the stronger condition `|shift| < gap`; a concrete example at gap one
and shift two has distinct but strictly positive readouts. No spatial photon
direction follows from inequality of these scalar values.

The phase difference includes an explicit coupling. A regression example has
a nonzero phase difference of `2 * pi` while its sine and cosine coincide with
those of zero, so a nonzero real phase difference alone does not imply distinct
observable phase factors.

## Actual three-vector correlations

`Physics/ParticleGammaCorrelation.lean` uses the repository's canonical
`FiniteSpin.Vec3R` and Mathlib's `dotProduct`. The two signed correlation values
are different exactly when the dot product is nonzero. A pair of nonzero
orthogonal vectors is a counterexample to replacing nonorthogonality by the
separate nonzeroness of the vectors. Simultaneous reversal leaves their dot
product invariant. No measurement-induced chirality separation is inferred
without an explicit detector and interaction model.

## Rotation after reversal

`Physics/CompoundChirality.lean` constructs reversal followed by a half-turn
about the second coordinate axis. Their composition is

\[
(s_1,s_2,s_3)\longmapsto(s_1,-s_2,s_3).
\]

It is involutive but need not negate the entire spin vector. This is a coordinate
model of the combined transformation, not an identification with Tomita modular
conjugation or a complete antiunitary quantum time-reversal operator.

The residual-spin identity is additive conservation, `initial - emitted`.
It permits a zero residual and does not claim that evaporation universally
increases orientation, removes entropy, or creates coherence.

## Validation status

All Lean paths above are under `lean/InfoGeometry/`. The four new owners and
`Physics/ChiralModelTests.lean` are staged with fifteen regression examples and
fourteen axiom audits. They remain **pending Lean 4.28.1 verification** while the
earlier, sequential pinned-source rebuild runs. No whole-repository validation,
`InfoGeometry.All` integration, GitHub push, or presentation export is claimed.

After the existing live compiler session terminates, check sequentially:

```bash
python3 /tmp/isnp-rebuild-pinned.py InfoGeometry.Physics.ChiralModelTests
```
