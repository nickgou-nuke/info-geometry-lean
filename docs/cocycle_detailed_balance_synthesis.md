# Cocycles, Chain Rules, and Broken Detailed Balance

This note captures the modular-probabilistic chain:
Radon-Nikodym composition, logarithmic flattening, and irreversibility under
noncommutative update transport.

## 1. Radon-Nikodym Chain Rule and Modular Cocycles

In the canonical modular layer (notably `Canonical/GrandSynthesis.lean`),
relative density transport is represented through Tomita-Takesaki style
operators on doubled/Krein carriers.

- Classical chain rule (`dμ/dλ = (dμ/dν) (dν/dλ)`) is multiplicative.
- In modular/operator language, this is the cocycle composition law for
  relative state transport.
- Relative modular objects encode state-change flow as a Connes-style 1-cocycle
  pattern.

## 2. Log Deformation and Additive Thermodynamic Charges

Applying `-log` converts multiplicative density chains into additive quantities.

- Multiplicative ratio transport becomes additive potential transport.
- In the canonical `LogSumExp`/thermodynamic bridge, additive energies are
  normalized into partition-style aggregates.
- This realizes the geometric-to-thermodynamic deformation:
  ratio geometry -> additive free-energy-like functionals.

## 3. Cycles, Hysteresis, and Broken Detailed Balance

For looped update paths, commutativity determines reversibility.

- Flat/invariant regimes admit vanishing cycle defect and reversible closure
  (detailed balance).
- In noncommutative update order regimes (hysteresis), path composition differs
  by order and generates cycle defect.
- This defect is the operator-geometric source of torsion/anomaly and thus
  macroscopic irreversibility.

## 4. Unified Statement

The framework unifies:

1. RN chain composition,
2. cocycle transport in modular flow,
3. logarithmic thermodynamic linearization,
4. and broken detailed balance from noncommutative update order.

So entropy-producing irreversibility appears as a structural consequence of
nontrivial cocycle holonomy in the information-geometry operator stack.
