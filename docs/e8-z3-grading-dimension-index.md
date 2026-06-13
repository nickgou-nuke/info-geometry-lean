# E8 Z3 Grading Dimension Index

> Owner: `lean/InfoGeometry/Canonical/E8Z3GradingDimension.lean`
>
> SymPy witness: `tools/sympy/e8_z3_grading_dimension.py`

This index records the proof strength of the finite dimension packet behind the
`Z3` grading slogan.

## Closed Lean Content

The Lean owner proves:

- neutral modeled dimension `8 + 78 = 86`;
- each flow modeled dimension `3 * 27 = 81`;
- total modeled split `86 + 81 + 81 = 248`;
- each sector charge is annihilated by multiplication by `3` modulo `3`;
- `e8_z3_grading_dimension_packet` bundles those finite facts.

## SymPy Witness

The SymPy script verifies the same dimension split and constructs a diagonal
order-three grading matrix with eigenvalue multiplicities `86`, `81`, and `81`.

## Not Proved Here

This is not a proof of:

- construction or classification of the `E8` Lie algebra;
- existence of an order-three automorphism on `E8`;
- fixed algebra `su(3) + e6`;
- representation branching into `(3,27)` and `(3bar,27bar)`;
- QCD, observed Standard Model generations, or phenomenology;
- zeta-zero, Weyl-character, or Riemann-hypothesis consequences.
