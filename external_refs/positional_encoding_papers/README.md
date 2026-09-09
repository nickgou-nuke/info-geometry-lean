# Positional-encoding source map

These are external mathematical references.  Lean source and kernel checking
remain the proof authority.

| Reference | Main formulation | Local Lean owner |
|---|---|---|
| [RoFormer, arXiv:2104.09864](https://arxiv.org/abs/2104.09864) | Rotation-matrix RoPE and relative inner-product dependence | `Clifford/Cl55RoPESplitTorusBridge.lean`, `Routing/DiscreteRoPERepresentation.lean`, `Canonical/PositionalDynamicsRegimeBridge.lean` |
| [ALiBi, arXiv:2108.12409](https://arxiv.org/abs/2108.12409) | Additive query-key score bias proportional to relative distance | `Volume/PfaffianPathBridge.lean` is unrelated; a dedicated score-bias owner is still needed |
| [FourierLearner, arXiv:2302.01925](https://arxiv.org/abs/2302.01925) | Spectral/Fourier representation of relative-position kernels | `Canonical/CyclotomicProjectorReadout.lean`, `OperatorAlgebra/KANCharacterFactorization.lean` |
| [HoPE, arXiv:2509.05218](https://arxiv.org/abs/2509.05218) | Hyperbolic/Lorentz boost positional encoding | `Clifford/Cl55RoPESplitTorusBridge.lean`, `Topology/ChiralContinuousHyperbolicRotor.lean` |
| [Geometric Deep Learning, arXiv:2104.13478](https://arxiv.org/abs/2104.13478) | Fourier/DFT interpretation of grid and graph positional structure | `Canonical/CyclotomicProjectorReadout.lean` |

## Formalization status

Already kernel-checked locally:

- additive elliptic and hyperbolic rotor laws;
- relative-position laws;
- Jordan nilpotent exponential truncation to a polynomial;
- LogCFT unipotent shear composition;
- transformer and masked-transformer positional-flow composition;
- Fourier/cyclotomic projector readouts.

Still requiring dedicated Lean owners:

- the ALiBi score-level construction and its augmentation into query/key
  vectors;
- the general FourierLearner spectral kernel and its finite approximation;
- higher-dimensional direct-sum positional groups;
- any direct equivalence between twin-wave, Pfaffian, and positional carriers.

The downloaded PDFs are retained only as source context; no empirical claim is
promoted to a Lean theorem without an explicit mathematical contract.
