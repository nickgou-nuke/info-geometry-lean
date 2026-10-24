# Prefix-local bipartite Sinkhorn response

## Source and base

Additive follow-up to PR #199, inspected at
`08f251a4b2c18eac4f20d68a30a2c3610390c9ce`.
Sources supplied in this conversation:
- `Pasted text(20261023-084704).txt`: multi-head shape/detector architecture.
- `Pasted text (2)(20261023-085152).txt`: block/strict-token implementation.
- `Pasted text (3)(4).txt`: finite prefix locality and future derivative proof.

The parent runtime owners `differentiable_sinkhorn_core_decomposition` and
`BistochasticBipartiteLaplacianSolver` are reused unchanged. Existing positive
matrix Sinkhorn normalization is owned by `Canonical.SinkhornFoundation`;
its statements and `Inference.PoissonSinkhornPotentials` were inspected. The
new Lean recurrence is an operational finite log-coordinate model, not a new
stochasticity predicate, Sinkhorn convergence proof or inverse construction.
No whole-repository absence/novelty claim is made.

## Ground-truth theorem contract

Carrier: finite real coordinate spaces and native Matrix, Finset, Set.EqOn,
Function.update, HasFDerivAt and ContinuousLinearMap. Allowed finite sets model
masks. Empty allowed sets pool to zero; probability normalization is proved
only for a nonempty allowed set. The homogeneous weighted-mean merging
identity and the nested-pooling identity establish the real algebra behind
online pooling; they do not prove a floating-point implementation.

For prefix-local input data, finite log-Sinkhorn, normalized detector decoding
and any pure current-channel processor preserve Set.EqOn prefix agreement.
Updating a future coordinate gives a constant partial map. That *actual*
pipeline partial map has derivative zero and zero cotangent pullback, using
native normed-space instances on a product of coordinate spaces. This needs
neither past-direction differentiability nor invertibility of a channel
matrix. It does not establish correctness or existence of a Poisson inverse.

The finite Sinkhorn theorem proves exact reconstruction and the final column
sum after a completed column update. It does not infer exact row sums at a
finite iteration count. Meaningful physical temperature is positive; locality
itself is algebraic and does not require that restriction.

## Changes from the supplied code (not silent corrections)

1. Strict-token source code selects `det_logits_prefix[..., -1, :, :]`, the
   entire query chunk, then shares its core/Poisson solution with every token.
   With seed 7, double precision, d_model=8, heads=2, channels=3, chunk_size=3,
   the derivative of token 4's output sum with respect to token 5 has maximum
   magnitude 0.012101990495516066. Future *chunk* derivatives are zero. The new
   strict mode uses a different detector prefix and core solve at every token.
   Block mode remains bidirectional within a chunk, as intended by the source.
2. Streaming state stores log mass and normalized key/value sums; it does not
   construct the source's C-by-C inter-chunk tensor. Exact -infinity masks and
   explicit zero-mass branches replace -1e9 sentinels. No virtual padding
   tokens are projected; explicit key/query padding is supported. Entirely
   padded prefixes produce finite zero outputs and gradients.
3. The source adds epsilon I to both reduced Gramian systems but describes the
   result as the original exact Poisson solution. On centered components this
   produces residual -epsilon z. This extension reuses the parent's unshifted,
   guarded solver; unresolved/disconnected cores are rejected, not silently
   regularized. Finite iteration and numerical residual qualifications remain.
4. `B^T U^T values` with detector responsibilities proportional to V*d_det is
   the source's balanced-channel branch. It is not generally the normalized
   five-factor C^T readout because it omits shape gains. The balanced branch is
   retained by default and named explicitly. Optional `direct_mode='five_factor'`
   uses r=B^T a, z=B^T diag(a) U^T values / r, and responsibilities proportional
   to V*diag(b*r); it equals C^T values / (C^T 1) for C=U diag(a) B diag(b) V^T.
5. Dropout is applied after readout, not to normalized probability weights.
   `poisson_mix_init` is a probability converted to a logit, not itself a logit.
   With no history, strict mode uses the local attention output alone.
6. The source Lean output omits the runtime's detector row normalization.
   The new pipeline explicitly normalizes those responsibilities. Its processor
   remains abstract and it certifies chunk-coordinate dependence, not compiled
   Python or all extraction/projection code. Strict-token Python causality is
   tested separately. Source snippets are not claimed to compile unchanged.

## Complexity and scope

Let N tokens, C chunks of maximum length L, K channels, d head features.
Online shape pooling costs O(N K d) arithmetic, with O(Kd) live prefix state.
Block mode performs C latent solves, O(C K^3). Strict mode uses a per-token
query-prefix core and therefore O(N K^3), plus O(N L d) local attention. Training
retains intermediate autograd states; the live-state bound is not total training
memory. Standard dot-product attention does not intrinsically require an
N-by-N matrix inverse: the notes' O(N^3) comparison concerns a token-level
Poisson solver, not ordinary attention.

This is a sequential reference architecture, not a fused GPU implementation or
API-identical replacement for torch.nn.MultiheadAttention. No train_entropic.py
file is patched. No speedup, training convergence or universal KV eviction is
claimed. Causality means input-to-output dependency for fixed parameters and
fixed stochastic masks, on finite successfully admitted inputs. Global diagnostic
summaries and exception behaviour are not claimed to be prefix-local.

## Use

```python
from tools.causal_bipartite_sinkhorn import BlockCausalMultiHeadBipartiteSinkhornAttention
layer = BlockCausalMultiHeadBipartiteSinkhornAttention(
    d_model=128, n_heads=4, num_channels=8, chunk_size=16,
    causal_mode='strict_token_causal', sinkhorn_iters=100)
y, diagnostics = layer(x, key_padding_mask=padding, return_diagnostics=True)
```

The noncausal `MultiHeadBipartiteSinkhornAttention` also supports cross attention.
Both classes accept float32/float64. Failed balancing requires more iterations;
there is no implicit change to the mathematical operator.

## Evidence at submission

17 local tests passed using PyTorch 2.10.0+cpu, including full-Jacobian forbidden
blocks, same-chunk future perturbations, masked/empty-prefix cases, exact-real
formula comparisons to tolerance, two gradient checks, solver agreement, and
prefix-extension tests. These tests do not replace Lean verification.

The dedicated workflow compiles only the two new modules with unchanged pinned
Mathlib and audits every new declaration. This does not certify all parent
modules or repository-wide CI. Parent PR #199 remains a draft with a failing
scoped Lean build at the inspected head. No parent files, dependency pins,
existing workflows or umbrella imports are changed by this follow-up.
