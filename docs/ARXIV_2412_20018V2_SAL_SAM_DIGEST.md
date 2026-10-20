# Alexandria digest: arXiv:2412.20018v2

## Provenance

- Source: [arXiv:2412.20018v2](https://arxiv.org/abs/2412.20018)
- Title: *How Biological Synapses Self-Assemble Gradient Learning*
- Authors: Qianli Liao, Liu Ziyin, Yulu Gan, Brian Cheung, Mark T. Harnett, Tomaso Poggio
- Local PDF SHA-256: `54676e1a96c41dbb071a83b3ef9e6b9c8a092a516a3ac4ad18341aa7aea57136`
- PDF metadata: 36 pages; arXiv version 2 dated 2026-10-12
- Alexandria extraction: 416 chunks, 140 canonical entities, 395 connected components
- Alexandria run id: `7fd319c0dab7b2b0`
- Raw extraction was made with `pdftotext -layout`; the semantic artifacts are retained in
  `/tmp/alexandria_2412_20018/semantic` and the local overlay in
  `/tmp/alexandria_2412_20018/overlay`.

This document records source-linked candidate mathematics. It does not treat the paper's
empirical results or biological interpretation as Lean theorems.

## Atomic archetypes

The labels below are normalized mathematical objects, not claims that the repository
already formalizes them.

| ID | Archetype | Source location | Classification |
| --- | --- | --- | --- |
| A0 | A two-stream layered state: upstream activations (h^\ell) and downstream activations \(\bar h^\ell\), with separate dimensions allowed | Main text §3.1, PDF pp. 6–7 | definition/model input |
| A1 | Forward and feedback recurrence \(h^{\ell+1}=W^\ell D_u^\ell h^\ell\), \(\bar h^\ell=\bar W^\ell D_d^{\ell+1}\bar h^{\ell+1}\) | §3.1, PDF p. 6 | definition |
| A2 | Four local heterosynaptic update rules for \(W,\bar W,V,\bar V\), each an outer-product signal minus local decay | equations (1)–(4), PDF p. 7 | definition |
| A3 | Forward/feedback pathway operators \(F^\ell,B^\ell\) and pathway error \(E_p^\ell=F^\ell-B^\ell\) | equation (5), §3.2, PDF p. 8 | definition |
| A4 | Interstream error \(E_v^\ell=V^\ell-(\bar V^{\ell-1})^T\) | equation (6), §3.2, PDF p. 8 | definition |
| A5 | Matched-rate cancellation law \(\Delta E_v^\ell=-\gamma E_v^\ell\), hence discrete exponential decay | Theorem/lemma discussion; SI Lemma 1, equations (19)–(21), PDF pp. 8, 18 | proved conditional result |
| A6 | Depth-chain telescoping: the SAM signal equals the backpropagated signal plus an explicit residual bounded by primitive alignment errors | SI Lemma 2, equations (22), (30), (41), PDF pp. 18–19 | proved conditional result |
| A7 | Generalized SGD update \(\Delta W^\ell=\eta_W(H_D^\ell+E_{v,D}^\ell)\Delta_{sgd}W^\ell-\gamma W^\ell+R^\ell\) under rank, boundary, rate, and error hypotheses | Main Theorem 1 and SI Theorem 2, equations (7), (23)–(24), PDF pp. 8, 19 | proved conditional result |
| A8 | Aligned preconditioner \(H_D^\ell=(D_u^{\ell+1}\bar V^\ell)(D_u^{\ell+1}\bar V^\ell)^T\) is positive semidefinite | SI Theorem 2, PDF p. 19 | proved algebraic consequence |
| A9 | Exact aligned limit: if all relevant \(E_p,E_v\) vanish, the residual vanishes and SAM reduces to PSD-preconditioned SGD with weight decay | SI Theorem 2, PDF p. 19 | proved conditional result |
| A10 | Interstream alignment is proved by the local rule, while pathway alignment \(E_p\to0\) is explicitly not proved from the rules alone | Remarks 1–2, PDF pp. 8, 19 | scope limitation |
| A11 | Biological realizability is graded by how much architecture is self-assembled rather than stipulated | Introduction/Fig. 1, PDF pp. 2–3 | interpretation |
| A12 | SAM's empirical benchmark and stability diagnostics compare against SGD and other baselines | §3.3 and figures/tables, PDF pp. 9–17 | empirical evidence |

## Causal poset

The dependency order is recorded in
`artifacts/alexandria/external/arxiv_2412_20018v2/causal_poset.json`.
The core chain is

\[
A0 \prec A1 \prec A2 \prec (A3,A4) \prec A5 \prec A6 \prec A7 \prec A8 \prec A9.
\]

A10 constrains A6–A9 rather than following from them. A11 and A12 are interpretation
and evidence nodes and do not supply premises for the formal chain.

## Lean formalization contracts

The smallest native Mathlib contracts are finite-dimensional and should be formalized in
this order:

1. Define finite layer data over a field, matrices with conformable dimensions, and the
   two recurrences (A0–A1).
2. Define the four update expressions and the two errors (A2–A4).
3. Prove the exact matched-rate cancellation identity (A5) for one layer. This is the
   highest-return source theorem because it needs only matrix addition, transpose, and
   scalar arithmetic.
4. Formalize the aligned preconditioner as `M * Mᵀ` and prove positive semidefiniteness
   using the existing Mathlib quadratic-form lemmas (A8).
5. State the depth-chain and generalized-SGD results only with the paper's rank,
   boundary, norm, and residual hypotheses (A6–A9). Do not promote the empirical claim
   `E_p → 0` (A10) to a theorem.

No claim here identifies SAM with a Clifford, Krein, KMS, or colimit construction. Any
future bridge must provide an explicit representation and a proved map between carriers.
