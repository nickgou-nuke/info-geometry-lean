/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Hermitian
import InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset

/-!
# Metriplectic–Causal Archetypes in Native Mathlib (Shared Conversation `9666a5a14e0d`)

This module records the noncommutative star-cut identities and the conjugate-transpose
Krein identities for actual `2 × 2` matrices over an arbitrary star ring. It reuses
the companion owner
`InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset`
for its block definitions and chiral Dirac identities. It makes no positivity,
commutative-scalar, or physical interpretation claim.

## Archetype inventory (pure mathematics) and routing

* **A1 (binary star cut; formalized here).** In any star ring, `x + x*` is
  self-adjoint, `x - x*` is skew-adjoint, and their sum is `2x`; with `2` invertible this
  is the decomposition `x = s + k`, `s* = s`, `k* = -k`.  The companion's
  `metriplectic_star_parity` is the `S/K`-parity corollary.
* **A3 (Krein adjoint; formalized here).** Under star parity
  (`S* = S`, `K* = -K`) the metriplectic block satisfies
  `M(S,K)ᴴ = J M(S,K) J` with `J = diag(1,-1)` — the faithful `conjTranspose` form of the
  companion's scalar-family `krein_self_adjoint_metriplectic_2x2` — and the chiral Dirac
  block `D(S,K)` is `Matrix.IsHermitian`.  The companion's `chiralDiracBlock_sq`
  (`D² = diag(G_out, G_in)`), `equilibriumFlowRoot_sq` (true `E²` with commutator
  off-diagonals), and `metriplectic_star_parity` cover the remaining doubling algebra.
* **A4 (Turn 10 — Walsh–Hadamard elenchus).** Reused from the companion:
  `walshHadamard_conjugation_elenchus` (`H₂ cl11Elem(dᵢ,d_p,d_s,d_c) H₂ =
  2 cl11Elem(dᵢ,d_s,d_p,-d_c)`, symmetric commuting conjugates, zero ε-weight),
  `sramXorSwizzle_involution_and_bijective`, `hypercube_bipartite_nonplanar_bound`,
  `talaska_urbanRenewal_schur_identity`.
* **A5 (Turn 05 — light-cone nullity, corrected).** Reused:
  `lightCone_nullity_and_cross_pairing` proves `(2Π±)ᵀ J (2Π±) = 0` and the corrected
  cross-pairing `2(J + ε)` (the source conversation's `½(J - ε)` is a sign/scale error).
* **A6 (Turns 05–06 — Witt CAR ladder).** Reused: `pfaffian_and_witt_car_ladder`.
* **A7 (Turn 06 — Jordan–Wigner `Cl(2,2)`).** Reused: `jordanWigner_cl22_relations`,
  `jordanWigner_isotropic_norm_vs_ungraded_aporia`.
* **A8 (Turn 11 — Lorentzian determinant, Cayley, dual horizons).** Reused:
  `cl11_lorentzian_det_resolvent_and_cayley`, `cl11_dual_critical_horizons`.
* **A9 (Turn 12 — BCFW amalgamation).** Reused: `bcfw_amalgamation_and_bridge_commutator`.
* **A10 (Turn 13 — Krein–Hamiltonian–Hopf crash).** Reused:
  `kreinHamiltonianHopf_bifurcation`, `kreinCrash_jordan_chain_and_null_norm`.
* **A11 (Turns 14–15 — Yangian surrogates).** Reused:
  `yangR4_unitarity_and_resonant_collapse`, `yangian_braided_qybe`,
  `yangian_parametric_braided_qybe`, `matrix3_braid_and_parametric_qybe`,
  `lax_rtt_and_quantum_determinant`, `clifford_ep_artin_braid_and_period_eight`
  (period **8**, correcting the Turn 14 prose claim of period 4).
* **A12 (Turn 16 — Zitterbewegung, ℤ₄ monodromy).** Reused:
  `diracKrein_carrier_decoupling_and_zitter_split`, `diracKrein_secular_crash_evolution`,
  `spinMonodromyEP_z4_periodicity`.
* **A13 (Turns 16–17 — FW rapidity dictionary).** Reused from the companion
  (`foldyWouthuysen_real_rapidity_bridge`, `thomasWigner_precession_commutator`) and from
  `InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge`
  (`loopWeight θ = -tanh²θ`, canonical rapidity `θ = artanh √(-f)` round trip
  `loopWeight_artanh_sqrt`, Schur prefactor `(1-f)/(1+f) = cosh 2θ`, dressed strand
  product `sinh(2θ)²/4`).
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalArchetypesNative

open scoped Matrix
open InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalPlabicKreinYangianPoset

/-! ## A1: the binary star cut in native star-ring form -/

section StarCut

variable {K : Type*} [Ring K] [StarRing K]

/-- **A1 (Turn 01).** In any star ring, `x + x*` is self-adjoint. -/
theorem isSelfAdjoint_add_star (x : K) : IsSelfAdjoint (x + star x) := by
  show star (x + star x) = x + star x
  rw [star_add, star_star]
  abel

/-- **A1 (Turn 01).** In any star ring, `x - x*` is skew-adjoint. -/
theorem star_sub_star_eq_neg (x : K) : star (x - star x) = -(x - star x) := by
  rw [star_sub, star_star]
  abel

/-- **A1 (Turn 01, doubled form).** The self-adjoint and skew-adjoint doubled parts sum
to the double of `x`: `x + x* + (x - x*) = 2x`.  With `2` invertible this recovers the
source's halves `S = (x + x*)/2`, `K = (x - x*)/2`; the doubled form avoids the halving. -/
theorem doubled_star_cut (x : K) : x + star x + (x - star x) = x + x := by
  abel

end StarCut

/-! ## A3 (Turns 01, 04): the faithful `conjTranspose` Krein adjoint of the doubled blocks -/

section KreinDoubling

variable {B : Type*} [Ring B] [StarRing B]

/-- **A3 (Turn 04, faithful form).** Under star parity (`S* = S`, `K* = -K`) the
metriplectic block is Krein self-adjoint in the native conjugate-transpose sense:
`M(S, K)ᴴ = J M(S, K) J` with `J = diag(1, -1)`.  The companion's
`krein_self_adjoint_metriplectic_2x2` proves the analogous identity for the different
scalar family `[[s, k], [-k, s]]`; this is the block claim the source actually makes. -/
theorem kreinJ_selfAdjoint_metriplecticBlock (S K : B) (hS : star S = S)
    (hK : star K = -K) :
    Matrix.conjTranspose (metriplecticBlock S K) =
      !![(1 : B), 0; 0, -1] * metriplecticBlock S K * !![(1 : B), 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [metriplecticBlock, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_two, hS, hK]

/-- **A3 (Turn 01).** Under star parity the chiral Dirac block `D(S, K)` is Hermitian:
`D(S, K)ᴴ = D(S, K)`.  Proved by reusing the companion's `metriplectic_star_parity`
(which gives `star (causalForward S K) = causalBackward S K`) rather than re-expanding
the star parity by hand. -/
theorem chiralDiracBlock_isHermitian (S K : B) (hS : star S = S) (hK : star K = -K) :
    Matrix.IsHermitian (chiralDiracBlock S K) := by
  have h := metriplectic_star_parity S K hS hK
  have hcb : star (causalBackward S K) = causalForward S K := by
    rw [← h.1, star_star]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralDiracBlock, Matrix.conjTranspose_apply, h.1, hcb]

end KreinDoubling

end InfoGeometry.OperatorAlgebra.PeirceSpine.MetriplecticCausalArchetypesNative
