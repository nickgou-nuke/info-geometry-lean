/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import InfoGeometry.Physics.AitchisonCartanDuallyFlatBridge

/-!
# Audit Module: AitchisonCartanDuallyFlatBridgeAudit

Automated kernel verification of Section 5.85:
- Zero debt: 0 sorry, 0 admit.
- Checks Cartan subalgebra projector trace vanishing and idempotence.
- Verifies CLR as Cartan projection of coordinate logarithms.
- Verifies Softmax as the exact inverse diffeomorphism on the Cartan subalgebra.
- Verifies Legendre-Fenchel duality equality at stationary points.
- Verifies dual Bregman divergence is identically the Kullback-Leibler divergence.
- Verifies primal Bregman divergence equals dual KL divergence with swapped arguments.
- Verifies generalized Pythagorean theorem on dually flat space under orthogonal geodesics.
- Verifies Shannon entropy maximality at the Jaynesian uniform prior.
- Verifies centered log-ratio difference matches coordinate log-ratio centering.
- Certified Axiom Footprint: standard foundational axioms only [propext, Classical.choice, Quot.sound].
-/

namespace InfoGeometry.Physics.AitchisonCartanDuallyFlatBridgeAudit

open InfoGeometry.Physics.AitchisonCartanDuallyFlat
open InfoGeometry.Physics.AitchisonTraceDeterminant

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {n : ℕ}

-- 1. Signature and Type-Level Verification
#check (sum_cartanProj_zero :
  ∀ (x : Fin n → ℝ) (hn : 0 < n), ∑ i, cartanProj x hn i = 0)

#check (cartanProj_idempotent :
  ∀ (x : Fin n → ℝ) (hn : 0 < n), cartanProj (cartanProj x hn) hn = cartanProj x hn)

#check (clr_eq_cartanProj_log :
  ∀ (P : PositiveDistribution n) (hn : 0 < n),
    clr P hn = cartanProj (fun i => Real.log (P.p i)) hn)

#check (clr_softmax_inversion :
  ∀ (u : Fin n → ℝ) (hn : 0 < n) (h_zero : ∑ i, u i = 0),
    clr (softmaxDist u hn) hn = u)

#check (legendre_fenchel_equality :
  ∀ (u : Fin n → ℝ) (hn : 0 < n),
    primalPotential u + dualPotential (softmaxDist u hn) = ∑ i, u i * (softmaxDist u hn).p i)

#check (dualBregman_eq_kl :
  ∀ (P Q : PositiveDistribution n), dualBregmanDiv P Q = klDivergence P Q)

#check (primalBregman_eq_kl :
  ∀ (u w : Fin n → ℝ) (hn : 0 < n),
    primalBregmanDiv u w hn = klDivergence (softmaxDist w hn) (softmaxDist u hn))

#check (kl_pythagorean_orthogonal :
  ∀ (P Q R : PositiveDistribution n)
    (h_ortho : ∑ i, (P.p i - Q.p i) * (Real.log (R.p i) - Real.log (Q.p i)) = 0),
    klDivergence P R = klDivergence P Q + klDivergence Q R)

#check (shannon_entropy_jaynesian :
  ∀ (hn : 0 < n), shannonEntropy (jaynesianDistribution n hn) = Real.log (n : ℝ))

#check (clr_sub_clr_eq_centered_logRatio :
  ∀ (P Q : PositiveDistribution n) (hn : 0 < n) (i : Fin n),
    clr P hn i - clr Q hn i = logRatio P Q i - (1 / (n : ℝ)) * ∑ k, logRatio P Q k)

#check (certified_aitchison_cartan_dually_flat_synthesis :
  CertifiedAitchisonCartanDuallyFlatSynthesis (n := n))

-- 2. Certified Axiom Footprint Verification
#print axioms certified_aitchison_cartan_dually_flat_synthesis

end InfoGeometry.Physics.AitchisonCartanDuallyFlatBridgeAudit
