import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
import InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge

/-!
# Finite Matrix Gauge Trace Bridge

This module proves the exact alignment between the normalized finite matrix trace
$\operatorname{tr}_n(E_{ij})$ on $M_{2^n}(\mathbb{C})$ and the canonical gauge state
$\varphi_{\mathrm{gauge}}(S_u S_v^\dagger)$ on words of length $n$:

$$\operatorname{tr}_n(E_{ij}) = 2^{-n} \delta_{ij} = \varphi_{\mathrm{gauge}}(S_u S_v^\dagger)$$

when $u, v \in \operatorname{BitWord} n$ correspond to matrix indices $i, j \in \operatorname{Fin}(2^n)$.
-/

noncomputable section

open Matrix
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliGaugeStateBridge
open InfoGeometry.OperatorAlgebra.CuntzCanonicalGaugeGNSState

namespace InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeTraceBridge

abbrev BitWord (n : ℕ) := Fin n → Bool

noncomputable def bitWordIndexEquiv (n : ℕ) : BitWord n ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (by simp [Fintype.card_fun])

/-- 🏆 THEOREM: Alignment between the finite matrix trace state and the gauge expectation. -/
theorem matrixTraceState_eq_canonicalGaugeState
    (n : ℕ) (i j : Fin (2 ^ n)) (u v : BitWord n)
    (h_diag_match : (i = j) ↔ (u = v)) :
    matrixTraceState n (Matrix.single i j 1) = canonicalGaugeState (List.ofFn u) (List.ofFn v) := by
  rw [matrixTraceState_single, canonicalGaugeState_word, List.length_ofFn]
  rw [one_div, ← inv_pow]
  have h_word_eq : (List.ofFn u = List.ofFn v) ↔ (u = v) := by
    constructor
    · intro h
      exact List.ofFn_injective h
    · intro h
      rw [h]
  by_cases hij : i = j
  · have huv : u = v := h_diag_match.mp hij
    have hlist : List.ofFn u = List.ofFn v := h_word_eq.mpr huv
    simp [hij, hlist]
  · have huv : ¬(u = v) := (not_iff_not.mpr h_diag_match).mp hij
    have hlist : ¬(List.ofFn u = List.ofFn v) := (not_iff_not.mpr h_word_eq).mpr huv
    simp [hij, hlist]

/-! The canonical finite word equivalence removes the diagonal-matching
hypothesis from the matrix-unit readout. -/
theorem matrixTraceState_bitWordUnit_eq_canonicalGaugeState
    (n : ℕ) (u v : BitWord n) :
    matrixTraceState n
        (Matrix.single (bitWordIndexEquiv n u) (bitWordIndexEquiv n v) 1) =
      canonicalGaugeState (List.ofFn u) (List.ofFn v) := by
  apply matrixTraceState_eq_canonicalGaugeState
  exact (bitWordIndexEquiv n).injective.eq_iff

end InfoGeometry.Canonical.CantorBernoulliFiniteMatrixGaugeTraceBridge
