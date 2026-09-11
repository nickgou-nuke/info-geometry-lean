import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Finite Weil-Form Positivity

This module formalizes a finite two-coordinate Euclidean quadratic form,
its positivity and definiteness, and a pointwise finite-readout lemma.  The
notation is deliberately GNS-shaped, but no arithmetic convolution,
zero-spectrum evaluation, trace formula, or colimit is constructed here.

These are finite Euclidean/GNS-shaped shadows only.  They do **not** prove
the arithmetic Weil positivity criterion, RH, a trace formula, or a
self-adjoint colimit operator.  The genuine arithmetic statement is retained
as an explicit source interface at the end of the file.
-/

noncomputable section

namespace InfoGeometry.Spectral.WeilPositivity

/-- GNS Test Observable State in Modal Basis -/
@[ext]
structure ModalWavepacket where
  re : ℝ
  im : ℝ

namespace ModalWavepacket

/-- Weil quadratic expectation functional: W(g * g*) = ||psi_g||^2 -/
def weilFunctional (g : ModalWavepacket) : ℝ :=
  g.re ^ 2 + g.im ^ 2

/-- 🏆 THEOREM 1: Exact Weil Positivity -/
theorem weil_positivity (g : ModalWavepacket) : 0 ≤ g.weilFunctional := by
  dsimp [weilFunctional]
  have h1 : 0 ≤ g.re ^ 2 := sq_nonneg _
  have h2 : 0 ≤ g.im ^ 2 := sq_nonneg _
  exact add_nonneg h1 h2

/-- 🏆 THEOREM 2: Weil Definiteness (W = 0 iff state = 0) -/
theorem weil_definiteness (g : ModalWavepacket) :
    g.weilFunctional = 0 ↔ g.re = 0 ∧ g.im = 0 := by
  dsimp [weilFunctional]
  constructor
  · intro h
    have h1 : 0 ≤ g.re ^ 2 := sq_nonneg _
    have h2 : 0 ≤ g.im ^ 2 := sq_nonneg _
    have h_re_sq : g.re ^ 2 = 0 := by linarith
    have h_im_sq : g.im ^ 2 = 0 := by linarith
    constructor
    · exact sq_eq_zero_iff.mp h_re_sq
    · exact sq_eq_zero_iff.mp h_im_sq
  · rintro ⟨h_re, h_im⟩
    rw [h_re, h_im]
    ring

end ModalWavepacket

/-- 2-Zero Spectral Pairing on the Critical Line -/
def spectralPairing (g1 g2 : ModalWavepacket) : ℝ :=
  g1.weilFunctional + g2.weilFunctional

/-- 🏆 THEOREM 3: Spectral Sum Positivity -/
theorem spectralPairing_nonneg (g1 g2 : ModalWavepacket) :
    0 ≤ spectralPairing g1 g2 := by
  dsimp [spectralPairing]
  have h1 := g1.weil_positivity
  have h2 := g2.weil_positivity
  exact add_nonneg h1 h2

/-- 🏆 THEOREM 4: Spectral Sum Definiteness -/
theorem spectralPairing_eq_zero_iff (g1 g2 : ModalWavepacket) :
    spectralPairing g1 g2 = 0 ↔ (g1.re = 0 ∧ g1.im = 0) ∧ (g2.re = 0 ∧ g2.im = 0) := by
  dsimp [spectralPairing]
  have h1 := g1.weil_positivity
  have h2 := g2.weil_positivity
  constructor
  · intro h
    have h_g1 : g1.weilFunctional = 0 := by linarith
    have h_g2 : g2.weilFunctional = 0 := by linarith
    constructor
    · exact (g1.weil_definiteness).mp h_g1
    · exact (g2.weil_definiteness).mp h_g2
  · rintro ⟨⟨r1, i1⟩, ⟨r2, i2⟩⟩
    have h_g1 : g1.weilFunctional = 0 := (g1.weil_definiteness).mpr ⟨r1, i1⟩
    have h_g2 : g2.weilFunctional = 0 := (g2.weil_definiteness).mpr ⟨r2, i2⟩
    rw [h_g1, h_g2, add_zero]

/-! ## Finite-family GNS shadow -/

def finiteSpectralPairing (waves : Finset ModalWavepacket) : ℝ :=
  ∑ g ∈ waves, g.weilFunctional

theorem finiteSpectralPairing_nonneg (waves : Finset ModalWavepacket) :
    0 ≤ finiteSpectralPairing waves := by
  unfold finiteSpectralPairing
  exact Finset.sum_nonneg fun g _ => g.weil_positivity

theorem finiteSpectralPairing_eq_zero_iff (waves : Finset ModalWavepacket) :
    finiteSpectralPairing waves = 0 ↔
      ∀ g ∈ waves, g.re = 0 ∧ g.im = 0 := by
  classical
  induction waves using Finset.induction_on with
  | empty =>
      simp [finiteSpectralPairing]
  | @insert g waves hgw ih =>
      constructor
      · intro hzero x hx
        have hsum :
            g.weilFunctional + (∑ x ∈ waves, x.weilFunctional) = 0 := by
          simpa [finiteSpectralPairing, Finset.sum_insert, hgw] using hzero
        have hrest : 0 ≤ ∑ x ∈ waves, x.weilFunctional := by
          exact Finset.sum_nonneg fun x _ => x.weil_positivity
        have hgzero : g.weilFunctional = 0 := by
          have hg_nonneg := g.weil_positivity
          linarith
        have hrestzero : (∑ x ∈ waves, x.weilFunctional) = 0 := by
          have hg_nonneg := g.weil_positivity
          linarith
        by_cases hxg : x = g
        · subst x
          exact (g.weil_definiteness).mp hgzero
        · have hxwaves : x ∈ waves := by
            exact Finset.mem_of_mem_insert_of_ne hx hxg
          exact (ih.mp hrestzero) x hxwaves
      · intro hall
        have hgzero : g.weilFunctional = 0 :=
          (g.weil_definiteness).mpr (hall g (by simp))
        have hwaves : ∀ x ∈ waves, x.re = 0 ∧ x.im = 0 := by
          intro x hx
          exact hall x (by simp [hx])
        rw [finiteSpectralPairing, Finset.sum_insert hgw, hgzero, zero_add]
        exact ih.mpr hwaves

theorem finiteSpectralPairing_pos_iff (waves : Finset ModalWavepacket) :
    0 < finiteSpectralPairing waves ↔
      ∃ g, g ∈ waves ∧ (g.re ≠ 0 ∨ g.im ≠ 0) := by
  constructor
  · intro hpos
    by_contra hnone
    push_neg at hnone
    have hall : ∀ g ∈ waves, g.re = 0 ∧ g.im = 0 := by
      intro g hg
      exact hnone g hg
    have hsumzero : finiteSpectralPairing waves = 0 :=
      (finiteSpectralPairing_eq_zero_iff waves).2 hall
    linarith
  · rintro ⟨g, hg, hne⟩
    have hterm : 0 < g.weilFunctional := by
      dsimp [ModalWavepacket.weilFunctional]
      rcases hne with hre | him
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hre) (sq_nonneg _)
      · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero him)
    unfold finiteSpectralPairing
    exact Finset.sum_pos'
      (fun x _ => x.weil_positivity)
      ⟨g, hg, hterm⟩

/--
Compatibility alias for pointwise positivity after a supplied finite readout.
Despite its historical name, this theorem does not assert a colimit
construction or transition-map compatibility.
-/
theorem colimit_preservation_of_weil_positivity
    (iota : ℕ → ModalWavepacket → ModalWavepacket)
    (n : ℕ) (g : ModalWavepacket) :
    0 ≤ (iota n g).weilFunctional := by
  have h := (iota n g).weil_positivity
  exact h


theorem weil_positive_on_self_convolution
    {TestFunction : Type*}
    (convolution : TestFunction → TestFunction → TestFunction)
    (star : TestFunction → TestFunction)
    (weil : TestFunction → ℝ)
    (hpositive : ∀ g, 0 ≤ weil (convolution g (star g)))
    (g : TestFunction) :
    0 ≤ weil (convolution g (star g)) :=
  hpositive g

end InfoGeometry.Spectral.WeilPositivity
