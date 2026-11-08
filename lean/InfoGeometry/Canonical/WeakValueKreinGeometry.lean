import InfoGeometry.Krein.DoubledSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Complex transition overlap and two real Krein quadratics

The two components of the repository's doubled L² carrier are the post- and
pre-selected vectors. The diagonal signature form measures their norm
difference. The swap form measures the real part of their transition overlap;
a phase-twisted swap measures its imaginary part. Therefore a complex overlap
vanishes precisely when both swap quadratics vanish. Diagonal isotropy alone
does not assert orthogonal selection or a singular weak-value denominator.
-/

noncomputable section

namespace InfoGeometry.Canonical.WeakValueKreinGeometry

open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local instance : InnerProductSpace ℝ E := InnerProductSpace.complexToReal

/-- Complex cross-overlap, with the post-selected vector in the first slot. -/
def overlap (z : DoubledSpace E) : ℂ :=
  inner ℂ (WithLp.fst z) (WithLp.snd z)

/-- The existing diagonal signature operator, evaluated in the complex Hilbert pairing. -/
def diagonalQuadratic (z : DoubledSpace E) : ℝ :=
  (inner ℂ z (spectral_epsilon (E := E) z)).re

/-- The existing modular swap detects the real overlap. -/
def swapQuadratic (z : DoubledSpace E) : ℝ :=
  (inner ℂ z (modular_j (E := E) z)).re

/-- The second signature axis detects the imaginary overlap. -/
def phaseSwap (z : DoubledSpace E) : DoubledSpace E :=
  to_doubled ((-Complex.I) • WithLp.snd z) (Complex.I • WithLp.fst z)

def phaseSwapQuadratic (z : DoubledSpace E) : ℝ :=
  (inner ℂ z (phaseSwap z)).re

theorem diagonalQuadratic_eq_norm_difference (z : DoubledSpace E) :
    diagonalQuadratic z = ‖WithLp.fst z‖ ^ 2 - ‖WithLp.snd z‖ ^ 2 := by
  change (inner ℂ (WithLp.fst z) (WithLp.fst z) +
    inner ℂ (WithLp.snd z) (-WithLp.snd z)).re = _
  rw [inner_neg_right, Complex.add_re, Complex.neg_re]
  have hfst : (inner ℂ (WithLp.fst z) (WithLp.fst z)).re = ‖WithLp.fst z‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hsnd : (inner ℂ (WithLp.snd z) (WithLp.snd z)).re = ‖WithLp.snd z‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [hfst, hsnd]
  ring

theorem swapQuadratic_eq_two_re_overlap (z : DoubledSpace E) :
    swapQuadratic z = 2 * (overlap z).re := by
  change (inner ℂ (WithLp.fst z) (WithLp.snd z) +
    inner ℂ (WithLp.snd z) (WithLp.fst z)).re = _
  have hs : (inner ℂ (WithLp.snd z) (WithLp.fst z)).re =
      (inner ℂ (WithLp.fst z) (WithLp.snd z)).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [Complex.add_re, hs]
  unfold overlap
  ring

theorem phaseSwapQuadratic_eq_two_im_overlap (z : DoubledSpace E) :
    phaseSwapQuadratic z = 2 * (overlap z).im := by
  change (inner ℂ (WithLp.fst z) ((-Complex.I) • WithLp.snd z) +
    inner ℂ (WithLp.snd z) (Complex.I • WithLp.fst z)).re = _
  rw [inner_smul_right, inner_smul_right, Complex.add_re]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im]
  have hs : (inner ℂ (WithLp.snd z) (WithLp.fst z)).im =
      -(inner ℂ (WithLp.fst z) (WithLp.snd z)).im :=
    inner_im_symm (𝕜 := ℂ) _ _
  rw [hs]
  unfold overlap
  ring

theorem overlap_eq_zero_iff_two_swap_quadratics (z : DoubledSpace E) :
    overlap z = 0 ↔ swapQuadratic z = 0 ∧ phaseSwapQuadratic z = 0 := by
  rw [swapQuadratic_eq_two_re_overlap, phaseSwapQuadratic_eq_two_im_overlap]
  constructor
  · intro h
    simp [h]
  · rintro ⟨hRe, hIm⟩
    apply Complex.ext
    · change (overlap z).re = 0
      linarith
    · change (overlap z).im = 0
      linarith

/-- The phase-twisted swap remains an involution. -/
theorem phaseSwap_involutive (z : DoubledSpace E) :
    phaseSwap (phaseSwap z) = z := by
  apply DoubledSpace.ext <;>
    simp [phaseSwap, smul_smul, Complex.I_mul_I]

/-- The two overlap-detecting signature axes anticommute. -/
theorem phaseSwap_modular_j_anticommutes (z : DoubledSpace E) :
    phaseSwap (modular_j (E := E) z) = -(modular_j (E := E) (phaseSwap z)) := by
  apply DoubledSpace.ext <;>
    simp [phaseSwap, modular_j, neg_smul]

/-- The new signature axis is the external complex phase times the owned real rotation. -/
theorem phaseSwap_eq_I_smul_complex_i (z : DoubledSpace E) :
    phaseSwap z = Complex.I • complex_i (E := E) z := by
  apply DoubledSpace.ext <;>
    simp [phaseSwap, complex_i, modular_j, spectral_epsilon, neg_smul]

/-- Equal nonzero components are diagonal-null, while their overlap is nonzero. -/
theorem equal_components_null_with_nonzero_overlap (x : E) (hx : x ≠ 0) :
    let z : DoubledSpace E := to_doubled x x
    z ≠ 0 ∧ diagonalQuadratic z = 0 ∧ overlap z ≠ 0 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hfst := congrArg (fun z : DoubledSpace E => WithLp.fst z) h
    exact hx (by simpa using hfst)
  · rw [diagonalQuadratic_eq_norm_difference]
    simp
  · change inner ℂ x x ≠ 0
    exact inner_self_ne_zero.mpr hx

end InfoGeometry.Canonical.WeakValueKreinGeometry
