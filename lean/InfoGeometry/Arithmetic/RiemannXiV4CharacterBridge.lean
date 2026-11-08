import InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# V₄ character decomposition of a completed zeta datum

This owner records only consequences of the functional equation and Schwarz
reflection.  It makes no assertion about the location or simplicity of zeros.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannXiV4CharacterBridge

open Complex
open InfoGeometry.Topology.RiemannZetaMathlibVicinityBridge

def centeredPoint (u τ : ℝ) : ℂ := (u : ℂ) + I * (τ : ℂ)

def centeredXi (Xi : ℂ → ℂ) (u τ : ℝ) : ℂ :=
  Xi (1 / 2 + centeredPoint u τ)

def xiRealCharacter (Xi : ℂ → ℂ) (u τ : ℝ) : ℝ :=
  (centeredXi Xi u τ).re

def xiImagCharacter (Xi : ℂ → ℂ) (u τ : ℝ) : ℝ :=
  (centeredXi Xi u τ).im

private theorem centered_arg_neg_neg (u τ : ℝ) :
    1 / 2 + centeredPoint (-u) (-τ) = 1 - (1 / 2 + centeredPoint u τ) := by
  apply Complex.ext
  · simp [centeredPoint]
    ring
  · simp [centeredPoint]

private theorem centered_arg_conj (u τ : ℝ) :
    1 / 2 + centeredPoint u (-τ) = star (1 / 2 + centeredPoint u τ) := by
  apply Complex.ext
  · simp [centeredPoint]
  · simp [centeredPoint]

theorem centeredXi_neg_neg (Xi : ℂ → ℂ)
    (hXi : XiFunctionDatum Xi) (u τ : ℝ) :
    centeredXi Xi (-u) (-τ) = centeredXi Xi u τ := by
  rw [centeredXi, centeredXi, centered_arg_neg_neg]
  exact hXi.functional_eq _

theorem centeredXi_conjugate (Xi : ℂ → ℂ)
    (hXi : XiFunctionDatum Xi) (u τ : ℝ) :
    centeredXi Xi u (-τ) = star (centeredXi Xi u τ) := by
  rw [centeredXi, centeredXi, centered_arg_conj]
  exact hXi.schwarz_refl _

theorem xiReal_even_u (Xi : ℂ → ℂ)
    (hXi : XiFunctionDatum Xi) (u τ : ℝ) :
    xiRealCharacter Xi (-u) τ = xiRealCharacter Xi u τ := by
  have h₁ := congrArg Complex.re (centeredXi_neg_neg Xi hXi u (-τ))
  have h₂ := congrArg Complex.re (centeredXi_conjugate Xi hXi u τ)
  have h₁' : xiRealCharacter Xi (-u) τ = xiRealCharacter Xi u (-τ) := by
    simpa [xiRealCharacter] using h₁
  have h₂' : xiRealCharacter Xi u (-τ) = xiRealCharacter Xi u τ := by
    simpa [xiRealCharacter] using h₂
  exact h₁'.trans h₂'

theorem xiReal_even_tau (Xi : ℂ → ℂ)
    (hXi : XiFunctionDatum Xi) (u τ : ℝ) :
    xiRealCharacter Xi u (-τ) = xiRealCharacter Xi u τ := by
  have h := centeredXi_conjugate Xi hXi u τ
  simpa [xiRealCharacter] using congrArg Complex.re h

theorem xiImag_odd_u (Xi : ℂ → ℂ)
    (hXi : XiFunctionDatum Xi) (u τ : ℝ) :
    xiImagCharacter Xi (-u) τ = -xiImagCharacter Xi u τ := by
  have h₁ := congrArg Complex.im (centeredXi_neg_neg Xi hXi u (-τ))
  have h₂ := congrArg Complex.im (centeredXi_conjugate Xi hXi u τ)
  have h₁' : xiImagCharacter Xi (-u) τ = xiImagCharacter Xi u (-τ) := by
    simpa [xiImagCharacter] using h₁
  have h₂' : xiImagCharacter Xi u (-τ) = -xiImagCharacter Xi u τ := by
    simpa [xiImagCharacter] using h₂
  exact h₁'.trans h₂'

theorem xiImag_odd_tau (Xi : ℂ → ℂ)
    (hXi : XiFunctionDatum Xi) (u τ : ℝ) :
    xiImagCharacter Xi u (-τ) = -xiImagCharacter Xi u τ := by
  have h := centeredXi_conjugate Xi hXi u τ
  have hi := congrArg Complex.im h
  simpa [xiImagCharacter] using hi

theorem xiImag_on_critical_line (Xi : ℂ → ℂ)
  (hXi : XiFunctionDatum Xi) (τ : ℝ) :
    xiImagCharacter Xi 0 τ = 0 := by
  have h := xiImag_odd_u Xi hXi 0 τ
  have h' : xiImagCharacter Xi 0 τ = -xiImagCharacter Xi 0 τ := by
    simpa using h
  linarith

theorem xiV4_character_packet (Xi : ℂ → ℂ)
    (hXi : XiFunctionDatum Xi) (u τ : ℝ) :
    xiRealCharacter Xi (-u) τ = xiRealCharacter Xi u τ ∧
    xiRealCharacter Xi u (-τ) = xiRealCharacter Xi u τ ∧
    xiImagCharacter Xi (-u) τ = -xiImagCharacter Xi u τ ∧
    xiImagCharacter Xi u (-τ) = -xiImagCharacter Xi u τ := by
  exact ⟨xiReal_even_u Xi hXi u τ,
    xiReal_even_tau Xi hXi u τ,
    xiImag_odd_u Xi hXi u τ,
    xiImag_odd_tau Xi hXi u τ⟩

end InfoGeometry.Arithmetic.RiemannXiV4CharacterBridge
