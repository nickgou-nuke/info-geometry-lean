import Mathlib.Tactic

/-!
# Golden spectral triple

An abstract Hilbert-space interface for finite golden q-CCR data.  The
Dirac/number-operator commutator consequence `[D,a†]=a†` is proved from the
commutator field alone.
-/

noncomputable section

namespace GoldenSpectralTriple

/-- Golden ratio. -/
def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- Golden q parameter. -/
def qPenrose : ℝ := phi⁻¹

/-- The Penrose parameter is the inverse golden ratio. -/
lemma qPenrose_mul_phi : qPenrose * phi = 1 := by
  have hphi_ne : phi ≠ 0 := by
    rw [phi]
    positivity
  rw [qPenrose]
  exact inv_mul_cancel₀ hphi_ne

/-- Abstract golden/Fibonacci Fock space data. -/
structure GoldenFockSpace (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Ngen : ℕ) where
  Ω : H
  vac_norm : ‖Ω‖ = 1
  create : Fin Ngen → H →L[ℂ] H
  inner_one_particle : ∀ i j : Fin Ngen,
    inner ℂ (create i Ω) (create j Ω) = if i = j then (1 : ℂ) else 0

/-- Dirac/number operator data.  The commutator says creating one tile/anyon
raises the inflation depth by exactly one. -/
structure GoldenDiracOperator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Ngen : ℕ} (F : GoldenFockSpace H Ngen) where
  D : H →L[ℂ] H
  vac_eigen : D F.Ω = 0
  commutator_create : ∀ i : Fin Ngen,
    D ∘L (F.create i) - (F.create i) ∘L D = F.create i

/-- First-particle metric consequence: `a†Ω` is a Dirac eigenvector with
eigenvalue `1`. -/
theorem dirac_creates_particle_metric {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {Ngen : ℕ}
    (F : GoldenFockSpace H Ngen) (Dirac : GoldenDiracOperator F) (i : Fin Ngen) :
    Dirac.D (F.create i F.Ω) = F.create i F.Ω := by
  have h := congrArg (fun T : H →L[ℂ] H => T F.Ω) (Dirac.commutator_create i)
  simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    Dirac.vac_eigen] at h
  simpa using h

end GoldenSpectralTriple
