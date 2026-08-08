import InfoGeometry.Topology.CuntzCantorSpectralTriple

/-!
# Operator-valued Connes spectral distance on the native Cuntz carrier

This module is an operator-level bridge over the existing
`CuntzCantorSpectralTriple`.  It deliberately does not introduce a second
spectral-triple carrier: the Dirac operator, represented action, cylinder
operators, and property commutators are taken from the native owner.

The distance predicate is stated on the represented cylinder observables.  It
therefore retains the continuous-operator norm
`‖[D, π(a)]‖`, while leaving positivity, completeness, and the full state-space
supremum to later C*-algebraic owners.
-/

noncomputable section

namespace InfoGeometry.Physics.Noncommutative

open InfoGeometry.Topology

variable {Op H : Type*} [Ring Op] [StarRing Op]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [MulAction ℂ H] [SMul Op H]

/-- The represented Connes differential `[D, π(a)]` on the native operator lane. -/
def representedDifferential
    (T : CuntzCantorSpectralTriple Op H) (a : Op) : H →L[ℂ] H :=
  T.dirac.comp (T.representedAction a) -
    (T.representedAction a).comp T.dirac

/-- The property differential of a finite Cuntz cylinder observable. -/
def cylinderDifferential
    (T : CuntzCantorSpectralTriple Op H)
    (n : Nat) (word : BinaryCylinder n) : H →L[ℂ] H :=
  T.boundedCommutatorWitness n word

@[simp] theorem cylinderDifferential_eq_representedDifferential
    (T : CuntzCantorSpectralTriple Op H)
    (n : Nat) (word : BinaryCylinder n) :
    cylinderDifferential T n word =
      representedDifferential T (T.cylinderRepresentation n word) :=
  T.boundedCommutatorCertified n word

/-- A cylinder observable is Dirac-Lipschitz when its operator differential has
operator norm at most one. -/
def isCylinderDiracLipschitz
    (T : CuntzCantorSpectralTriple Op H)
    (n : Nat) (word : BinaryCylinder n) : Prop :=
  ‖cylinderDifferential T n word‖ ≤ 1

/-- A finite-cylinder version of the Connes state-distance bound. -/
def cylinderStateDistanceBound
    (T : CuntzCantorSpectralTriple Op H)
    (μ ν : Op → ℝ) (d : ℝ) : Prop :=
  (∀ (n : Nat) (word : BinaryCylinder n),
    isCylinderDiracLipschitz T n word →
      |μ (T.cylinderRepresentation n word) -
        ν (T.cylinderRepresentation n word)| ≤ d) ∧
    0 ≤ d

theorem cylinderStateDistanceBound_symmetry
    (T : CuntzCantorSpectralTriple Op H) (μ ν : Op → ℝ) (d : ℝ)
    (h : cylinderStateDistanceBound T μ ν d) :
    cylinderStateDistanceBound T ν μ d := by
  refine ⟨?_, h.2⟩
  intro n word hLip
  simpa [abs_sub_comm] using h.1 n word hLip

theorem cylinderStateDistanceBound_triangle
    (T : CuntzCantorSpectralTriple Op H)
    (μ ν ρ : Op → ℝ) (d₁ d₂ : ℝ)
    (h₁ : cylinderStateDistanceBound T μ ν d₁)
    (h₂ : cylinderStateDistanceBound T ν ρ d₂) :
    cylinderStateDistanceBound T μ ρ (d₁ + d₂) := by
  refine ⟨?_, by linarith [h₁.2, h₂.2]⟩
  intro n word hLip
  have htri := abs_sub_le
    (μ (T.cylinderRepresentation n word))
    (ν (T.cylinderRepresentation n word))
    (ρ (T.cylinderRepresentation n word))
  linarith [h₁.1 n word hLip, h₂.1 n word hLip]

theorem cylinderStateDistanceBound_self
    (T : CuntzCantorSpectralTriple Op H) (μ : Op → ℝ) :
    cylinderStateDistanceBound T μ μ 0 := by
  refine ⟨?_, le_rfl⟩
  intro n word hLip
  simp

theorem representedDifferential_leibniz_on_cylinder
    (T : CuntzCantorSpectralTriple Op H)
    (n : Nat) (word : BinaryCylinder n) :
    cylinderDifferential T n word =
      T.dirac.comp (T.representedAction (T.cylinderRepresentation n word)) -
        (T.representedAction (T.cylinderRepresentation n word)).comp T.dirac := by
  exact T.boundedCommutatorCertified n word

theorem connes_wasserstein_operator_synthesis
    (T : CuntzCantorSpectralTriple Op H)
    (μ ν ρ : Op → ℝ) (d₁ d₂ : ℝ)
    (h₁ : cylinderStateDistanceBound T μ ν d₁)
    (h₂ : cylinderStateDistanceBound T ν ρ d₂) :
    cylinderStateDistanceBound T ν μ d₁ ∧
      cylinderStateDistanceBound T μ ρ (d₁ + d₂) ∧
      cylinderStateDistanceBound T μ μ 0 := by
  exact ⟨cylinderStateDistanceBound_symmetry T μ ν d₁ h₁,
    cylinderStateDistanceBound_triangle T μ ν ρ d₁ d₂ h₁ h₂,
    cylinderStateDistanceBound_self T μ⟩

end InfoGeometry.Physics.Noncommutative
