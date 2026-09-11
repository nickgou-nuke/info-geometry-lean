import InfoGeometry.Canonical.Cl55WittLieRouting
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55ThreeColorWittChannels

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.Cl55WittLieRouting

/-- The selected three-colour subspace of the five-mode Witt space.

This is only the canonical inclusion `Fin 3 ↪ Fin 5`; it does not assert an
identification with a split-octonionic circular basis. -/
def colorToCl55Index (i : Fin 3) : Fin 5 :=
  ⟨i.val, by omega⟩

def GammaPlus (i : Fin 3) : MatStage 5 :=
  creation (colorToCl55Index i)

def GammaMinus (i : Fin 3) : MatStage 5 :=
  annihilation (colorToCl55Index i)

@[simp] theorem GammaPlus_sq (i : Fin 3) :
    GammaPlus i * GammaPlus i = 0 := by
  exact creation_same_site_sq (colorToCl55Index i)

@[simp] theorem GammaMinus_sq (i : Fin 3) :
    GammaMinus i * GammaMinus i = 0 := by
  exact annihilation_same_site_sq (colorToCl55Index i)

theorem colorToCl55Index_injective : Function.Injective colorToCl55Index := by
  intro i j h
  apply Fin.ext
  simpa [colorToCl55Index] using congrArg Fin.val h

theorem Gamma_anticomm_metric_readout (i j : Fin 3) :
    GammaPlus i * GammaMinus j + GammaMinus j * GammaPlus i =
      if i = j then (1 : MatStage 5) else 0 := by
  dsimp [GammaPlus, GammaMinus]
  by_cases h : i = j
  · subst j
    simpa using creation_annihilation_anticomm (colorToCl55Index i)
      (colorToCl55Index i)
  · have h' : colorToCl55Index i ≠ colorToCl55Index j := by
      intro hij
      exact h (colorToCl55Index_injective hij)
    simpa [h, h'] using creation_annihilation_anticomm
      (colorToCl55Index i) (colorToCl55Index j)

theorem GammaPlus_commutator_bivector_readout (i j : Fin 3) :
    bracket (GammaPlus i) (GammaPlus j) =
      (2 : ℝ) • (GammaPlus i * GammaPlus j) := by
  dsimp [GammaPlus]
  exact creation_bracket_real (colorToCl55Index i) (colorToCl55Index j)

theorem GammaMinus_commutator_bivector_readout (i j : Fin 3) :
    bracket (GammaMinus i) (GammaMinus j) =
      (2 : ℝ) • (GammaMinus i * GammaMinus j) := by
  dsimp [GammaMinus]
  exact annihilation_bracket_real (colorToCl55Index i) (colorToCl55Index j)

theorem Gamma_mixed_commutator_grade_zero_readout (i j : Fin 3) :
    bracket (GammaPlus i) (GammaMinus j) =
      (2 : ℝ) • E (colorToCl55Index i) (colorToCl55Index j) := by
  dsimp [GammaPlus, GammaMinus]
  exact creation_annihilation_bracket_real
    (colorToCl55Index i) (colorToCl55Index j)

theorem GammaPlus_commutator_mem_wittPosTwo (i j : Fin 3) :
    bracket (GammaPlus i) (GammaPlus j) ∈ wittPosTwo := by
  dsimp [GammaPlus, wittPosOne]
  exact wittPosOne_bracket_mem_wittPosTwo
    (Submodule.subset_span (Set.mem_range_self (colorToCl55Index i)))
    (Submodule.subset_span (Set.mem_range_self (colorToCl55Index j)))

theorem GammaMinus_commutator_mem_wittNegTwo (i j : Fin 3) :
    bracket (GammaMinus i) (GammaMinus j) ∈ wittNegTwo := by
  dsimp [GammaMinus, wittNegOne]
  exact wittNegOne_bracket_mem_wittNegTwo
    (Submodule.subset_span (Set.mem_range_self (colorToCl55Index i)))
    (Submodule.subset_span (Set.mem_range_self (colorToCl55Index j)))

theorem Gamma_mixed_commutator_mem_wittZero (i j : Fin 3) :
    bracket (GammaPlus i) (GammaMinus j) ∈ wittZero := by
  dsimp [GammaPlus, GammaMinus, wittPosOne, wittNegOne]
  exact wittPosOne_bracket_mem_wittZero
    (Submodule.subset_span (Set.mem_range_self (colorToCl55Index i)))
    (Submodule.subset_span (Set.mem_range_self (colorToCl55Index j)))

end InfoGeometry.Canonical.Cl55ThreeColorWittChannels
