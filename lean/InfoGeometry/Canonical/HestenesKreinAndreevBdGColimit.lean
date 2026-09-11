import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.CenteredXiTwinKernel
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.HestenesKreinConnesAbsorptionColimit
import InfoGeometry.Canonical.HestenesKreinResolventColimit
import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.Physics.FermionicAndreevReflection

/-!
# Andreev/BdG readouts on the Hestenes--Krein colimit

This owner records the finite algebraic content of the Andreev/Bogoliubov--de
Gennes analogy: a doubled particle--hole block, its swap symmetry and trace
zero, the finite four-step Andreev loop, and compatible real readouts on a
Hestenes--Krein cone.

The identification of Andreev bound states with Riemann zeros, a BdG spectral
theorem, a superconducting gap theorem, and the Riemann Hypothesis remain
explicit analytic targets rather than conclusions of this file.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinAndreevBdGColimit

open InfoGeometry.Arithmetic.CenteredXiTwinKernel
open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.HestenesKreinConnesAbsorptionColimit
open InfoGeometry.Canonical.HestenesKreinResolventColimit
open InfoGeometry.Krein
open InfoGeometry.Physics
open InfoGeometry.Physics.FermionicAndreevReflection
open scoped BigOperators

/-! ## Finite particle--hole block algebra -/

def particleHoleSwap : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

def bdgHamiltonian (h pairing : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![h, pairing; -pairing, -h]

theorem bdgHamiltonian_trace_zero (h pairing : ℝ) :
    Matrix.trace (bdgHamiltonian h pairing) = 0 := by
  simp [bdgHamiltonian, Matrix.trace, Fin.sum_univ_two]

theorem bdg_particleHole_symmetry (h pairing : ℝ) :
    particleHoleSwap * bdgHamiltonian h pairing * particleHoleSwap =
      -bdgHamiltonian h pairing := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [particleHoleSwap, bdgHamiltonian, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem particleHoleSwap_sq :
    particleHoleSwap * particleHoleSwap =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [particleHoleSwap, Matrix.mul_apply, Fin.sum_univ_two]

/-! The native chiral block carrier supplies the reusable spectral-triple
shadow for the off-diagonal particle--hole block. -/

theorem native_chiral_block_readout (Delta : ℝ) :
    (chiralGrading * chiralGrading =
        (1 : BdGBlock ℝ)) ∧
    (bdgStar (diracOperator Delta) = diracOperator Delta) ∧
    (diracOperator Delta * chiralGrading +
        chiralGrading * diracOperator Delta = (0 : BdGBlock ℝ)) := by
  exact ⟨chiralGrading_sq, dirac_self_adjoint Delta,
    dirac_anticommutes_with_chirality Delta⟩

/-! ## Finite paired cosine mode -/

def pairedPrimeMode (t y : ℝ) : ℝ :=
  twinEven t y

theorem pairedPrimeMode_eq_two_cos (t y : ℝ) :
    pairedPrimeMode t y = 2 * Real.cos (t * y) := by
  exact twinEven_eq_two_cos t y

/-! ## A theorem-safe ABS/nodal interface -/

theorem andreevBoundState_iff_cosineNode
    (Xi : ℝ → ℝ) (Phi : ℝ → ℝ)
    (hrepresentation : ∀ t, Xi t =
      2 * ∫ y : ℝ, Phi y * Real.cos (t * y))
    (γ : ℝ) :
    Xi γ = 0 ↔ cosineNode Phi γ := by
  exact (cosineNode_iff_representation_zero Xi Phi hrepresentation γ).symm

/-! ## Functional reflection / chiral sign readouts -/

def functionalReflection (s : ℂ) : ℂ := 1 - s

def chiralParityFlip (μ : ℝ) : ℝ := -μ

theorem functionalReflection_involutive (s : ℂ) :
    functionalReflection (functionalReflection s) = s := by
  unfold functionalReflection
  ring

theorem functionalReflection_preserves_cosineNode
    (Phi : ℝ → ℝ) (hXi : ∀ t, cosineTransform Phi t = cosineTransform Phi (-t))
    {γ : ℝ} (hnode : cosineNode Phi γ) :
    cosineNode Phi (-γ) := by
  unfold cosineNode at hnode ⊢
  rw [hXi (-γ)]
  simpa using hnode

/-! ## Compatible colimit readout -/

def stageAndreevReadout {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) : ℝ :=
  readout n x

def limitAndreevReadout {C : HestenesKreinCone}
    (readout : DoubledSpace C.LimitBase → ℝ)
    (x : DoubledSpace C.LimitBase) : ℝ :=
  readout x

theorem stageAndreevReadout_eq_limit
    {C : HestenesKreinCone}
    (stageReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitReadout : DoubledSpace C.LimitBase → ℝ)
    (hreadout : ∀ n x, stageReadout n x = limitReadout (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageAndreevReadout stageReadout n x =
      limitAndreevReadout limitReadout (C.ι n x) := by
  exact hreadout n x

theorem stageAndreevReadout_bondIterate
    {C : HestenesKreinCone}
    (stageReadout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hreadout : ∀ n m x,
      stageReadout (n + m)
          (C.toFilteredPhaseCone.bondIterate n m x) = stageReadout n x)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stageAndreevReadout stageReadout (n + m)
        (C.toFilteredPhaseCone.bondIterate n m x) =
      stageAndreevReadout stageReadout n x := by
  exact hreadout n m x

end InfoGeometry.Canonical.HestenesKreinAndreevBdGColimit

end noncomputable section
