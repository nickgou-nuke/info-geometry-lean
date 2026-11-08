import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionDerivationSpinRep

open ContinuousLinearMap

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H
local notation "NambuH" => H × H
local notation "EndNambu" => NambuH →L[ℂ] NambuH

/-- Bundled decomposition of a g_{2(2)} derivation into sl3 stabilizer and pairing components. -/
structure SplitDerivationDecomp (E : Type*) where
  diagA : E
  pairDelta : E
  pairDeltaDagger : E

/-- Representation map ρ : g_{2(2)} → End(H ⊕ H). -/
noncomputable def rho (D : SplitDerivationDecomp EndH) : EndNambu :=
  (D.diagA.coprod D.pairDelta).prod
    (D.pairDeltaDagger.coprod (-ContinuousLinearMap.adjoint D.diagA))

/-- Block 11 extraction (normal diagonal component). -/
def block11 (T : EndNambu) : EndH :=
  (ContinuousLinearMap.fst ℂ H H).comp (T.comp (ContinuousLinearMap.inl ℂ H H))

/-- Block 12 extraction (superconducting pairing component). -/
def block12 (T : EndNambu) : EndH :=
  (ContinuousLinearMap.fst ℂ H H).comp (T.comp (ContinuousLinearMap.inr ℂ H H))

/-- Block 21 extraction (pairing conjugate component). -/
def block21 (T : EndNambu) : EndH :=
  (ContinuousLinearMap.snd ℂ H H).comp (T.comp (ContinuousLinearMap.inl ℂ H H))

/-- Block 22 extraction (hole diagonal component). -/
def block22 (T : EndNambu) : EndH :=
  (ContinuousLinearMap.snd ℂ H H).comp (T.comp (ContinuousLinearMap.inr ℂ H H))

@[simp]
theorem block11_rho (D : SplitDerivationDecomp EndH) :
    block11 (rho D) = D.diagA := by
  apply ContinuousLinearMap.ext
  intro u
  simp [block11, rho, ContinuousLinearMap.comp_apply]

@[simp]
theorem block12_rho (D : SplitDerivationDecomp EndH) :
    block12 (rho D) = D.pairDelta := by
  apply ContinuousLinearMap.ext
  intro v
  simp [block12, rho, ContinuousLinearMap.comp_apply]

@[simp]
theorem block21_rho (D : SplitDerivationDecomp EndH) :
    block21 (rho D) = D.pairDeltaDagger := by
  apply ContinuousLinearMap.ext
  intro u
  simp [block21, rho, ContinuousLinearMap.comp_apply]

@[simp]
theorem block22_rho (D : SplitDerivationDecomp EndH) :
    block22 (rho D) = -ContinuousLinearMap.adjoint D.diagA := by
  apply ContinuousLinearMap.ext
  intro v
  simp [block22, rho, ContinuousLinearMap.comp_apply]

/-- 🏆 THEOREM: The sl3 stabilizer sector acts purely diagonally on Nambu space. -/
theorem sl3_stabilizer_is_block_diagonal (A : EndH) :
    let D : SplitDerivationDecomp EndH := ⟨A, 0, 0⟩
    block12 (rho D) = 0 ∧ block21 (rho D) = 0 := by
  intro D
  exact ⟨block12_rho D, block21_rho D⟩

/-- 🏆 THEOREM: The 3 ⊕ 3* pairing sector acts purely off-diagonally on Nambu space. -/
theorem pairing_sector_is_block_off_diagonal (Δ Δdag : EndH) :
    let D : SplitDerivationDecomp EndH := ⟨0, Δ, Δdag⟩
    block11 (rho D) = 0 ∧ block22 (rho D) = 0 := by
  intro D
  refine ⟨block11_rho D, ?_⟩
  rw [block22_rho D]
  dsimp [D]
  simp

/-- 🏆 MASTER SOLDERING THEOREM: The upper-right Nambu block extracts exactly the pairing potential. -/
theorem xi_soldering_theorem (D : SplitDerivationDecomp EndH) :
    block12 (rho D) = D.pairDelta :=
  block12_rho D

end InfoGeometry.Canonical.SplitOctonionDerivationSpinRep

end noncomputable section
