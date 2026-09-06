import InfoGeometry.Quantum.GeometricTensorSplitOctonionChiralFrame

/-!
# Polarized vielbein transport for the split-octonion frame

This owner contains the generic conjugation argument used by a transported
polarization.  The inverse-flow law is an explicit field, so the result is a
theorem rather than an axiom about an unspecified propagator.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Quantum.ChiralSplitOctonionDerivationVielbein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

local notation "EndE" => E →L[ℝ] E

structure MovingPolarization where
  U : ℝ → EndE
  Uinv : ℝ → EndE
  leftInverse : ∀ t, (Uinv t).comp (U t) = ContinuousLinearMap.id ℝ E
  P0 : EndE
  Pt : ℝ → EndE
  def_Pt : ∀ t, Pt t = (U t).comp ((P0.comp (Uinv t)))

def FPlus (pol : MovingPolarization (E := E))
    (F₀ : EndE) (t : ℝ) : EndE := pol.U t |>.comp F₀

def FMinus (pol : MovingPolarization (E := E))
    (F₀ : EndE) (t : ℝ) : EndE := pol.U t |>.comp F₀

theorem transportedPlus_mem_plus
    (pol : MovingPolarization (E := E)) (F₀ : EndE) (t : ℝ) (u : E)
    (h_ref : pol.P0 (F₀ u) = F₀ u) :
    pol.Pt t ((FPlus pol F₀ t) u) = (FPlus pol F₀ t) u := by
  rw [pol.def_Pt]
  change pol.U t (pol.P0 (pol.Uinv t (pol.U t (F₀ u)))) =
    pol.U t (F₀ u)
  have h_inv := congrArg (fun f : EndE => f (F₀ u)) (pol.leftInverse t)
  dsimp at h_inv
  rw [h_inv]
  rw [h_ref]

theorem transportedMinus_mem_minus
    (pol : MovingPolarization (E := E)) (F₀ : EndE) (t : ℝ) (u : E)
    (h_ref : pol.P0 (F₀ u) = -(F₀ u)) :
    pol.Pt t ((FMinus pol F₀ t) u) = -(FMinus pol F₀ t) u := by
  rw [pol.def_Pt]
  change pol.U t (pol.P0 (pol.Uinv t (pol.U t (F₀ u)))) =
    -pol.U t (F₀ u)
  have h_inv := congrArg (fun f : EndE => f (F₀ u)) (pol.leftInverse t)
  dsimp at h_inv
  rw [h_inv, h_ref]
  simp

end InfoGeometry.Quantum.ChiralSplitOctonionDerivationVielbein
