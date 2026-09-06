import Mathlib.Tactic
import InfoGeometry.Canonical.FilteredHestenesKreinColimit

/-!
# Bregman readouts on the Hestenes--Krein colimit

This owner translates the scalar readout behind the operatorial
Souriau/Bregman interface.  Potential, gradient, and pairing compatibility are
explicit finite-stage premises.  It does not identify the readouts with a
zeta potential or prove a global Legendre theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinBregmanColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Krein

def stageBregman
    {C : HestenesKreinCone}
    (potential : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (gradient : ∀ n, DoubledSpace (C.Base n) → DoubledSpace (C.Base n))
    (pairing : ∀ n, DoubledSpace (C.Base n) → DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x y : DoubledSpace (C.Base n)) : ℝ :=
  potential n x - potential n y - pairing n (gradient n y) (x - y)

def limitBregman
    {C : HestenesKreinCone}
    (potential : DoubledSpace C.LimitBase → ℝ)
    (gradient : DoubledSpace C.LimitBase → DoubledSpace C.LimitBase)
    (pairing : DoubledSpace C.LimitBase → DoubledSpace C.LimitBase → ℝ)
    (x y : DoubledSpace C.LimitBase) : ℝ :=
  potential x - potential y - pairing (gradient y) (x - y)

theorem stageBregman_eq_limitBregman
    {C : HestenesKreinCone}
    (potential : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (gradient : ∀ n, DoubledSpace (C.Base n) → DoubledSpace (C.Base n))
    (pairing : ∀ n, DoubledSpace (C.Base n) → DoubledSpace (C.Base n) → ℝ)
    (limitPotential : DoubledSpace C.LimitBase → ℝ)
    (limitGradient : DoubledSpace C.LimitBase → DoubledSpace C.LimitBase)
    (limitPairing : DoubledSpace C.LimitBase → DoubledSpace C.LimitBase → ℝ)
    (hpotential : ∀ n z, potential n z = limitPotential (C.ι n z))
    (hgradient : ∀ n z, C.ι n (gradient n z) = limitGradient (C.ι n z))
    (hpairing : ∀ n u v,
      pairing n u v = limitPairing (C.ι n u) (C.ι n v))
    (n : ℕ) (x y : DoubledSpace (C.Base n)) :
    stageBregman potential gradient pairing n x y =
      limitBregman limitPotential limitGradient limitPairing (C.ι n x) (C.ι n y) := by
  unfold stageBregman limitBregman
  rw [hpotential n x, hpotential n y]
  have hsub : C.ι n (x - y) = C.ι n x - C.ι n y := by
    exact (C.ι n).map_sub x y
  rw [hpairing n (gradient n y) (x - y), hgradient n y, ← hsub]

theorem stageBregman_self
    {C : HestenesKreinCone}
    (potential : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (gradient : ∀ n, DoubledSpace (C.Base n) → DoubledSpace (C.Base n))
    (pairing : ∀ n, DoubledSpace (C.Base n) → DoubledSpace (C.Base n) → ℝ)
    (hzero : ∀ n z, pairing n z 0 = 0)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageBregman potential gradient pairing n x x = 0 := by
  unfold stageBregman
  simp only [sub_self]
  rw [hzero]
  ring

theorem limitBregman_self
    {C : HestenesKreinCone}
    (potential : DoubledSpace C.LimitBase → ℝ)
    (gradient : DoubledSpace C.LimitBase → DoubledSpace C.LimitBase)
    (pairing : DoubledSpace C.LimitBase → DoubledSpace C.LimitBase → ℝ)
    (hzero : ∀ z, pairing z 0 = 0)
    (x : DoubledSpace C.LimitBase) :
    limitBregman potential gradient pairing x x = 0 := by
  unfold limitBregman
  simp only [sub_self]
  rw [hzero]
  ring

end InfoGeometry.Canonical.HestenesKreinBregmanColimit

end noncomputable section
