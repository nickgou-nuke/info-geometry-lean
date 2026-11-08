import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Dynamics.SouriauDiracHodge

/-!
# Common-generator algebra

This is the finite algebraic core of a shared radial/phase generator.  It
records only a ring-level commuting generator `H` and a square-minus-one phase
axis `K`.  No exponential convergence, positivity, adjointness, or physical
time interpretation is asserted here.
-/

namespace InfoGeometry.Canonical.CommonGeneratorKreinBridge

open InfoGeometry.Krein

noncomputable section

variable {A : Type*} [Ring A]

structure CommonGeneratorData (A : Type*) [Ring A] where
  H : A
  K : A
  K_sq : K * K = -1
  HK_comm : H * K = K * H

namespace CommonGeneratorData

variable (C : CommonGeneratorData A)

/-- The positive/radial generator readout. -/
def radialGenerator : A := C.H

/-- The `K`-rotated generator readout. -/
def phaseGenerator : A := -(C.K * C.H)

@[simp] theorem radialGenerator_eq : C.radialGenerator = C.H := rfl

@[simp] theorem phaseGenerator_eq : C.phaseGenerator = -(C.K * C.H) := rfl

theorem radial_phase_commute :
    C.radialGenerator * C.phaseGenerator =
      C.phaseGenerator * C.radialGenerator := by
  unfold radialGenerator phaseGenerator
  calc
    C.H * -(C.K * C.H) = -(C.H * C.K * C.H) := by noncomm_ring
    _ = -(C.K * C.H * C.H) := by rw [C.HK_comm]
    _ = -(C.K * C.H) * C.H := by noncomm_ring

theorem phaseGenerator_square :
    C.phaseGenerator * C.phaseGenerator = -(C.H * C.H) := by
  unfold phaseGenerator
  calc
    (-(C.K * C.H)) * (-(C.K * C.H)) =
        C.K * (C.H * C.K) * C.H := by noncomm_ring
    _ = C.K * (C.K * C.H) * C.H := by rw [C.HK_comm]
    _ = (C.K * C.K) * (C.H * C.H) := by noncomm_ring
    _ = -(C.H * C.H) := by rw [C.K_sq]; noncomm_ring

/-! ## Native real Hestenes specialization -/

noncomputable def ofKreinOperatorData
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [KreinSpace H]
    (D : InfoGeometry.Dynamics.SouriauDiracHodge.KreinOperatorData H)
    (H₀ : H →L[ℝ] H)
    (hHK : H₀ * D.K = D.K * H₀) :
    CommonGeneratorData (H →L[ℝ] H) :=
  { H := H₀
    K := D.K
    K_sq := D.K_sq
    HK_comm := hHK }

theorem ofKreinOperatorData_phaseGenerator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [KreinSpace H]
    (D : InfoGeometry.Dynamics.SouriauDiracHodge.KreinOperatorData H)
    (H₀ : H →L[ℝ] H)
    (hHK : H₀ * D.K = D.K * H₀) :
    (ofKreinOperatorData D H₀ hHK).phaseGenerator = -(D.K * H₀) := rfl

end CommonGeneratorData

end

end InfoGeometry.Canonical.CommonGeneratorKreinBridge
