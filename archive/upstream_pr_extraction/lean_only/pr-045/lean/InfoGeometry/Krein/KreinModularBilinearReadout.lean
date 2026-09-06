import InfoGeometry.Krein.LiouvilleanDynamics
import InfoGeometry.Krein.InvolutiveSelfDualCarrier

/-!
# Krein modular bilinear readout

This owner records the invariant bilinear kernel supplied by the native Krein
space structure. It is deliberately not a metric: the fundamental symmetry
may make the kernel indefinite, and no positivity or separation is assumed.
-/

namespace InfoGeometry.Krein

open KreinSpace

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H]

/-- The involution-compatible Krein bilinear kernel induced by the native
fundamental symmetry. This is a kernel/readout, not a distance. -/
noncomputable def KreinBilinearKernel (u v : H) : ℝ :=
  kreinInner u v

@[simp] theorem KreinBilinearKernel_apply (u v : H) :
    KreinBilinearKernel u v = kreinInner u v :=
  rfl

theorem continuous_KreinBilinearKernel :
    Continuous (fun p : H × H => KreinBilinearKernel p.1 p.2) := by
  simpa [KreinBilinearKernel, kreinInner_def] using
    continuous_inner.comp
      (((KreinSpace.J (H := H)).continuous.comp continuous_fst).prodMk
        continuous_snd)

/-- The modular orbit readout of the Krein bilinear kernel. -/
noncomputable def modularKreinBilinearKernel
    (G : KreinSkewGenerator (H := H)) (t : ℝ) (u v : H) : ℝ :=
  KreinBilinearKernel (G.modularFlow.flow t u) (G.modularFlow.flow t v)

theorem modularKreinBilinearKernel_invariant
    (G : KreinSkewGenerator (H := H)) (t : ℝ) (u v : H) :
    modularKreinBilinearKernel G t u v = KreinBilinearKernel u v := by
  exact G.flow_isKreinIsometry t u v

theorem modularKreinBilinearKernel_invariant_eq
    (G : KreinSkewGenerator (H := H)) (t : ℝ) :
    (fun u v => modularKreinBilinearKernel G t u v) =
      fun u v => KreinBilinearKernel u v := by
  funext u v
  exact modularKreinBilinearKernel_invariant G t u v

theorem modularKreinQuadraticReadout_invariant
    (G : KreinSkewGenerator (H := H)) (t : ℝ) (u : H) :
    modularKreinBilinearKernel G t u u = KreinBilinearKernel u u := by
  exact modularKreinBilinearKernel_invariant G t u u

section InvolutiveSelfDual

/-- Explicit compatibility between an involutive self-dual pairing and the
native Krein bilinear kernel. The equality is a bridge datum, not inferred
from the two structures merely sharing a Hilbert carrier. -/
structure InvolutiveSelfDualKreinBridge
    (X : InvolutiveSelfDualCarrier) [KreinSpace X.H] where
  pairing_eq_krein : ∀ u v, X.kreinPairing u v = kreinInner u v

theorem modularPairing_invariant
    (X : InvolutiveSelfDualCarrier) [KreinSpace X.H]
    (B : InvolutiveSelfDualKreinBridge X)
    (G : KreinSkewGenerator (H := X.H)) (t : ℝ) (u v : X.H) :
    X.kreinPairing (G.modularFlow.flow t u) (G.modularFlow.flow t v) =
      X.kreinPairing u v := by
  rw [B.pairing_eq_krein, B.pairing_eq_krein]
  exact G.flow_isKreinIsometry t u v

end InvolutiveSelfDual

end InfoGeometry.Krein
