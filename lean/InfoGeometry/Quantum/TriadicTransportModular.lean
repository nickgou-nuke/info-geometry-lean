import InfoGeometry.Quantum.TriadicTransportCore
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Quantum.TriadicTransport

open InfoGeometry.Krein

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*}

local notation "H₂" => DoubledSpace E

noncomputable def modularKreinScore (q a : H₂) : ℝ :=
  KreinSpace.kreinInner (H := H₂) q a

noncomputable def exponentialWeight (q a : H₂) : ℝ :=
  Real.exp (modularKreinScore q a)

structure ExponentialModularTransport (ι : Type*) extends TriadicTransportData (E := E) ι where
  queries : ι → H₂
  keys : ι → H₂

theorem modular_softMax_consistency (data : ExponentialModularTransport (E := E) ι) :
    ∀ (c : ℝ) (_hc : c > 0) (v : ι → H₂),
      let w_mod := fun i => exponentialWeight (data.queries i) (data.keys i)
      InfoGeometry.Projective.same_ray (data.Update (fun i => c * w_mod i) v) (data.Update w_mod v) := by
  intro c hc v
  exact data.Update_weight_hom c hc (fun i => exponentialWeight (data.queries i) (data.keys i)) v

end InfoGeometry.Quantum.TriadicTransport
