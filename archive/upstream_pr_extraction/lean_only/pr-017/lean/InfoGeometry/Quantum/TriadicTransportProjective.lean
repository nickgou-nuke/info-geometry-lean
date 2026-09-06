import InfoGeometry.Quantum.TriadicTransportCore
import InfoGeometry.Projective.Rays

namespace InfoGeometry.Quantum.TriadicTransport

open InfoGeometry.Krein
open InfoGeometry.Projective

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*}

local notation "H₂" => DoubledSpace E

theorem Update_weight_proj_stable
    [CompleteSpace E] (data : TriadicTransportData (E := E) ι)
    {w : ι → ℝ} {v : ι → H₂} (c : ℝ) (hc : c > 0) :
    projectivize (data.Update (fun i => c * w i) v) = projectivize (data.Update w v) := by
  apply Quotient.sound
  exact data.Update_weight_hom c hc w v

theorem Update_content_proj_stable
    [CompleteSpace E] (data : TriadicTransportData (E := E) ι)
    {w : ι → ℝ} {v : ι → H₂} (c : ℝ) (hc : c ≠ 0) :
    projectivize (data.Update w (fun i => c • v i)) = projectivize (data.Update w v) := by
  rw [data.Update_content_hom]
  simpa using projectivize_smul (E := E) (u := Units.mk0 c hc) (v := data.Update w v)

end InfoGeometry.Quantum.TriadicTransport
