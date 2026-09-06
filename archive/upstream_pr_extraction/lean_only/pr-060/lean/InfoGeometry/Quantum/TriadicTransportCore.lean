import InfoGeometry.Quantum.CliffordDictionary
import InfoGeometry.Projective.Rays

/-!
# InfoGeometry.Quantum.TriadicTransportCore

Abstract grammar for a triadic transport system (Probe, Address, Content) 
on a doubled real carrier. This module formalizes the roles and the 
abstract update operator without assuming a specific physical realization 
(like a surprisal barycenter).

## Theoretical Roles
- **Probe** (Q): The selection/query channel.
- **Addr** (A): The addressable key channel.
- **Content** (V): The transported value channel.

These roles are defined as projections on the carrier space $H$.
-/

namespace InfoGeometry.Quantum.TriadicTransport

open InfoGeometry.Krein
open InfoGeometry.Projective

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- 
**Triadic Transport Data**:
Abstract bundle for the triadic roles and the transport update operator.
-/
structure TriadicTransportData (ι : Type*) where
  /-- Probe (Query) projector. -/
  Probe_proj : H₂ →L[ℝ] H₂
  /-- Addressable (Key) projector. -/
  Addr_proj : H₂ →L[ℝ] H₂
  /-- Content (Value) projector (optional, can be Identity). -/
  Content_proj : H₂ →L[ℝ] H₂
  
  -- Projector Axioms
  Probe_sq : Probe_proj.comp Probe_proj = Probe_proj
  Addr_sq : Addr_proj.comp Addr_proj = Addr_proj
  Content_sq : Content_proj.comp Content_proj = Content_proj
  
  -- Complementarity (Optional, but often intended for Q/A)
  Probe_Addr_disjoint : Probe_proj.comp Addr_proj = 0
  Addr_Probe_disjoint : Addr_proj.comp Probe_proj = 0

  /-- 
  **Abstract Update Operator**:
  A family of weights and contents mapped to an output carrier.
  Weights are primary (counts/functionals), not necessarily normalized.
  -/
  Update : (ι → ℝ) → (ι → H₂) → H₂

  -- Axioms of Homogeneity
  
  /-- 
  **Weight Homogeneity**: 
  Rescaling the entire weight family by a positive constant 
  preserves the output ray in $P(H)$.
  -/
  Update_weight_hom : ∀ (c : ℝ) (_hc : c > 0) (w : ι → ℝ) (v : ι → H₂),
    same_ray (E := E) (Update (fun i => c * w i) v) (Update w v)

  /-- 
  **Content Homogeneity**: 
  Rescaling the content family linearly (or via Weyl action) 
  scales the output vector linearly.
  -/
  Update_content_hom : ∀ (c : ℝ) (w : ι → ℝ) (v : ι → H₂),
    Update w (fun i => c • v i) = c • Update w v

namespace TriadicTransportData

variable {ι : Type*} (data : TriadicTransportData (E := E) ι)

/-- 
**Admissibility Condition**:
A weight/content pair is admissible if the update result is nonzero. 
This is required for descent to the projective ray space.
-/
def IsAdmissible (w : ι → ℝ) (v : ι → H₂) : Prop :=
  data.Update w v ≠ 0

end TriadicTransportData

end InfoGeometry.Quantum.TriadicTransport
