import InfoGeometry.Canonical.ChiralRGFlow
import InfoGeometry.Canonical.GaugeGroups

/-!
# InfoGeometry.Canonical.YangMillsBridge

Bridge-layer contracts linking the existing chiral RG flow scaffold to
Yang-Mills mass-gap obligations.
-/

namespace InfoGeometry.Canonical.YangMillsBridge

open InfoGeometry.Canonical.ChiralRGFlow
open InfoGeometry.Canonical.GaugeGroups

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Minimal `SU(N)` gauge instantiation contract.
Updated to use the formal group structures from the hierarchy layer.
-/
structure SUNGaugeInstantiation where
  /-- Color rank parameter. -/
  n : ℕ
  /-- Nontrivial gauge rank (`N ≥ 2`). -/
  n_ge_two : 2 ≤ n
  /-- Formal SU(N) group model contract. -/
  su_model : SUN n
  /-- Formal PSU(N) projective group model contract. -/
  psu_model : PSUN n su_model
  /-- Marker that this carrier models an `SU(N)` gauge sector. -/
  is_su_model : Prop
  /-- Witness that the `SU(N)` marker holds for this instantiation. -/
  is_su_model_holds : is_su_model

/-- Existence-layer obligations matching the constructive QFT side. -/
structure QFTAxiomsLayer where
  /-- Reflection positivity witness. -/
  has_reflection_positivity : Prop
  /-- Proof of reflection positivity. -/
  reflection_positivity_holds : has_reflection_positivity
  /-- Osterwalder-Schrader axioms witness. -/
  has_osterwalder_schrader : Prop
  /-- Proof of the Osterwalder-Schrader layer. -/
  osterwalder_schrader_holds : has_osterwalder_schrader
  /-- Wightman reconstruction witness. -/
  has_wightman_reconstruction : Prop
  /-- Proof of Wightman reconstruction availability. -/
  wightman_reconstruction_holds : has_wightman_reconstruction

/-- Consolidated bridge package from chiral RG to Yang-Mills mass-gap targets. -/
structure YangMillsMassGapBridge (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] where
  /-- Gauge-theory instantiation data. -/
  su_inst : SUNGaugeInstantiation
  /-- Chiral RG model currently available in the canonical layer. -/
  rg_model : ChiralAsymptoticModel E
  /-- Constructive QFT existence obligations. -/
  qft_layer : QFTAxiomsLayer
  /-- Candidate strict spectral gap (`λ₁`). -/
  spectral_gap : ℝ
  /-- Strict positivity target for the mass gap. -/
  spectral_gap_pos : 0 < spectral_gap
  /-- Lower bound linking chiral scale to the spectral gap. -/
  gamma_le_spectral_gap : rg_model.gamma ≤ spectral_gap

/-- Obligation 1: explicit `SU(N)` gauge instantiation. -/
def has_su_n_instantiation (B : YangMillsMassGapBridge E) : Prop :=
  B.su_inst.is_su_model

/-- Obligation 2: existence layer via OS/Wightman-style witnesses. -/
def has_os_wightman_existence_layer (B : YangMillsMassGapBridge E) : Prop :=
  B.qft_layer.has_reflection_positivity ∧
    B.qft_layer.has_osterwalder_schrader ∧
    B.qft_layer.has_wightman_reconstruction

/-- Obligation 3: strict positive mass gap. -/
def has_strict_mass_gap (B : YangMillsMassGapBridge E) : Prop :=
  0 < B.spectral_gap

/-- The RG component of the bridge inherits asymptotic freedom. -/
lemma asymptotic_freedom_of_bridge_rg_model
    (B : YangMillsMassGapBridge E) :
    IsAsymptoticallyFree B.rg_model.flow :=
  asymptotic_freedom_of_negative_beta B.rg_model

/-- The bridge carries a strict mass-gap witness by construction. -/
lemma strict_mass_gap_of_bridge (B : YangMillsMassGapBridge E) :
    has_strict_mass_gap B :=
  B.spectral_gap_pos

/-- The bridge carries the chiral-to-gap lower bound witness. -/
lemma chiral_scale_bounds_mass_gap (B : YangMillsMassGapBridge E) :
    B.rg_model.gamma ≤ B.spectral_gap :=
  B.gamma_le_spectral_gap

/-- Consolidated milestone theorem for the three Yang-Mills obligations. -/
theorem millennium_obligations_of_bridge
    (B : YangMillsMassGapBridge E) :
    has_su_n_instantiation B ∧
      has_os_wightman_existence_layer B ∧
      has_strict_mass_gap B := by
  refine ⟨B.su_inst.is_su_model_holds, ?_, B.spectral_gap_pos⟩
  exact ⟨B.qft_layer.reflection_positivity_holds,
    B.qft_layer.osterwalder_schrader_holds,
    B.qft_layer.wightman_reconstruction_holds⟩

end InfoGeometry.Canonical.YangMillsBridge
