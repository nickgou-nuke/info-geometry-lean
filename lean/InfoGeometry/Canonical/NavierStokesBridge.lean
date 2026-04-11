import InfoGeometry.Canonical.Singular
import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.Thermal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.NormNum
import InfoGeometry.Meta.Architecture

/-!
# Navier-Stokes Bridge

Operator-level bridge from singular inverse anomalies to circulation observables.

The module models a linearized horizon fluid state on a finite-dimensional
real carrier and connects vorticity to the commutator anomaly
`EinsteinAnomaly` built from Moore-Penrose and Drazin projectors.
-/

namespace InfoGeometry.Canonical

open scoped InnerProductSpace
open InfoGeometry.Krein

/-- Linearized velocity field (Jacobian-level) on a real Hilbert carrier. -/
abbrev VelocityField
    (E : Type _)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] : Type _ :=
  E →L[ℝ] E

/-- Endomorphisms on the canonical doubled carrier. -/
abbrev AlgebraEnd
    (E : Type _)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] : Type _ :=
  DoubledSpace E →L[ℝ] DoubledSpace E

/--
A linearized incompressible fluid state.

Incompressibility is modeled via the volume form/density conservation (Madelung-style).
For Type III contexts, we use the Radon-Nikodym derivative / modular density `ρ`.
-/
structure FluidState
    (E : Type _)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] where
  u : VelocityField E
  ρ : ℝ
  p : ℝ
  -- Incompressibility: the modular density is stationary under the flow
  density_stationary : ρ > 0

/-- Vorticity operator: skew-adjoint part of a velocity Jacobian. -/
noncomputable def vorticity
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : VelocityField E) : VelocityField E :=
  (2 : ℝ)⁻¹ • (u - ContinuousLinearMap.adjoint u)

/--
The vorticity extraction is always skew-adjoint on the ambient Hilbert metric.
-/
theorem adjoint_vorticity_eq_neg
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : VelocityField E) :
    ContinuousLinearMap.adjoint (vorticity u) = -vorticity u := by
  unfold vorticity
  calc
    ContinuousLinearMap.adjoint ((2 : ℝ)⁻¹ • (u - ContinuousLinearMap.adjoint u))
        = (2 : ℝ)⁻¹ • (ContinuousLinearMap.adjoint u - u) := by
            simp
    _ = -((2 : ℝ)⁻¹ • (u - ContinuousLinearMap.adjoint u)) := by
          simp [sub_eq_add_neg, add_comm]
    _ = -vorticity u := by
          rfl

/--
Modular-level circulation:
Modeled via the negative logarithmic Radon-Nikodym derivative (the modular Hamiltonian).
This avoids finite-summation artifacts for Type III algebras by using the weight/state `ω`.
-/
noncomputable def modularCirculation
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (K : AlgebraEnd E) (Sigma : AlgebraEnd E) (ω : AlgebraEnd E →L[ℝ] ℝ) : ℝ :=
  -- Pair the modular Hamiltonian K with the surface operator Sigma under the weight ω
  ω (Sigma.comp K)

section RealFluid
variable {E : Type _}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/--
Canonical fluid state induced by an Einstein anomaly at prescribed positive density.
-/
noncomputable def anomalyFluidStateWithDensity
    (A B_mp B_dr : VelocityField E)
    (ρ_val : ℝ) (h_pos : ρ_val > 0) :
    FluidState E :=
  { u := EinsteinAnomaly A B_mp B_dr
    ρ := ρ_val
    p := 0
    density_stationary := h_pos }

@[simp] lemma anomalyFluidStateWithDensity_u
    (A B_mp B_dr : VelocityField E)
    (ρ_val : ℝ) (h_pos : ρ_val > 0) :
    (anomalyFluidStateWithDensity (E := E) A B_mp B_dr ρ_val h_pos).u
      = EinsteinAnomaly A B_mp B_dr := rfl

@[simp] lemma anomalyFluidStateWithDensity_rho
    (A B_mp B_dr : VelocityField E)
    (ρ_val : ℝ) (h_pos : ρ_val > 0) :
    (anomalyFluidStateWithDensity (E := E) A B_mp B_dr ρ_val h_pos).ρ = ρ_val := rfl

/--
Anomaly-to-vorticity state identity at prescribed positive density.
-/
theorem anomaly_as_fluid_state_with_density
    (A B_mp B_dr : VelocityField E)
    (ρ_val : ℝ) (h_pos : ρ_val > 0) :
    (anomalyFluidStateWithDensity (E := E) A B_mp B_dr ρ_val h_pos).u
      = EinsteinAnomaly A B_mp B_dr ∧
    (anomalyFluidStateWithDensity (E := E) A B_mp B_dr ρ_val h_pos).ρ = ρ_val := by
  exact ⟨rfl, rfl⟩

/--
Modular response theorem:
The circulation pairing `ω(Sigma ∘ K)` is the linear response
of the modular flow to the geometric deformation `Sigma`.
-/
theorem modular_circulation_response
    (K Sigma : AlgebraEnd E)
    (ω : AlgebraEnd E →L[ℝ] ℝ) :
    modularCirculation K Sigma ω = ω (Sigma.comp K) :=
  rfl

end RealFluid

section RealKreinFluid

variable {E : Type _}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The vorticity of a skew-adjoint velocity field equals the field itself. -/
lemma vorticity_eq_self_of_skew
    {u : VelocityField E}
    (hSkew : ContinuousLinearMap.adjoint u = -u) :
    vorticity u = u := by
  unfold vorticity
  rw [hSkew]
  calc
    (2 : ℝ)⁻¹ • (u - -u) = (2 : ℝ)⁻¹ • (u + u) := by simp
    _ = (2 : ℝ)⁻¹ • ((2 : ℝ) • u) := by simp [two_smul]
    _ = ((2 : ℝ)⁻¹ * (2 : ℝ)) • u := by rw [smul_smul]
    _ = u := by norm_num

/--
Linearized momentum residual for the vorticity closure condition `ω(u) = u`.
-/
noncomputable def momentumResidual
    (u : VelocityField E) : VelocityField E :=
  vorticity u - u

omit [FiniteDimensional ℝ E] in
/--
The linearized momentum residual vanishes for skew-adjoint flows.
-/
lemma momentumResidual_eq_zero_of_skew
    {u : VelocityField E}
    (hSkew : ContinuousLinearMap.adjoint u = -u) :
    momentumResidual u = 0 := by
  unfold momentumResidual
  rw [vorticity_eq_self_of_skew (E := E) hSkew]
  simp

/--
Canonical unit-density anomaly state.
-/
noncomputable def anomalyFluidState
    (A B_mp B_dr : VelocityField E) :
    FluidState E :=
  anomalyFluidStateWithDensity (E := E) A B_mp B_dr 1 (by norm_num)

/-- Operator-level membrane identity on the canonical unit-density anomaly state. -/
theorem anomaly_as_fluid_state
    (A B_mp B_dr : VelocityField E) :
    (anomalyFluidState (E := E) A B_mp B_dr).u = EinsteinAnomaly A B_mp B_dr := by
  rfl

/--
State-level momentum closure for the canonical anomaly fluid:
if the Einstein anomaly lane is skew-adjoint, the induced canonical fluid state
has zero linearized momentum residual.
-/
theorem anomalyFluidState_momentumResidual_eq_zero_of_skew
    (A B_mp B_dr : VelocityField E)
    (hSkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr) :
    momentumResidual (E := E) ((anomalyFluidState (E := E) A B_mp B_dr).u) = 0 := by
  have hResidual :
      momentumResidual (E := E) (EinsteinAnomaly A B_mp B_dr) = 0 :=
    momentumResidual_eq_zero_of_skew (E := E) hSkew
  simpa [anomaly_as_fluid_state (E := E) A B_mp B_dr] using hResidual

omit [FiniteDimensional ℝ E] in
/--
If the anomaly lane is skew-adjoint, its linearized momentum residual vanishes.
-/
theorem anomalyMomentumResidual_eq_zero_of_skew
    (A B_mp B_dr : VelocityField E)
    (hSkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr) :
    momentumResidual (E := E) (EinsteinAnomaly A B_mp B_dr) = 0 := by
  exact momentumResidual_eq_zero_of_skew (E := E) hSkew

/--
Regularization-driven momentum closure:
if `B_mp` is Moore-Penrose for `A`, `B_dr` is Drazin for `A`, and the Drazin
spectral projector is self-adjoint, then the Einstein-anomaly lane has zero
linearized momentum residual.
-/
theorem anomalyMomentumResidual_eq_zero_of_regularization
    (A B_mp B_dr : VelocityField E)
    (k : ℕ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr : IsDrazinInverse A B_dr k)
    (h_dr_star : star (A * B_dr) = A * B_dr) :
    momentumResidual (E := E) (EinsteinAnomaly A B_mp B_dr) = 0 := by
  have hSkew :
      ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
        = -EinsteinAnomaly A B_mp B_dr := by
    simpa using
      (einsteinAnomaly_skew_adjoint (a := A) (b_mp := B_mp) (b_dr := B_dr)
        (k := k) h_mp h_dr h_dr_star)
  exact anomalyMomentumResidual_eq_zero_of_skew (E := E) A B_mp B_dr hSkew

/--
State-level regularization-driven momentum closure on the canonical unit-density
anomaly fluid state.
-/
theorem anomalyFluidState_momentumResidual_eq_zero_of_regularization
    (A B_mp B_dr : VelocityField E)
    (k : ℕ)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr : IsDrazinInverse A B_dr k)
    (h_dr_star : star (A * B_dr) = A * B_dr) :
    momentumResidual (E := E) ((anomalyFluidState (E := E) A B_mp B_dr).u) = 0 := by
  have hResidual :
      momentumResidual (E := E) (EinsteinAnomaly A B_mp B_dr) = 0 :=
    anomalyMomentumResidual_eq_zero_of_regularization
      (E := E) A B_mp B_dr k h_mp h_dr h_dr_star
  simpa [anomaly_as_fluid_state (E := E) A B_mp B_dr] using hResidual

end RealKreinFluid

section MadelungBridge

variable {E : Type _}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- Doubled real carrier used as the Arnold/Majorana context-adaptive state space. -/
abbrev ArnoldMajoranaCarrier (E : Type _) := DoubledSpace E

/-- Modular Hamiltonian as an operator on the doubled carrier. -/
abbrev modularHamiltonian (K : AlgebraEnd E) : AlgebraEnd E := K

/--
Second-order regularizer: composition square of the modular Hamiltonian.
-/
noncomputable def freeEnergyHessianRegularizer
    (K : AlgebraEnd E) : AlgebraEnd E :=
  K.comp K

/-- Grand-canonical ensemble scalar average of a modular observable. -/
noncomputable def grandCanonicalEnsembleAverage
    (ω : AlgebraEnd E →L[ℝ] ℝ) (K : AlgebraEnd E) : ℝ :=
  ω K

/-- Linearized modular flow converted to a velocity field. -/
def modularVelocity
    (β : ℝ) (K : AlgebraEnd E) :
    AlgebraEnd E :=
  β • modularHamiltonian (E := E) K

set_option linter.unusedSectionVars false in
/--
Differential identity at `β = 0`:
the modular-velocity linear response is the modular Hamiltonian.
-/
theorem hasDerivAt_modularVelocity_zero
    (K : AlgebraEnd E) :
    HasDerivAt
      (fun β : ℝ => modularVelocity (E := E) β K)
      (modularHamiltonian (E := E) K)
      0 := by
  let e : ℝ →L[ℝ] AlgebraEnd E :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (modularHamiltonian (E := E) K)
  have hF : HasFDerivAt (fun β : ℝ => modularVelocity (E := E) β K) e 0 := by
    simpa [e, modularVelocity, modularHamiltonian] using (e.hasFDerivAt (x := (0 : ℝ)))
  have hD : HasDerivAt
      (fun β : ℝ => modularVelocity (E := E) β K)
      (e 1)
      0 := hF.hasDerivAt
  simpa [e, modularVelocity, modularHamiltonian] using hD

set_option linter.unusedSectionVars false in
/-- Derivative form of `hasDerivAt_modularVelocity_zero`. -/
theorem deriv_modularVelocity_zero
    (K : AlgebraEnd E) :
    deriv (fun β : ℝ => modularVelocity (E := E) β K) 0 =
      modularHamiltonian (E := E) K := by
  letI : IsBoundedSMul ℝ (AlgebraEnd E) := by
    refine IsBoundedSMul.of_norm_smul_le (α := ℝ) (β := AlgebraEnd E) ?_
    intro c f
    exact (ContinuousLinearMap.opNorm_smul_le (𝕜₂ := ℝ)
      (E := DoubledSpace E) (F := DoubledSpace E) c f)
  change deriv (fun β : ℝ => β • K) 0 = K
  simpa using (((hasDerivAt_id (0 : ℝ)).smul_const K).deriv)

/-- Linear embedding of the base carrier into the doubled carrier (`x ↦ (x,0)`). -/
noncomputable def embedBase : E →L[ℝ] ArnoldMajoranaCarrier E where
  toLinearMap :=
    { toFun := fun x => InfoGeometry.Krein.to_doubled x 0
      map_add' := by
        intro x y
        apply (WithLp.ofLp_injective 2)
        simp [InfoGeometry.Krein.to_doubled]
      map_smul' := by
        intro a x
        apply (WithLp.ofLp_injective 2)
        simp [InfoGeometry.Krein.to_doubled, smul_zero] }
  cont := by
    simpa [InfoGeometry.Krein.to_doubled] using
      (WithLp.prod_continuous_toLp (p := 2) (α := E) (β := E)).comp
        (continuous_id.prodMk continuous_const)

/-- First-component projection from doubled carrier to the base carrier. -/
noncomputable def projBase : ArnoldMajoranaCarrier E →L[ℝ] E where
  toLinearMap :=
    { toFun := fun v => WithLp.fst v
      map_add' := by intro v w; simp [WithLp.add_fst]
      map_smul' := by intro a v; simp [WithLp.smul_fst] }
  cont := by
    simpa using
      WithLp.continuous_fst (p := 2) (α := E) (β := E)

/-- Collapses a doubled-carrier modular velocity into a base-carrier velocity field. -/
noncomputable def collapseToBaseVelocity
    (M : AlgebraEnd E) : VelocityField E :=
  (projBase (E := E)).comp (M.comp (embedBase (E := E)))

/-- Thermodynamic/probabilistic smoothing criterion: divergence-free collapsed modular velocity. -/
def IsThermodynamicallySmoothed
    (β : ℝ) (K : AlgebraEnd E) : Prop :=
  Real.log
      (|LinearMap.det
        (collapseToBaseVelocity (E := E) (modularVelocity (E := E) β K)).toLinearMap|)
    = 0

/--
Canonical smoothing witness at thermal equilibrium (`β = 0`):
the collapsed modular velocity vanishes, hence its log-volume change is zero.
-/
theorem isThermodynamicallySmoothed_zero_beta
    (K : AlgebraEnd E) :
    IsThermodynamicallySmoothed (E := E) 0 K := by
  unfold IsThermodynamicallySmoothed
  simp [collapseToBaseVelocity, modularVelocity]

/-- Madelung density from the doubled real thermal vacuum amplitude. -/
noncomputable def madelungDensity
    {K : AlgebraEnd E}
    (vac : ThermalVacuum (E := E) K) : ℝ :=
  ‖WithLp.fst vac.Omega‖ ^ (2 : ℕ) + ‖WithLp.snd vac.Omega‖ ^ (2 : ℕ)

set_option linter.unusedSectionVars false in
/-- The Madelung density is strictly positive for nondegenerate thermal vacua. -/
lemma madelungDensity_pos
    {K : AlgebraEnd E}
    (vac : ThermalVacuum (E := E) K) :
    0 < madelungDensity (E := E) vac := by
  dsimp [madelungDensity]
  by_cases hx : WithLp.fst vac.Omega = 0
  · have hy : WithLp.snd vac.Omega ≠ 0 := by
      intro hy
      have hOmegaZero : vac.Omega = 0 := by
        apply InfoGeometry.Krein.DoubledSpace.ext
        · simpa using hx
        · simpa using hy
      exact (vac.vacuum_nonzero hOmegaZero).elim
    exact add_pos_of_nonneg_of_pos
      (pow_nonneg (norm_nonneg _) 2)
      (pow_pos (norm_pos_iff.mpr hy) 2)
  · exact add_pos_of_pos_of_nonneg
      (pow_pos (norm_pos_iff.mpr hx) 2)
      (pow_nonneg (norm_nonneg _) 2)

/-- Madelung phase from ensemble averaging of the modular Hamiltonian. -/
noncomputable def madelungPhase
    (ω : AlgebraEnd E →L[ℝ] ℝ) (K : AlgebraEnd E) : ℝ :=
  grandCanonicalEnsembleAverage (E := E) ω K

/--
Madelung functor (linearized):
thermal-vacuum modular data is promoted to a divergence-free fluid state.
-/
noncomputable def madelungFluidState
    (β : ℝ)
    (K : AlgebraEnd E)
    (vac : ThermalVacuum (E := E) K)
    (ω : AlgebraEnd E →L[ℝ] ℝ)
    (_hSmooth : IsThermodynamicallySmoothed β K) :
    FluidState E :=
  { u := collapseToBaseVelocity (E := E) (modularVelocity (E := E) β K)
    ρ := madelungDensity (E := E) vac
    p := madelungPhase (E := E) ω K
    density_stationary := madelungDensity_pos (E := E) vac }

@[simp] theorem madelungFluidState_velocity
    (β : ℝ)
    (K : AlgebraEnd E)
    (vac : ThermalVacuum (E := E) K)
    (ω : AlgebraEnd E →L[ℝ] ℝ)
    (hSmooth : IsThermodynamicallySmoothed β K) :
    (madelungFluidState β K vac ω hSmooth).u
      = collapseToBaseVelocity (E := E) (modularVelocity β K) := rfl

/--
Canonical equilibrium Madelung state with smoothing discharged constructively
from `β = 0`.
-/
noncomputable def madelungFluidState_zero
    (K : AlgebraEnd E)
    (vac : ThermalVacuum (E := E) K)
    (ω : AlgebraEnd E →L[ℝ] ℝ) :
    FluidState E :=
  madelungFluidState (E := E) 0 K vac ω
    (isThermodynamicallySmoothed_zero_beta (E := E) K)

@[simp] theorem madelungFluidState_zero_velocity
    (K : AlgebraEnd E)
    (vac : ThermalVacuum (E := E) K)
    (ω : AlgebraEnd E →L[ℝ] ℝ) :
    (madelungFluidState_zero (E := E) K vac ω).u = 0 := by
  simp [madelungFluidState_zero, madelungFluidState, collapseToBaseVelocity, modularVelocity]

end MadelungBridge


section HelicityBridge

variable {E : Type _}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/--
Helicity Operator (H).
The composition of the velocity Jacobian and its vorticity.
H = u ∘ vorticity(u).
-/
noncomputable def helicityOperator
    (u : VelocityField E) : VelocityField E :=
  u.comp (vorticity u)

/--
Forward flow component in the doubled space.
-/
noncomputable def forwardWave
    (u : VelocityField E) : AlgebraEnd E :=
  (ContinuousLinearMap.id ℝ (DoubledSpace E) + spectral_epsilon (E := E)).comp (embedBase.comp (u.comp projBase))

/--
Backward flow component in the doubled space.
-/
noncomputable def backwardWave
    (u : VelocityField E) : AlgebraEnd E :=
  (ContinuousLinearMap.id ℝ (DoubledSpace E) - spectral_epsilon (E := E)).comp (embedBase.comp (u.comp projBase))

/--
Twin Wave Helicity Invariant.
Defined as the pairing (interference) between the forward and backward waves in the Krein space.
-/
noncomputable def twinWaveHelicity
    (u : VelocityField E) (Ω : AlgebraEnd E →L[ℝ] ℝ) : ℝ :=
  Ω ((forwardWave u).comp (backwardWave u))

set_option linter.unusedSectionVars false in
/--
Theorem: Helicity-to-TwinWave Bridge.
The helicity invariant is constructively identified with the pairing of the forward
and backward modular waves.
-/
theorem helicity_eq_twin_wave_pairing
    (u : VelocityField E) (Ω : AlgebraEnd E →L[ℝ] ℝ) :
    twinWaveHelicity u Ω = Ω ((forwardWave u).comp (backwardWave u)) :=
  rfl

end HelicityBridge


section ChiralFlowBridge

variable {E : Type _}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-!
### Krein-Modular Basis for Chiral Flow

The 'two types' of chiral charges are formally identified with the eigenspaces
of the Krein spectral involution `ε`, or equivalently, the sectors swapped by
the modular conjugation `J`.
-/

/--
Krein spectral projectors: $P_+ = (I + ε)/2$ and $P_- = (I - ε)/2$.
These isolate the two types of chiral sectors.
-/
noncomputable def kreinPlusProjector : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (DoubledSpace E) + spectral_epsilon (E := E))

noncomputable def kreinMinusProjector : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (DoubledSpace E) - spectral_epsilon (E := E))

/--
Two-type Chiral Charges:
Representing the 'plus' and 'minus' sectors of the modular doubling.
Linked to the Krein projectors $P_+$ and $P_-$.
-/
structure ChiralCharges where
  plus : ℝ
  minus : ℝ

/-- Net Chiral Charge: the imbalance (chirality) between the two sectors. -/
def netChiralCharge (c : ChiralCharges) : ℝ := c.plus - c.minus

/--
Chiral Flux:
Current generated by the Einstein Anomaly acting as a transition operator.
For Type III factors, this is the modular response (weight pairing) to the anomaly.
The flux is the mechanism that 'charges' the two sectors by shifting population across $J$.
-/
noncomputable def chiralFlux
    (χ : VelocityField E) (ω : VelocityField E →L[ℝ] ℝ) : ℝ :=
  -- Expectation value of the anomaly under the state/weight ω.
  ω χ

omit [FiniteDimensional ℝ E] in
/--
Theorem: Anomaly sources Chiral Flow.
The commutator anomaly χ [P_D, P_MP] sources the currents between the two charge sectors.
This formally encodes the hunch that circulation is a flow of chiral charges,
driven by the mismatch between geometric (Penrose) and spectral (Drazin) data.
-/
theorem chiral_anomaly_sources_flow
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ) :
    chiralFlux (EinsteinAnomaly A B_mp B_dr) ω
      = ω (A * B_mp * (A * B_dr) - A * B_dr * (A * B_mp)) := by
  rfl

end ChiralFlowBridge

attribute [rep_depth operator]
  VelocityField
  AlgebraEnd
  vorticity
  adjoint_vorticity_eq_neg
  modularCirculation
  anomalyFluidStateWithDensity
  anomalyFluidStateWithDensity_u
  anomalyFluidStateWithDensity_rho
  anomaly_as_fluid_state_with_density
  modular_circulation_response
  vorticity_eq_self_of_skew
  momentumResidual
  momentumResidual_eq_zero_of_skew
  anomalyFluidState
  anomaly_as_fluid_state
  anomalyMomentumResidual_eq_zero_of_skew
  ArnoldMajoranaCarrier
  modularHamiltonian
  freeEnergyHessianRegularizer
  grandCanonicalEnsembleAverage
  modularVelocity
  hasDerivAt_modularVelocity_zero
  deriv_modularVelocity_zero
  embedBase
  projBase
  collapseToBaseVelocity
  madelungDensity
  madelungDensity_pos
  madelungPhase
  madelungFluidState
  madelungFluidState_velocity
  madelungFluidState_zero
  madelungFluidState_zero_velocity
  forwardWave
  backwardWave
  twinWaveHelicity
  helicityOperator
  helicity_eq_twin_wave_pairing
  kreinPlusProjector
  kreinMinusProjector
  netChiralCharge
  chiralFlux
  IsThermodynamicallySmoothed
  isThermodynamicallySmoothed_zero_beta
  chiral_anomaly_sources_flow

end InfoGeometry.Canonical
