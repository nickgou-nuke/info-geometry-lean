import InfoGeometry.Canonical.Singular
import InfoGeometry.Canonical.DrazinInfiniteCore
import InfoGeometry.Canonical.FluidCore
import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.Thermal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Tactic.NormNum
import InfoGeometry.Meta.Architecture

/-!
# Linearized Anomaly-Fluid Bridge

Operator-level bridge from singular inverse anomalies to linearized vorticity
closure observables.

The module models a linear velocity Jacobian and connects the skew-adjoint
Einstein anomaly to the closure condition `vorticity u = u`.

This is not a formalization of the Navier-Stokes PDE. It does not contain
global-in-time evolution, pressure projection, viscosity, Laplacian estimates,
or a regularity theorem.
-/

namespace InfoGeometry.Canonical

open scoped InnerProductSpace
open InfoGeometry.Krein

/-- Endomorphisms on the canonical doubled carrier. -/
abbrev AlgebraEnd
    (E : Type _)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] : Type _ :=
  DoubledSpace E →L[ℝ] DoubledSpace E

/--
A linearized fluid readout.

This stores velocity, density, and pressure data. It does not by itself encode
the incompressibility equation; incompressibility or volume preservation must be
supplied separately by a smoothing/backend property.
-/
structure FluidState
    (E : Type _)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  u : VelocityField E
  ρ : ℝ
  p : ℝ
  -- Positivity of the modular density.
  density_pos : ρ > 0

/-- Vorticity operator: skew-adjoint part of a velocity Jacobian. -/
noncomputable def vorticity
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : VelocityField E) : VelocityField E :=
  (2 : ℝ)⁻¹ • (u - ContinuousLinearMap.adjoint u)

/-- Symmetric strain-rate part of a linear velocity Jacobian. -/
noncomputable def strainRate
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : VelocityField E) : VelocityField E :=
  (2 : ℝ)⁻¹ • (u + ContinuousLinearMap.adjoint u)

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

/-- The strain-rate extraction is self-adjoint on the ambient Hilbert metric. -/
theorem adjoint_strainRate_eq_self
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : VelocityField E) :
    ContinuousLinearMap.adjoint (strainRate u) = strainRate u := by
  unfold strainRate
  calc
    ContinuousLinearMap.adjoint ((2 : ℝ)⁻¹ • (u + ContinuousLinearMap.adjoint u))
        = (2 : ℝ)⁻¹ • (ContinuousLinearMap.adjoint u + u) := by
            simp
    _ = (2 : ℝ)⁻¹ • (u + ContinuousLinearMap.adjoint u) := by
          rw [add_comm]
    _ = strainRate u := by
          rfl

/-- A linear velocity Jacobian decomposes into strain plus vorticity. -/
theorem strainRate_add_vorticity_eq
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : VelocityField E) :
    strainRate u + vorticity u = u := by
  unfold strainRate vorticity
  ext x
  simp [sub_eq_add_neg]
  module

/-- Divergence-free (trace-free) property for a velocity field Jacobian. -/
def IsDivergenceFree
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (u : VelocityField E) : Prop :=
  LinearMap.trace ℝ E u.toLinearMap = 0

theorem trace_adjoint
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (u : VelocityField E) :
    LinearMap.trace ℝ E (ContinuousLinearMap.adjoint u).toLinearMap =
      LinearMap.trace ℝ E u.toLinearMap := by
  obtain ⟨ι, b, _⟩ := exists_orthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner (ContinuousLinearMap.adjoint u).toLinearMap b]
  rw [LinearMap.trace_eq_sum_inner u.toLinearMap b]
  apply Fintype.sum_congr
  intro x
  dsimp
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_comm]

theorem vorticity_isDivergenceFree
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (u : VelocityField E) :
    IsDivergenceFree (vorticity u) := by
  unfold IsDivergenceFree vorticity
  dsimp
  rw [LinearMap.map_smul, LinearMap.map_sub, trace_adjoint]
  simp

/--
Modular-level circulation pairing.

This pairs an installed modular Hamiltonian/readout `K` with a surface operator
`Sigma` under the linear weight `ω`. This definition does not construct `K` as
`-log ρ`; that identification belongs in a separate modular/Radon-Nikodym
property.
-/
noncomputable def modularCirculation
    {E : Type _}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (K : AlgebraEnd E) (Sigma : AlgebraEnd E) (ω : AlgebraEnd E →L[ℝ] ℝ) : ℝ :=
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
    density_pos := h_pos }

omit [FiniteDimensional ℝ E] in
@[simp] lemma anomalyFluidStateWithDensity_u
    (A B_mp B_dr : VelocityField E)
    (ρ_val : ℝ) (h_pos : ρ_val > 0) :
    (anomalyFluidStateWithDensity (E := E) A B_mp B_dr ρ_val h_pos).u
      = EinsteinAnomaly A B_mp B_dr := rfl

omit [FiniteDimensional ℝ E] in
@[simp] lemma anomalyFluidStateWithDensity_rho
    (A B_mp B_dr : VelocityField E)
    (ρ_val : ℝ) (h_pos : ρ_val > 0) :
    (anomalyFluidStateWithDensity (E := E) A B_mp B_dr ρ_val h_pos).ρ = ρ_val := rfl

omit [FiniteDimensional ℝ E] in
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
Definitional form of the modular circulation pairing.
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

omit [FiniteDimensional ℝ E] in
/-- The vorticity of a self-adjoint velocity field vanishes. -/
lemma vorticity_eq_zero_of_self_adjoint
    {u : VelocityField E}
    (hSelf : ContinuousLinearMap.adjoint u = u) :
    vorticity u = 0 := by
  unfold vorticity
  rw [hSelf]
  simp

/--
Linearized residual for the vorticity closure condition `vorticity u = u`.
-/
noncomputable def vorticityClosureResidual
    (u : VelocityField E) : VelocityField E :=
  vorticity u - u

/--
Deprecated compatibility name: this is not the full Navier-Stokes momentum
residual. Use `vorticityClosureResidual`.
-/
noncomputable def momentumResidual
    (u : VelocityField E) : VelocityField E :=
  vorticityClosureResidual u

omit [FiniteDimensional ℝ E] in
/--
The linearized vorticity-closure residual vanishes for skew-adjoint flows.
-/
lemma vorticityClosureResidual_eq_zero_of_skew
    {u : VelocityField E}
    (hSkew : ContinuousLinearMap.adjoint u = -u) :
    vorticityClosureResidual u = 0 := by
  unfold vorticityClosureResidual
  rw [vorticity_eq_self_of_skew (E := E) hSkew]
  simp

omit [FiniteDimensional ℝ E] in
/-- Compatibility form for the deprecated `momentumResidual` name. -/
lemma momentumResidual_eq_zero_of_skew
    {u : VelocityField E}
    (hSkew : ContinuousLinearMap.adjoint u = -u) :
    momentumResidual u = 0 := by
  exact vorticityClosureResidual_eq_zero_of_skew (E := E) hSkew

/--
Canonical unit-density anomaly state.
-/
noncomputable def anomalyFluidState
    (A B_mp B_dr : VelocityField E) :
    FluidState E :=
  anomalyFluidStateWithDensity (E := E) A B_mp B_dr 1 (by norm_num)

omit [FiniteDimensional ℝ E] in
/-- Operator-level membrane identity on the canonical unit-density anomaly state. -/
theorem anomaly_as_fluid_state
    (A B_mp B_dr : VelocityField E) :
    (anomalyFluidState (E := E) A B_mp B_dr).u = EinsteinAnomaly A B_mp B_dr := by
  rfl

omit [FiniteDimensional ℝ E] in
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

omit [FiniteDimensional ℝ E] in
/--
Regularization-driven momentum closure:
if `B_mp` is Moore-Penrose for `A`, `B_dr` is Drazin for `A`, and the Drazin
regularization channel `A * B_dr` is star-selfadjoint, then the
Einstein-anomaly lane has zero linearized momentum residual.
-/
theorem anomalyMomentumResidual_eq_zero_of_regularization
    (A B_mp B_dr : VelocityField E)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (k : ℕ)
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

omit [FiniteDimensional ℝ E] in
/--
Regularization-driven momentum closure with existential Drazin property:
for fixed `B_dr`, a property `∃ k, IsDrazinInverse A B_dr k` is sufficient.
-/
theorem anomalyMomentumResidual_eq_zero_of_regularization_exists
    (A B_mp B_dr : VelocityField E)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr_exists : ∃ k : ℕ, IsDrazinInverse A B_dr k)
    (h_dr_star : star (A * B_dr) = A * B_dr) :
    momentumResidual (E := E) (EinsteinAnomaly A B_mp B_dr) = 0 := by
  rcases h_dr_exists with ⟨k, h_dr⟩
  exact anomalyMomentumResidual_eq_zero_of_regularization
    (E := E) A B_mp B_dr h_mp k h_dr h_dr_star

omit [FiniteDimensional ℝ E] in
/--
State-level regularization-driven momentum closure on the canonical unit-density
anomaly fluid state.
-/
theorem anomalyFluidState_momentumResidual_eq_zero_of_regularization
    (A B_mp B_dr : VelocityField E)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (k : ℕ)
    (h_dr : IsDrazinInverse A B_dr k)
    (h_dr_star : star (A * B_dr) = A * B_dr) :
    momentumResidual (E := E) ((anomalyFluidState (E := E) A B_mp B_dr).u) = 0 := by
  have hResidual :
      momentumResidual (E := E) (EinsteinAnomaly A B_mp B_dr) = 0 :=
    anomalyMomentumResidual_eq_zero_of_regularization
      (E := E) A B_mp B_dr h_mp k h_dr h_dr_star
  simpa [anomaly_as_fluid_state (E := E) A B_mp B_dr] using hResidual

omit [FiniteDimensional ℝ E] in
/--
State-level regularization closure with existential Drazin property:
for fixed `B_dr`, a property `∃ k, IsDrazinInverse A B_dr k` is sufficient.
-/
theorem anomalyFluidState_momentumResidual_eq_zero_of_regularization_exists
    (A B_mp B_dr : VelocityField E)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr_exists : ∃ k : ℕ, IsDrazinInverse A B_dr k)
    (h_dr_star : star (A * B_dr) = A * B_dr) :
    momentumResidual (E := E) ((anomalyFluidState (E := E) A B_mp B_dr).u) = 0 := by
  rcases h_dr_exists with ⟨k, h_dr⟩
  exact anomalyFluidState_momentumResidual_eq_zero_of_regularization
    (E := E) A B_mp B_dr h_mp k h_dr h_dr_star

/--
Finite-dimensional regularization package:
derive a canonical Drazin property internally and expose anomaly skewness as a
star-selfadjointness consequence on the induced Drazin regularization channel.
-/
theorem anomalySkew_of_regularization_of_finiteDimensional
    (A B_mp : VelocityField E)
    (h_mp : IsMoorePenroseInverse A B_mp) :
    ∃ (k : ℕ) (B_dr : VelocityField E),
      IsDrazinInverse A B_dr k ∧
      (star (A * B_dr) = A * B_dr →
        ContinuousLinearMap.adjoint (EinsteinAnomaly A B_mp B_dr)
          = -EinsteinAnomaly A B_mp B_dr) := by
  rcases DrazinExistenceBridge.exists_canonicalDrazinInverse_global_endCLM
      (E := E) A with ⟨k, B_dr, h_dr⟩
  refine ⟨k, B_dr, h_dr, ?_⟩
  intro h_dr_star
  simpa using
    (einsteinAnomaly_skew_adjoint
      (a := A)
      (b_mp := B_mp)
      (b_dr := B_dr)
      (k := k)
      h_mp
      h_dr
      h_dr_star)

/--
Finite-dimensional regularization package at the momentum-closure level:
derive a canonical Drazin property internally and reduce closure to the
star-selfadjointness channel.
-/
theorem anomalyMomentumResidual_eq_zero_of_regularization_of_finiteDimensional
    (A B_mp : VelocityField E)
    (h_mp : IsMoorePenroseInverse A B_mp) :
    ∃ (k : ℕ) (B_dr : VelocityField E),
      IsDrazinInverse A B_dr k ∧
      (star (A * B_dr) = A * B_dr →
        momentumResidual (E := E) (EinsteinAnomaly A B_mp B_dr) = 0) := by
  rcases anomalySkew_of_regularization_of_finiteDimensional
      (E := E) A B_mp h_mp with ⟨k, B_dr, h_dr, _hSkew_of_star⟩
  refine ⟨k, B_dr, h_dr, ?_⟩
  intro h_dr_star
  exact anomalyMomentumResidual_eq_zero_of_regularization_exists
    (E := E) A B_mp B_dr h_mp ⟨k, h_dr⟩ h_dr_star

/--
Finite-dimensional regularization package at the state level:
derive a canonical Drazin property internally and reduce state momentum closure
to the star-selfadjointness channel.
-/
theorem anomalyFluidState_momentumResidual_eq_zero_of_regularization_of_finiteDimensional
    (A B_mp : VelocityField E)
    (h_mp : IsMoorePenroseInverse A B_mp) :
    ∃ (k : ℕ) (B_dr : VelocityField E),
      IsDrazinInverse A B_dr k ∧
      (star (A * B_dr) = A * B_dr →
        momentumResidual (E := E) ((anomalyFluidState (E := E) A B_mp B_dr).u) = 0) := by
  rcases anomalySkew_of_regularization_of_finiteDimensional
      (E := E) A B_mp h_mp with ⟨k, B_dr, h_dr, _hSkew_of_star⟩
  refine ⟨k, B_dr, h_dr, ?_⟩
  intro h_dr_star
  exact anomalyFluidState_momentumResidual_eq_zero_of_regularization_exists
    (E := E) A B_mp B_dr h_mp ⟨k, h_dr⟩ h_dr_star

/--
Finite-dimensional global-Drazin regularization wrapper:
derive a canonical Drazin property internally and expose momentum closure while
keeping only the star/selfadjointness channel as external input.
-/
theorem anomalyMomentumResidual_eq_zero_of_regularization_global_drazin
    (A B_mp : VelocityField E)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr_star_of_drazin :
      ∀ {k : ℕ} {B_dr : VelocityField E},
        IsDrazinInverse A B_dr k →
          star (A * B_dr) = A * B_dr) :
    ∃ (B_dr : VelocityField E),
      momentumResidual (E := E) (EinsteinAnomaly A B_mp B_dr) = 0 := by
  rcases DrazinExistenceBridge.exists_canonicalDrazinInverse_global_endCLM
      (E := E) A with ⟨k, B_dr, h_dr⟩
  refine ⟨B_dr, ?_⟩
  exact anomalyMomentumResidual_eq_zero_of_regularization
    (E := E)
    A B_mp B_dr
    h_mp
    k
    h_dr
    (h_dr_star_of_drazin h_dr)

/--
Finite-dimensional global-Drazin state-level wrapper:
derive a canonical Drazin property internally and expose fluid-state momentum
closure while keeping only the star/selfadjointness channel as external input.
-/
theorem anomalyFluidState_momentumResidual_eq_zero_of_regularization_global_drazin
    (A B_mp : VelocityField E)
    (h_mp : IsMoorePenroseInverse A B_mp)
    (h_dr_star_of_drazin :
      ∀ {k : ℕ} {B_dr : VelocityField E},
        IsDrazinInverse A B_dr k →
          star (A * B_dr) = A * B_dr) :
    ∃ (B_dr : VelocityField E),
      momentumResidual (E := E) ((anomalyFluidState (E := E) A B_mp B_dr).u) = 0 := by
  rcases DrazinExistenceBridge.exists_canonicalDrazinInverse_global_endCLM
      (E := E) A with ⟨k, B_dr, h_dr⟩
  refine ⟨B_dr, ?_⟩
  exact anomalyFluidState_momentumResidual_eq_zero_of_regularization
    (E := E)
    A B_mp B_dr
    h_mp
    k
    h_dr
    (h_dr_star_of_drazin h_dr)

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

/-- Collapsed Jacobian `id + velocity`. -/
noncomputable def collapsedJacobian
    (β : ℝ) (K : AlgebraEnd E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E +
    collapseToBaseVelocity (E := E) (modularVelocity (E := E) β K)

/-- Absolute determinant of the collapsed Jacobian. -/
noncomputable def collapsedJacobianAbsDet
    (β : ℝ) (K : AlgebraEnd E) : ℝ :=
  |LinearMap.det ((collapsedJacobian (E := E) β K).toLinearMap)|

/--
Thermodynamic/probabilistic smoothing criterion:
the collapsed Jacobian has unit absolute volume change.
-/
def IsThermodynamicallySmoothed
    (β : ℝ) (K : AlgebraEnd E) : Prop :=
  collapsedJacobianAbsDet (E := E) β K = 1

set_option linter.unusedSectionVars false in
/--
Canonical smoothing property at thermal equilibrium (`β = 0`):
the collapsed modular velocity vanishes, so the Jacobian is the identity and
the absolute volume change is one.
-/
theorem isThermodynamicallySmoothed_zero_beta
    (K : AlgebraEnd E) :
    IsThermodynamicallySmoothed (E := E) 0 K := by
  unfold IsThermodynamicallySmoothed collapsedJacobianAbsDet collapsedJacobian
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
thermal-vacuum modular data is promoted to a finite-dimensional fluid state
under an installed smoothing/volume-preservation property.
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
    density_pos := madelungDensity_pos (E := E) vac }

@[simp] theorem madelungFluidState_velocity
    (β : ℝ)
    (K : AlgebraEnd E)
    (vac : ThermalVacuum (E := E) K)
    (ω : AlgebraEnd E →L[ℝ] ℝ)
    (hSmooth : IsThermodynamicallySmoothed β K) :
    (madelungFluidState β K vac ω hSmooth).u
      = collapseToBaseVelocity (E := E) (modularVelocity β K) := rfl

/--
A Madelung fluid state equipped with the determinant/volume smoothing property
from the modular velocity construction.
-/
structure SmoothedMadelungFluidState
    (E : Type _)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] where
  β : ℝ
  K : AlgebraEnd E
  state : FluidState E
  smoothed : IsThermodynamicallySmoothed (E := E) β K
  velocity_eq :
    state.u =
      collapseToBaseVelocity (E := E)
        (modularVelocity (E := E) β K)

/-- Proof-bearing Madelung state constructor preserving the smoothing property. -/
noncomputable def smoothedMadelungFluidState
    (β : ℝ)
    (K : AlgebraEnd E)
    (vac : ThermalVacuum (E := E) K)
    (ω : AlgebraEnd E →L[ℝ] ℝ)
    (hSmooth : IsThermodynamicallySmoothed β K) :
    SmoothedMadelungFluidState E where
  β := β
  K := K
  state := madelungFluidState (E := E) β K vac ω hSmooth
  smoothed := hSmooth
  velocity_eq := rfl

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

/-- Proof-bearing equilibrium Madelung state at `β = 0`. -/
noncomputable def smoothedMadelungFluidState_zero
    (K : AlgebraEnd E)
    (vac : ThermalVacuum (E := E) K)
    (ω : AlgebraEnd E →L[ℝ] ℝ) :
    SmoothedMadelungFluidState E :=
  smoothedMadelungFluidState (E := E) 0 K vac ω
    (isThermodynamicallySmoothed_zero_beta (E := E) K)

@[simp] theorem madelungFluidState_zero_velocity
    (K : AlgebraEnd E)
    (vac : ThermalVacuum (E := E) K)
    (ω : AlgebraEnd E →L[ℝ] ℝ) :
    (madelungFluidState_zero (E := E) K vac ω).u = 0 := by
  simp [madelungFluidState_zero, madelungFluidState, collapseToBaseVelocity, modularVelocity]

@[simp] theorem smoothedMadelungFluidState_zero_velocity
    (K : AlgebraEnd E)
    (vac : ThermalVacuum (E := E) K)
    (ω : AlgebraEnd E →L[ℝ] ℝ) :
    (smoothedMadelungFluidState_zero (E := E) K vac ω).state.u = 0 := by
  simp [
    smoothedMadelungFluidState_zero,
    smoothedMadelungFluidState,
    madelungFluidState,
    collapseToBaseVelocity,
    modularVelocity
  ]

omit [FiniteDimensional ℝ E] in
/-- Auxiliary lemma showing the scaling behaviour of collapsed base velocity. -/
theorem collapseToBaseVelocity_smul (β : ℝ) (K : AlgebraEnd E) :
    collapseToBaseVelocity (β • K) = β • collapseToBaseVelocity K := by
  ext x
  simp [collapseToBaseVelocity]

omit [FiniteDimensional ℝ E] in
/-- Linearity of the collapsed modular velocity trace. -/
theorem trace_madelung_velocity_eq (β : ℝ) (K : AlgebraEnd E) :
    LinearMap.trace ℝ E (collapseToBaseVelocity (β • K)).toLinearMap =
      β * LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap := by
  rw [collapseToBaseVelocity_smul]
  exact map_smul (LinearMap.trace ℝ E) β (collapseToBaseVelocity K).toLinearMap

/-- Divergence-free condition reduction for the collapsed Madelung fluid state. -/
theorem madelung_divergence_free_iff (β : ℝ) (K : AlgebraEnd E)
    (vac : ThermalVacuum (E := E) K) (ω : AlgebraEnd E →L[ℝ] ℝ)
    (hSmooth : IsThermodynamicallySmoothed β K) :
    IsDivergenceFree (madelungFluidState β K vac ω hSmooth).u ↔
      β = 0 ∨ LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0 := by
  unfold IsDivergenceFree
  rw [madelungFluidState_velocity]
  unfold modularVelocity
  unfold modularHamiltonian
  rw [trace_madelung_velocity_eq]
  exact mul_eq_zero

/-- If the collapsed base velocity has zero trace, the Madelung fluid state is
divergence-free for every inverse temperature. -/
theorem madelung_divergence_free_of_trace_zero (β : ℝ) (K : AlgebraEnd E)
    (vac : ThermalVacuum (E := E) K) (ω : AlgebraEnd E →L[ℝ] ℝ)
    (hSmooth : IsThermodynamicallySmoothed β K)
    (hTrace : LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0) :
    IsDivergenceFree (madelungFluidState β K vac ω hSmooth).u := by
  rw [madelung_divergence_free_iff β K vac ω hSmooth]
  exact Or.inr hTrace

/-- If the inverse temperature is zero, the Madelung fluid state is
divergence-free. -/
theorem madelung_divergence_free_of_zero_beta (β : ℝ) (K : AlgebraEnd E)
    (vac : ThermalVacuum (E := E) K) (ω : AlgebraEnd E →L[ℝ] ℝ)
    (hSmooth : IsThermodynamicallySmoothed β K)
    (h_beta : β = 0) :
    IsDivergenceFree (madelungFluidState β K vac ω hSmooth).u := by
  rw [madelung_divergence_free_iff β K vac ω hSmooth]
  exact Or.inl h_beta

/-- The zero-parameter Madelung state has divergence-free velocity. -/
theorem madelungFluidState_isDivergenceFree_of_zero_beta
    (K : AlgebraEnd E)
    (vac : ThermalVacuum (E := E) K)
    (ω : AlgebraEnd E →L[ℝ] ℝ) :
    IsDivergenceFree
      (madelungFluidState_zero (E := E) K vac ω).u := by
  unfold IsDivergenceFree
  rw [madelungFluidState_zero_velocity]
  simp

end MadelungBridge


section HelicityBridge

variable {E : Type _}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/--
Helicity operator proxy:
the composition of the velocity Jacobian and its vorticity.
-/
noncomputable def helicityOperator
    (u : VelocityField E) : VelocityField E :=
  u.comp (vorticity u)

omit [FiniteDimensional ℝ E] in
/-- Self-adjoint velocity has zero helicity operator. -/
lemma helicityOperator_eq_zero_of_self_adjoint
    {u : VelocityField E}
    (hSelf : ContinuousLinearMap.adjoint u = u) :
    helicityOperator u = 0 := by
  unfold helicityOperator
  rw [vorticity_eq_zero_of_self_adjoint (E := E) hSelf]
  simp

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
Twin-wave helicity readout:
the pairing between the forward and backward waves in the Krein space.
-/
noncomputable def twinWaveHelicity
    (u : VelocityField E) (Ω : AlgebraEnd E →L[ℝ] ℝ) : ℝ :=
  Ω ((forwardWave u).comp (backwardWave u))

set_option linter.unusedSectionVars false in
/-- Definitional form of the twin-wave helicity readout. -/
theorem twinWaveHelicity_def
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
Projector-shaped Krein sector readouts:
`P_+ = (I + ε)/2` and `P_- = (I - ε)/2`.
-/
noncomputable def kreinPlusProjector : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (DoubledSpace E) + spectral_epsilon (E := E))

noncomputable def kreinMinusProjector : DoubledSpace E →L[ℝ] DoubledSpace E :=
  ((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (DoubledSpace E) - spectral_epsilon (E := E))

/--
Two-type Chiral Charges:
Representing the plus and minus readouts of the modular doubling.
-/
structure ChiralCharges where
  plus : ℝ
  minus : ℝ

/-- Net Chiral Charge: the imbalance (chirality) between the two sectors. -/
def netChiralCharge (c : ChiralCharges) : ℝ := c.plus - c.minus

/--
Chiral Flux:
Current generated by the Einstein Anomaly acting as a transition operator.
In this finite-dimensional bridge, this is represented by a real linear
functional pairing with the anomaly.
-/
noncomputable def chiralFlux
    (χ : VelocityField E) (ω : VelocityField E →L[ℝ] ℝ) : ℝ :=
  -- Expectation value of the anomaly under the state/weight ω.
  ω χ

omit [FiniteDimensional ℝ E] in
/--
Definitional unfolding of the chiral flux of the Einstein anomaly.
-/
theorem chiralFlux_EinsteinAnomaly_def
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ) :
    chiralFlux (EinsteinAnomaly A B_mp B_dr) ω
      = ω (A * B_mp * (A * B_dr) - A * B_dr * (A * B_mp)) := by
  rfl

omit [FiniteDimensional ℝ E] in
/-- Compatibility name for `chiralFlux_EinsteinAnomaly_def`. -/
theorem chiral_anomaly_sources_flow
    (A B_mp B_dr : VelocityField E)
    (ω : VelocityField E →L[ℝ] ℝ) :
    chiralFlux (EinsteinAnomaly A B_mp B_dr) ω
      = ω (A * B_mp * (A * B_dr) - A * B_dr * (A * B_mp)) :=
  chiralFlux_EinsteinAnomaly_def (E := E) A B_mp B_dr ω

end ChiralFlowBridge

attribute [rep_depth krein]
  AlgebraEnd
  vorticity
  strainRate
  adjoint_vorticity_eq_neg
  adjoint_strainRate_eq_self
  strainRate_add_vorticity_eq
  modularCirculation
  anomalyFluidStateWithDensity
  anomalyFluidStateWithDensity_u
  anomalyFluidStateWithDensity_rho
  anomaly_as_fluid_state_with_density
  modular_circulation_response
  vorticity_eq_self_of_skew
  vorticity_eq_zero_of_self_adjoint
  vorticityClosureResidual
  momentumResidual
  vorticityClosureResidual_eq_zero_of_skew
  momentumResidual_eq_zero_of_skew
  anomalyFluidState
  anomaly_as_fluid_state
  anomalyMomentumResidual_eq_zero_of_skew
  anomalyMomentumResidual_eq_zero_of_regularization
  anomalyMomentumResidual_eq_zero_of_regularization_exists
  anomalyFluidState_momentumResidual_eq_zero_of_regularization
  anomalyFluidState_momentumResidual_eq_zero_of_regularization_exists
  anomalySkew_of_regularization_of_finiteDimensional
  anomalyMomentumResidual_eq_zero_of_regularization_of_finiteDimensional
  anomalyFluidState_momentumResidual_eq_zero_of_regularization_of_finiteDimensional
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
  collapsedJacobian
  collapsedJacobianAbsDet
  madelungDensity
  madelungDensity_pos
  madelungPhase
  madelungFluidState
  madelungFluidState_velocity
  SmoothedMadelungFluidState
  smoothedMadelungFluidState
  madelungFluidState_zero
  smoothedMadelungFluidState_zero
  madelungFluidState_zero_velocity
  smoothedMadelungFluidState_zero_velocity
  forwardWave
  backwardWave
  twinWaveHelicity
  helicityOperator
  helicityOperator_eq_zero_of_self_adjoint
  twinWaveHelicity_def
  kreinPlusProjector
  kreinMinusProjector
  netChiralCharge
  chiralFlux
  IsThermodynamicallySmoothed
  isThermodynamicallySmoothed_zero_beta
  chiralFlux_EinsteinAnomaly_def
  chiral_anomaly_sources_flow
  IsDivergenceFree
  trace_adjoint
  vorticity_isDivergenceFree
  madelung_divergence_free_of_trace_zero
  madelung_divergence_free_of_zero_beta

end InfoGeometry.Canonical
