import InfoGeometry.Canonical.WeylTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Canonical.IncompressibleBitBridge

namespace InfoGeometry.Canonical.WeylTransportBridge

open InfoGeometry.Canonical.ConformalUnification

variable {I X A E : Type*}
variable [Fintype I]
variable [AddCommGroup A] [Module ℝ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

structure FlatCurvatureValueBridge
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (target : ℝ) where
  lineIntegrator : WeylLineIntegrator I A A
  holonomyMap : WeylHolonomyMap A ℝ
  flat_to_zeroCurvatureIntegral :
    ∀ B : WeylGaugeField X A,
      WeylGaugeField.IsFlat (Δ := Δ) B →
      lineIntegrator.integrateCurvature Δ B γ = 0
  zeroCurvatureIntegral_to_target :
    ∀ B : WeylGaugeField X A,
      lineIntegrator.integrateCurvature Δ B γ = 0 →
      lineIntegrator.holonomy holonomyMap B γ = target

abbrev FlatCurvatureProjectorObstructionBridge
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X) :=
  FlatCurvatureValueBridge (Δ := Δ) (γ := γ) ‖CI.projectorObstruction‖₊

abbrev FlatCurvatureChiralScaleBridge
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X) :=
  FlatCurvatureValueBridge (Δ := Δ) (γ := γ) CI.chiralScale

def FlatCurvatureValueBridge.retarget
    {Δ : WeylDifferentialOperator ℝ X A}
    {γ : WeylTrajectory I X}
    {t₁ t₂ : ℝ}
    (bridge : FlatCurvatureValueBridge (Δ := Δ) (γ := γ) t₁)
    (ht : t₁ = t₂) :
    FlatCurvatureValueBridge (Δ := Δ) (γ := γ) t₂ where
  lineIntegrator := bridge.lineIntegrator
  holonomyMap := bridge.holonomyMap
  flat_to_zeroCurvatureIntegral := bridge.flat_to_zeroCurvatureIntegral
  zeroCurvatureIntegral_to_target := by
    intro B hZero
    calc
      bridge.lineIntegrator.holonomy bridge.holonomyMap B γ = t₁ := by
        exact bridge.zeroCurvatureIntegral_to_target B hZero
      _ = t₂ := ht

/-- Compatibility adapter: any chiral-scale bridge induces an
operator-obstruction bridge. -/
def FlatCurvatureProjectorObstructionBridge.ofChiralScaleBridge
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge : FlatCurvatureChiralScaleBridge (CI := CI) (Δ := Δ) (γ := γ)) :
    FlatCurvatureProjectorObstructionBridge (CI := CI) (Δ := Δ) (γ := γ) :=
  FlatCurvatureValueBridge.retarget bridge CI.chiralScale_eq_projectorObstruction_nnnorm

/-- Compatibility adapter: any operator-obstruction bridge induces a
chiral-scale bridge as a corollary. -/
def FlatCurvatureChiralScaleBridge.ofProjectorObstructionBridge
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge : FlatCurvatureProjectorObstructionBridge (CI := CI) (Δ := Δ) (γ := γ)) :
    FlatCurvatureChiralScaleBridge (CI := CI) (Δ := Δ) (γ := γ) :=
  FlatCurvatureValueBridge.retarget bridge CI.projectorObstruction_nnnorm_eq_chiralScale

omit [Fintype I] in
theorem holonomy_eq_target_of_flat
    {Δ : WeylDifferentialOperator ℝ X A}
    {γ : WeylTrajectory I X}
    {target : ℝ}
    (bridge : FlatCurvatureValueBridge (Δ := Δ) (γ := γ) target)
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ = target := by
  exact bridge.zeroCurvatureIntegral_to_target B (bridge.flat_to_zeroCurvatureIntegral B hFlat)

omit [Fintype I] [FiniteDimensional ℝ E] in
/--
Operator-first flat-curvature bridge theorem:
local Weyl flatness collapses transport to the norm of the projector-obstruction
operator.
-/
theorem holonomy_eq_projectorObstruction_nnnorm_of_flat
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge (CI := CI) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ = ‖CI.projectorObstruction‖₊ := by
  simpa using holonomy_eq_target_of_flat (bridge := bridge) (B := B) hFlat

omit [Fintype I] [FiniteDimensional ℝ E] in
/-- Scalar compatibility corollary from the operator-first bridge. -/
theorem holonomy_eq_chiralScale_of_flat_compat
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge (CI := CI) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ = CI.chiralScale := by
  calc
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ = ‖CI.projectorObstruction‖₊ := by
      exact holonomy_eq_projectorObstruction_nnnorm_of_flat
        (CI := CI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat
    _ = CI.chiralScale := CI.projectorObstruction_nnnorm_eq_chiralScale

omit [Fintype I] [FiniteDimensional ℝ E] in
@[deprecated holonomy_eq_chiralScale_of_flat_compat (since := "2026-04-06")]
theorem holonomy_eq_chiralScale_of_flat
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureChiralScaleBridge (CI := CI) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ = CI.chiralScale := by
  simpa using holonomy_eq_target_of_flat (bridge := bridge) (B := B) hFlat

omit [Fintype I] [FiniteDimensional ℝ E] in
@[deprecated holonomy_eq_chiralScale_of_flat_compat (since := "2026-04-06")]
theorem holonomy_eq_chiralScale_of_flat_of_projectorObstructionBridge
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge (CI := CI) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ = CI.chiralScale := by
  exact holonomy_eq_chiralScale_of_flat_compat
    (CI := CI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat

def finiteSumFlatCurvatureValueBridge
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (H : WeylHolonomyMap A ℝ)
    (target : ℝ)
    (hZeroToTarget :
      ∀ B : WeylGaugeField X A,
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).integrateCurvature Δ B γ = 0 →
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).holonomy H B γ = target) :
    FlatCurvatureValueBridge (Δ := Δ) (γ := γ) target where
  lineIntegrator := WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)
  holonomyMap := H
  flat_to_zeroCurvatureIntegral := by
      intro B hFlat
      exact WeylLineIntegrator.finiteSumIntegrator_integrateCurvature_eq_zero_of_flat
        (Δ := Δ) (B := B) (γ := γ) hFlat
  zeroCurvatureIntegral_to_target := by
    intro B hZero
    exact hZeroToTarget B hZero

abbrev finiteSumFlatCurvatureProjectorObstructionBridge
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (H : WeylHolonomyMap A ℝ)
    (hZeroToObstruction :
      ∀ B : WeylGaugeField X A,
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).integrateCurvature Δ B γ = 0 →
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).holonomy H B γ
          = ‖CI.projectorObstruction‖₊) :
    FlatCurvatureProjectorObstructionBridge (CI := CI) (Δ := Δ) (γ := γ) :=
  finiteSumFlatCurvatureValueBridge (Δ := Δ) (γ := γ) (H := H) (target := ‖CI.projectorObstruction‖₊)
    hZeroToObstruction

/--
Canonical finite-trajectory scalar constructor as a compatibility layer over
the operator-first bridge.
-/
def finiteSumFlatCurvatureChiralScaleBridge
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (H : WeylHolonomyMap A ℝ)
    (hZeroToChiral :
      ∀ B : WeylGaugeField X A,
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).integrateCurvature Δ B γ = 0 →
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).holonomy H B γ = CI.chiralScale) :
    FlatCurvatureChiralScaleBridge (CI := CI) (Δ := Δ) (γ := γ) := by
  let opBridge :=
    finiteSumFlatCurvatureValueBridge
      (Δ := Δ) (γ := γ) (H := H) (target := ‖CI.projectorObstruction‖₊)
      (hZeroToTarget := fun B hZero => by
        calc
          (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).holonomy H B γ
              = CI.chiralScale := hZeroToChiral B hZero
          _ = ‖CI.projectorObstruction‖₊ := CI.chiralScale_eq_projectorObstruction_nnnorm)
  exact
    FlatCurvatureChiralScaleBridge.ofProjectorObstructionBridge
      (CI := CI) (Δ := Δ) (γ := γ) opBridge

section

omit [FiniteDimensional ℝ E]

theorem finiteSum_holonomy_eq_target_of_flat
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (H : WeylHolonomyMap A ℝ)
    (target : ℝ)
    (B : WeylGaugeField X A)
    (hZeroToTarget :
      ∀ B' : WeylGaugeField X A,
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).integrateCurvature Δ B' γ = 0 →
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).holonomy H B' γ = target)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).holonomy H B γ = target := by
  let bridge := finiteSumFlatCurvatureValueBridge
    (Δ := Δ) (γ := γ) (H := H) (target := target) hZeroToTarget
  simpa [bridge] using
    holonomy_eq_target_of_flat (bridge := bridge) (B := B) hFlat

end

omit [FiniteDimensional ℝ E] in
/-- Finite-trajectory flat-curvature theorem at the operator endpoint. -/
theorem finiteSum_holonomy_eq_projectorObstruction_nnnorm_of_flat
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (H : WeylHolonomyMap A ℝ)
    (B : WeylGaugeField X A)
    (hZeroToObstruction :
      ∀ B' : WeylGaugeField X A,
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).integrateCurvature Δ B' γ = 0 →
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).holonomy H B' γ
          = ‖CI.projectorObstruction‖₊)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).holonomy H B γ
      = ‖CI.projectorObstruction‖₊ := by
  exact finiteSum_holonomy_eq_target_of_flat
    (Δ := Δ) (γ := γ) (H := H) (target := ‖CI.projectorObstruction‖₊)
    (B := B) hZeroToObstruction hFlat

section

omit [FiniteDimensional ℝ E]

/-- Finite-trajectory scalar compatibility theorem over the generic bridge. -/
theorem finiteSum_holonomy_eq_chiralScale_of_flat_compat
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (H : WeylHolonomyMap A ℝ)
    (B : WeylGaugeField X A)
    (hZeroToChiral :
      ∀ B' : WeylGaugeField X A,
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).integrateCurvature Δ B' γ = 0 →
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).holonomy H B' γ = CI.chiralScale)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).holonomy H B γ = CI.chiralScale := by
  exact finiteSum_holonomy_eq_target_of_flat
    (Δ := Δ) (γ := γ) (H := H) (target := CI.chiralScale)
    (B := B) hZeroToChiral hFlat

@[deprecated finiteSum_holonomy_eq_chiralScale_of_flat_compat (since := "2026-04-06")]
theorem finiteSum_holonomy_eq_chiralScale_of_flat
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (H : WeylHolonomyMap A ℝ)
    (B : WeylGaugeField X A)
    (hZeroToChiral :
      ∀ B' : WeylGaugeField X A,
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).integrateCurvature Δ B' γ = 0 →
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).holonomy H B' γ = CI.chiralScale)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).holonomy H B γ = CI.chiralScale := by
  exact finiteSum_holonomy_eq_chiralScale_of_flat_compat
    (CI := CI) (Δ := Δ) (γ := γ) (H := H) (B := B) hZeroToChiral hFlat

end

omit [Fintype I] [FiniteDimensional ℝ E] in
/--
Flat Weyl holonomy collapses to zero when unit relative volume forces the
conformal inference into the normal phase.
-/
theorem holonomy_eq_zero_of_flat_of_unitRelativeVolume
    {n : Nat}
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge : FlatCurvatureChiralScaleBridge (CI := CI) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B)
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = InfoGeometry.Canonical.MoE.kahlerPotentialRN n M)
    (hUnitVolume : InfoGeometry.Canonical.MoE.relativeVolumeChangeRN n M = 1) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ = 0 := by
  have hScaleZero :=
    CI.chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume
  have hHol :
      bridge.lineIntegrator.holonomy bridge.holonomyMap B γ = CI.chiralScale := by
    exact bridge.zeroCurvatureIntegral_to_target B
      (bridge.flat_to_zeroCurvatureIntegral B hFlat)
  exact hHol.trans hScaleZero

omit [Fintype I] [FiniteDimensional ℝ E] in
/--
Flat Weyl holonomy collapses to zero on the proof-carrying unit-relative-volume
branch.

This narrows the explicit hypothesis surface from the bare equality
`relativeVolumeChangeRN n M = 1` to the constructive `UnitRelativeVolumeBit`
packet while preserving `holonomy_eq_zero_of_flat_of_unitRelativeVolume` as the
compatibility theorem.
-/
theorem holonomy_eq_zero_of_flat_of_unitRelativeVolumeBit
    {n : Nat}
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge : FlatCurvatureChiralScaleBridge (CI := CI) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B)
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = InfoGeometry.Canonical.MoE.kahlerPotentialRN n M)
    (bit : InfoGeometry.Canonical.IncompressibleBitBridge.UnitRelativeVolumeBit n M) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ = 0 := by
  exact holonomy_eq_zero_of_flat_of_unitRelativeVolume
    (CI := CI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) (hFlat := hFlat)
    (M := M) hScaleFromKahler bit

omit [Fintype I] [FiniteDimensional ℝ E] in
/-- Nonvanishing case:
if Drazin and Moore-Penrose projectors do not commute, flat Weyl transport has
strictly positive holonomy at the projector-obstruction endpoint. -/
theorem holonomy_pos_of_flat_of_noncommute
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge (CI := CI) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B)
    (hNonComm : CI.P_D.comp CI.P_MP ≠ CI.P_MP.comp CI.P_D) :
    0 < bridge.lineIntegrator.holonomy bridge.holonomyMap B γ := by
  have hObsNe : CI.projectorObstruction ≠ 0 := by
    rw [CI.projectorObstruction_eq_commutator]
    exact sub_ne_zero.mpr hNonComm
  have hObsNormPos : 0 < (‖CI.projectorObstruction‖₊ : ℝ) := by
    exact NNReal.coe_pos.mpr ((nnnorm_pos).mpr hObsNe)
  have hHol :
      bridge.lineIntegrator.holonomy bridge.holonomyMap B γ = ‖CI.projectorObstruction‖₊ := by
    exact holonomy_eq_projectorObstruction_nnnorm_of_flat
      (CI := CI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat
  exact hHol.symm ▸ hObsNormPos

omit [Fintype I] [FiniteDimensional ℝ E] in
/-- Nonvanishing case (nonzero form): noncommuting Drazin/Penrose projectors
force nonzero flat Weyl holonomy. -/
theorem holonomy_ne_zero_of_flat_of_noncommute
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge :
      FlatCurvatureProjectorObstructionBridge (CI := CI) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B)
    (hNonComm : CI.P_D.comp CI.P_MP ≠ CI.P_MP.comp CI.P_D) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ ≠ 0 := by
  exact ne_of_gt <|
    holonomy_pos_of_flat_of_noncommute
      (CI := CI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat hNonComm

end InfoGeometry.Canonical.WeylTransportBridge
