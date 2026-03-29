import InfoGeometry.Canonical.DeterminantCore
import InfoGeometry.Canonical.LogDet
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Canonical.ThermoFromLogDet
import InfoGeometry.Volume.LogPotential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# InfoGeometry.Canonical.ZetaDeterminant

Initial canonical zeta-determinant layer.

This finite-dimensional start identifies the zeta-regularized determinant/log-
determinant with the absolute determinant and `logAbsDet` on `GL(ℝ)`.
It also provides SPD/log-det and thermodynamic aliases so existing determinant-
thermo bridges can be reused through a zeta entrypoint.
-/

namespace InfoGeometry.Canonical.Determinant

universe v

section GLReal

variable {V : Type v} [Fintype V] [DecidableEq V]

/-- Finite-dimensional zeta-regularized determinant on `GL(ℝ)`. -/
noncomputable def zetaRegularizedDet (g : «GL» ℝ V) : ℝ :=
  |((jacDet ℝ V g : ℝˣ) : ℝ)|

/-- Finite-dimensional zeta-regularized logarithmic determinant. -/
noncomputable def zetaRegularizedLogDet (g : «GL» ℝ V) : ℝ :=
  Real.log (zetaRegularizedDet (V := V) g)

lemma zetaRegularizedDet_pos (g : «GL» ℝ V) :
    0 < zetaRegularizedDet (V := V) g := by
  unfold zetaRegularizedDet jacDet
  exact abs_pos.mpr (Units.ne_zero _)

@[simp] lemma zetaRegularizedLogDet_eq_logAbsDet (g : «GL» ℝ V) :
    zetaRegularizedLogDet (V := V) g = logAbsDet V g := rfl

/-- Multiplicativity of the finite-dimensional zeta log-determinant. -/
theorem zetaRegularizedLogDet_mul (f g : «GL» ℝ V) :
    zetaRegularizedLogDet (V := V) (f * g)
      = zetaRegularizedLogDet (V := V) f + zetaRegularizedLogDet (V := V) g := by
  have hf0 : zetaRegularizedDet (V := V) f ≠ 0 :=
    (zetaRegularizedDet_pos (V := V) f).ne'
  have hg0 : zetaRegularizedDet (V := V) g ≠ 0 :=
    (zetaRegularizedDet_pos (V := V) g).ne'
  calc
    zetaRegularizedLogDet (V := V) (f * g)
        = Real.log (zetaRegularizedDet (V := V) (f * g)) := rfl
    _ = Real.log (zetaRegularizedDet (V := V) f * zetaRegularizedDet (V := V) g) := by
          unfold zetaRegularizedDet jacDet
          rw [(detHom ℝ V).map_mul]
          simp [Units.val_mul, abs_mul]
    _ = Real.log (zetaRegularizedDet (V := V) f)
        + Real.log (zetaRegularizedDet (V := V) g) := by
          exact Real.log_mul hf0 hg0
    _ = zetaRegularizedLogDet (V := V) f + zetaRegularizedLogDet (V := V) g := by
          rfl

end GLReal

section OperatorSpectral

variable {E : Type _}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Operator-level zeta regularized log-determinant at cutoff `Λ`. -/
noncomputable def operatorZetaRegularizedLogDet
    (L : E →L[ℝ] E) (Λ : ℝ) : ℝ :=
  Real.log (|LinearMap.det (ContinuousLinearMap.toLinearMap ((1 / Λ) • L))|)

/--
Regularized operator/spectral zeta package.

`regularizedOp` is the regularized operator input (e.g. Drazin inverse or a
shifted variant), and `cutoff` is the spectral scale.
-/
structure SpectralZetaLogDetData where
  regularizedOp : E →L[ℝ] E
  cutoff : ℝ
  cutoff_ne_zero : cutoff ≠ 0

namespace SpectralZetaLogDetData

/-- Extract the regularized zeta log-determinant represented by the package. -/
noncomputable def logDet (pkg : SpectralZetaLogDetData (E := E)) : ℝ :=
  operatorZetaRegularizedLogDet (E := E) pkg.regularizedOp pkg.cutoff

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem logDet_eq
    (pkg : SpectralZetaLogDetData (E := E)) :
    pkg.logDet = operatorZetaRegularizedLogDet (E := E) pkg.regularizedOp pkg.cutoff := rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem cutoff_ne_zero'
    (pkg : SpectralZetaLogDetData (E := E)) :
    pkg.cutoff ≠ 0 :=
  pkg.cutoff_ne_zero

end SpectralZetaLogDetData

/-- Canonical zeta package extracted from a regularized spectral triple. -/
noncomputable def spectralZetaLogDetDataOfRegularizedTriple
    (RST : InfoGeometry.Canonical.SpectralInference.RegularizedSpectralTriple E)
    (Λ : ℝ) (hΛ : Λ ≠ 0) : SpectralZetaLogDetData (E := E) where
  regularizedOp := RST.DD
  cutoff := Λ
  cutoff_ne_zero := hΛ

omit [FiniteDimensional ℝ E] in
@[simp] theorem spectralZetaLogDetDataOfRegularizedTriple_logDet
    (RST : InfoGeometry.Canonical.SpectralInference.RegularizedSpectralTriple E)
    (Λ : ℝ) (hΛ : Λ ≠ 0) :
    (spectralZetaLogDetDataOfRegularizedTriple (E := E) RST Λ hΛ).logDet
      = InfoGeometry.Canonical.SpectralInference.RegularizedSpectralTriple.spectralAction
          (RST := RST) Λ := rfl

/-- Canonical zeta package extracted from a chiral regularized spectral triple. -/
noncomputable def spectralZetaLogDetDataOfChiralTriple
    (CST : InfoGeometry.Canonical.SpectralInference.ChiralSpectralTriple E)
    (Λ : ℝ) (hΛ : Λ ≠ 0) : SpectralZetaLogDetData (E := E) where
  regularizedOp :=
    CST.DD + InfoGeometry.Canonical.SpectralInference.ChiralSpectralTriple.epsilon CST • 1
  cutoff := Λ
  cutoff_ne_zero := hΛ

omit [FiniteDimensional ℝ E] in
@[simp] theorem spectralZetaLogDetDataOfChiralTriple_logDet
    (CST : InfoGeometry.Canonical.SpectralInference.ChiralSpectralTriple E)
    (Λ : ℝ) (hΛ : Λ ≠ 0) :
    (spectralZetaLogDetDataOfChiralTriple (E := E) CST Λ hΛ).logDet
      = InfoGeometry.Canonical.SpectralInference.ChiralSpectralTriple.chiralSpectralAction
          (CST := CST) Λ := rfl

end OperatorSpectral

section SPDReal

variable {n : ℕ}

/-- SPD zeta-log-det barrier (canonical alias to the existing log-det barrier). -/
noncomputable abbrev zetaLogDetBarrier (X : InfoGeometry.Jordan.SPD n) : ℝ :=
  InfoGeometry.Jordan.logDetBarrier X

@[simp] theorem zetaLogDetBarrier_eq_logDetBarrier
    (X : InfoGeometry.Jordan.SPD n) :
    zetaLogDetBarrier X = InfoGeometry.Jordan.logDetBarrier X := rfl

/-- Thermodynamic zeta-energy alias induced by the Burg/log-det geometry. -/
noncomputable abbrev zetaEnergyFromLogDet
    {Ω : Type _} [Fintype Ω]
    (X0 : InfoGeometry.Jordan.SPD n) (X : Ω → InfoGeometry.Jordan.SPD n) : Ω → ℝ :=
  InfoGeometry.Thermo.energyFromLogDet (X0 := X0) X

end SPDReal

section UniversalVolumeBridge

variable {W : Type _} [AddCommGroup W] [Module ℝ W]

/-- Zeta entrypoint for the universal additive log-volume potential. -/
noncomputable def zetaRegularizedLogVolume (g : W ≃ₗ[ℝ] W) : ℝ :=
  Real.log (|((InfoGeometry.Volume.Base.VolumeHom g : ℝˣ) : ℝ)|)

@[simp] theorem zetaRegularizedLogVolume_eq_logAbsVolume
    (g : W ≃ₗ[ℝ] W) :
    zetaRegularizedLogVolume (W := W) g =
      InfoGeometry.Volume.LogPotential.LogAbsVolume g := rfl

theorem zetaRegularizedLogVolume_add
    (f g : W ≃ₗ[ℝ] W) :
    zetaRegularizedLogVolume (W := W) (f.trans g)
      = zetaRegularizedLogVolume (W := W) f + zetaRegularizedLogVolume (W := W) g := by
  simpa [zetaRegularizedLogVolume, InfoGeometry.Volume.LogPotential.LogAbsVolume] using
    (InfoGeometry.Volume.LogPotential.logAbsVolume_add (f := f) (g := g))

/-- Capstone-facing bridge: discharge universal log-volume additivity from zeta API. -/
theorem capstone_logAbsVolume_add_from_zeta
    (f g : W ≃ₗ[ℝ] W) :
    InfoGeometry.Volume.LogPotential.LogAbsVolume (f.trans g)
      = InfoGeometry.Volume.LogPotential.LogAbsVolume f
        + InfoGeometry.Volume.LogPotential.LogAbsVolume g := by
  simpa [zetaRegularizedLogVolume_eq_logAbsVolume (W := W)] using
    (zetaRegularizedLogVolume_add (W := W) (f := f) (g := g))

end UniversalVolumeBridge

end InfoGeometry.Canonical.Determinant
