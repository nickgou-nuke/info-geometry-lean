import InfoGeometry.Canonical.DeterminantCore
import InfoGeometry.Jordan.LogDet
import InfoGeometry.Canonical.SpectralInference
import InfoGeometry.Thermo.FromLogDet
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

set_option linter.unusedSectionVars false

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
Right-composition additivity for the operatorial zeta log-determinant.

No commutativity assumption is imposed on `L` and `K`; composition is the
ambient (potentially noncommutative) operator product.  The logarithmic split
requires explicit nondegeneracy of the scaled and right factors.
-/
@[rep_depth operator]
theorem operatorZetaRegularizedLogDet_mul_right
    (L K : E →L[ℝ] E) (Λ : ℝ)
    (hdetScaledL : LinearMap.det (ContinuousLinearMap.toLinearMap ((1 / Λ) • L)) ≠ 0)
    (hdetK : LinearMap.det (ContinuousLinearMap.toLinearMap K) ≠ 0) :
    operatorZetaRegularizedLogDet (E := E) (L * K) Λ
      = operatorZetaRegularizedLogDet (E := E) L Λ
        + Real.log (|LinearMap.det (ContinuousLinearMap.toLinearMap K)|) := by
  have hmul : ((1 / Λ) • (L * K)) = (((1 / Λ) • L) * K) := by
    ext x
    simp [ContinuousLinearMap.mul_def]
  calc
    operatorZetaRegularizedLogDet (E := E) (L * K) Λ
        = Real.log (|LinearMap.det (ContinuousLinearMap.toLinearMap ((1 / Λ) • (L * K)))|) := rfl
    _ = Real.log (|LinearMap.det (ContinuousLinearMap.toLinearMap ((((1 / Λ) • L : E →L[ℝ] E) * K)))|) := by
          rw [hmul]
    _ = Real.log
          (|(LinearMap.det (ContinuousLinearMap.toLinearMap (((1 / Λ) • L : E →L[ℝ] E)))
            * LinearMap.det (ContinuousLinearMap.toLinearMap (K : E →L[ℝ] E)))|) := by
          congr
          exact (LinearMap.det : (E →ₗ[ℝ] E) →* ℝ).map_mul
            (ContinuousLinearMap.toLinearMap (((1 / Λ) • L : E →L[ℝ] E)))
            (ContinuousLinearMap.toLinearMap (K : E →L[ℝ] E))
    _ = Real.log
          (|LinearMap.det (ContinuousLinearMap.toLinearMap (((1 / Λ) • L : E →L[ℝ] E)))|
            * |LinearMap.det (ContinuousLinearMap.toLinearMap (K : E →L[ℝ] E))|) := by
          rw [abs_mul]
    _ = Real.log (|LinearMap.det (ContinuousLinearMap.toLinearMap (((1 / Λ) • L : E →L[ℝ] E)))|)
        + Real.log (|LinearMap.det (ContinuousLinearMap.toLinearMap (K : E →L[ℝ] E))|) := by
          exact Real.log_mul (abs_ne_zero.mpr hdetScaledL) (abs_ne_zero.mpr hdetK)
    _ = operatorZetaRegularizedLogDet (E := E) L Λ
        + Real.log (|LinearMap.det (ContinuousLinearMap.toLinearMap (K : E →L[ℝ] E))|) := by
          rfl

/--
Left-composition additivity for the operatorial zeta log-determinant.

As in the right-composition theorem, no commutativity is assumed between the
factors; composition order is preserved explicitly.
-/
@[rep_depth operator]
theorem operatorZetaRegularizedLogDet_mul_left
    (L K : E →L[ℝ] E) (Λ : ℝ)
    (hdetK : LinearMap.det (ContinuousLinearMap.toLinearMap K) ≠ 0)
    (hdetScaledL : LinearMap.det (ContinuousLinearMap.toLinearMap ((1 / Λ) • L)) ≠ 0) :
    operatorZetaRegularizedLogDet (E := E) (K * L) Λ
      = Real.log (|LinearMap.det (ContinuousLinearMap.toLinearMap K)|)
        + operatorZetaRegularizedLogDet (E := E) L Λ := by
  have hmul : ((1 / Λ) • (K * L)) = (K * ((1 / Λ) • L)) := by
    ext x
    simp [ContinuousLinearMap.mul_def]
  calc
    operatorZetaRegularizedLogDet (E := E) (K * L) Λ
        = Real.log (|LinearMap.det (ContinuousLinearMap.toLinearMap ((1 / Λ) • (K * L)))|) := rfl
    _ = Real.log (|LinearMap.det (ContinuousLinearMap.toLinearMap ((K * ((1 / Λ) • L) : E →L[ℝ] E)))|) := by
          rw [hmul]
    _ = Real.log
          (|(LinearMap.det (ContinuousLinearMap.toLinearMap (K : E →L[ℝ] E))
            * LinearMap.det (ContinuousLinearMap.toLinearMap (((1 / Λ) • L : E →L[ℝ] E))))|) := by
          congr
          exact (LinearMap.det : (E →ₗ[ℝ] E) →* ℝ).map_mul
            (ContinuousLinearMap.toLinearMap (K : E →L[ℝ] E))
            (ContinuousLinearMap.toLinearMap (((1 / Λ) • L : E →L[ℝ] E))
)
    _ = Real.log
          (|LinearMap.det (ContinuousLinearMap.toLinearMap (K : E →L[ℝ] E))|
            * |LinearMap.det (ContinuousLinearMap.toLinearMap (((1 / Λ) • L : E →L[ℝ] E)))|) := by
          rw [abs_mul]
    _ = Real.log (|LinearMap.det (ContinuousLinearMap.toLinearMap (K : E →L[ℝ] E))|)
        + Real.log (|LinearMap.det (ContinuousLinearMap.toLinearMap (((1 / Λ) • L : E →L[ℝ] E)))|) := by
          exact Real.log_mul (abs_ne_zero.mpr hdetK) (abs_ne_zero.mpr hdetScaledL)
    _ = Real.log (|LinearMap.det (ContinuousLinearMap.toLinearMap (K : E →L[ℝ] E))|)
        + operatorZetaRegularizedLogDet (E := E) L Λ := by
          rfl

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
        + InfoGeometry.Volume.LogPotential.LogAbsVolume g :=
  InfoGeometry.Volume.LogPotential.logAbsVolume_add (f := f) (g := g)

end UniversalVolumeBridge

end InfoGeometry.Canonical.Determinant
