import Mathlib
import proofs.KANFormalization
import proofs.PrimonCuntzTower

noncomputable section

namespace InfoGeometry.Quantum.IwasawaAnalyticityLock

open scoped BigOperators

/-
Finite determinant identities for the KAN factorization used below.

The basic finite fact is algebraic: if the log determinant of the modeled KAN
operator equals a chosen additive logarithmic coordinate, then the corresponding
determinant-trace defect is zero.

The later colimit statements are parametrized by an explicit map from finite
defects to the selected limit object.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite log determinant of the modeled KAN transfer operator. -/
def logDet (F : InfoGeometry.Quantum.KANFormalization.KANFactor ι) : ℝ :=
  Real.log (Matrix.det (InfoGeometry.Quantum.KANFormalization.KANFactor.total F))

/--
Finite determinant-trace defect.

`spectralLogScale` is an additive logarithmic coordinate.  The defect vanishes
exactly when `log ∘ det` agrees with that coordinate.
-/
def traceDefect (F : InfoGeometry.Quantum.KANFormalization.KANFactor ι)
    (spectralLogScale : ℝ) : ℝ :=
  logDet F - spectralLogScale

/-- Finite bridge: an explicit log-det equality annihilates the trace defect. -/
theorem traceDefect_eq_zero_of_log_bridge
    (F : InfoGeometry.Quantum.KANFormalization.KANFactor ι)
    (spectralLogScale : ℝ)
    (hlog : logDet F = spectralLogScale) :
    traceDefect F spectralLogScale = 0 := by
  simp [traceDefect, hlog]

/--
Finite sequence of determinant-trace defects, together with two algebraic facts:
every finite defect is zero and consecutive defects agree.
-/
structure FiniteTraceDefectModel where
  defect : ℕ → ℝ
  defect_zero : ∀ n, defect n = 0
  defect_compatible : ∀ n, defect (n + 1) = defect n

/-- The finite lock is just the recorded zero-defect theorem. -/
theorem finite_iwasawa_analyticity_lock (M : FiniteTraceDefectModel) :
    ∀ n, M.defect n = 0 :=
  M.defect_zero

/--
Colimit-style limit object for determinant-trace defects.

The limit defect is specified by a finite-stage defect through a linear map into
the selected limit space.  With this representation, finite zero-defect
transports directly to the limit.
-/
structure IwasawaAnalyticityLimit (M : FiniteTraceDefectModel) where
  Limit : Type*
  [hAdd : AddCommGroup Limit]
  [hModule : Module ℝ Limit]
  inc : ℕ → (ℝ →ₗ[ℝ] Limit)
  colimitDefect : Limit
  repStage : ℕ
  hRepresent : colimitDefect = inc repStage (M.defect repStage)

attribute [instance] IwasawaAnalyticityLimit.hAdd IwasawaAnalyticityLimit.hModule

/--
Colimit transport theorem for the Iwasawa analyticity defect.

The limit defect is reduced to a finite stage, where it is zero, and linearity
maps that zero value into the limit space.
-/
theorem iwasawa_analyticity_limit_lock
    (M : FiniteTraceDefectModel)
    (L : IwasawaAnalyticityLimit M) :
    L.colimitDefect = 0 := by
  rw [L.hRepresent, M.defect_zero L.repStage]
  exact (L.inc L.repStage).map_zero

/--
Colimit data for determinant-trace defects.

The structure records a real-valued limit defect together with the implication
from vanishing finite defects to vanishing of that limit defect.
-/
structure ColimitTraceDefectModel extends FiniteTraceDefectModel where
  colimitDefect : ℝ
  colimit_eq_zero_of_finite_zero :
    (∀ n, defect n = 0) → colimitDefect = 0

/--
Iwasawa analyticity statement for a supplied colimit defect model.
-/
theorem infinite_iwasawa_analyticity_lock (M : ColimitTraceDefectModel) :
    M.colimitDefect = 0 :=
  M.colimit_eq_zero_of_finite_zero M.defect_zero

namespace PrimonCuntz

/-- Additive logarithmic coordinate of the finite Primon/Cuntz KAN stage. -/
def spectralLogScale (n : ℕ) : ℝ :=
  ∑ i : Fin (n + 1), Real.log ((i.1 + 1 : ℝ))

/-- Finite Primon/Cuntz determinant-trace defect. -/
def defect (n : ℕ) : ℝ :=
  traceDefect (InfoGeometry.Quantum.PrimonCuntzTower.primonCuntzKANFactor n)
    (spectralLogScale n)

/-- The finite Primon/Cuntz KAN bridge has zero determinant-trace defect. -/
theorem defect_zero (n : ℕ) : defect n = 0 := by
  apply traceDefect_eq_zero_of_log_bridge
  exact InfoGeometry.Quantum.PrimonCuntzTower.primonCuntz_tower_kan_log_bridge n

/-- Compatibility of the Primon/Cuntz defects across one stage. -/
theorem defect_compatible (n : ℕ) : defect (n + 1) = defect n := by
  rw [defect_zero (n + 1), defect_zero n]

/-- Finite Primon/Cuntz trace-defect model. -/
def finiteTraceDefectModel : FiniteTraceDefectModel :=
  { defect := defect
  , defect_zero := defect_zero
  , defect_compatible := defect_compatible }

/--
Concrete colimit presentation for the Primon/Cuntz defect.

The limit defect is represented in the limit space `ℝ` by its finite defect at
stage 0, and the finite zero-defect theorem supplies the value.
-/
def finite_iwasawa_colimit_trivial : IwasawaAnalyticityLimit finiteTraceDefectModel :=
  { Limit := ℝ
    , inc := fun _ => LinearMap.id
    , colimitDefect := 0
    , repStage := 0
    , hRepresent := by
        simpa [finiteTraceDefectModel] using (defect_zero 0).symm }

/-- Concrete specialization of the abstract colimit lock theorem. -/
theorem primon_iwasawa_analyticity_limit_lock_trivial :
    (finite_iwasawa_colimit_trivial.colimitDefect) = 0 :=
  iwasawa_analyticity_limit_lock finiteTraceDefectModel finite_iwasawa_colimit_trivial

/-- Finite Primon/Cuntz Iwasawa analyticity lock. -/
theorem primon_finite_iwasawa_analyticity_lock :
    ∀ n, defect n = 0 :=
  InfoGeometry.Quantum.IwasawaAnalyticityLock.finite_iwasawa_analyticity_lock
    finiteTraceDefectModel

/-- Colimit-style transport of the Primon/Cuntz analyticity lock. -/
theorem primon_iwasawa_analyticity_limit_lock
    (L : IwasawaAnalyticityLimit finiteTraceDefectModel) :
    L.colimitDefect = 0 :=
  InfoGeometry.Quantum.IwasawaAnalyticityLock.iwasawa_analyticity_limit_lock
    finiteTraceDefectModel L

/-- A Primon/Cuntz colimit defect model vanishes when its finite defects are the
Primon/Cuntz finite defects. -/
theorem colimit_iwasawa_analyticity_lock
    (M : ColimitTraceDefectModel)
    (hdefect : ∀ n, M.defect n = defect n) :
    M.colimitDefect = 0 := by
  apply M.colimit_eq_zero_of_finite_zero
  intro n
  rw [hdefect n, defect_zero n]

end PrimonCuntz

end InfoGeometry.Quantum.IwasawaAnalyticityLock
