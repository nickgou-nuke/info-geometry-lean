import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.KANFormalization
import InfoGeometry.External.Auto.PrimonCuntzTower

noncomputable section

namespace InfoGeometry.Quantum.IwasawaAnalyticityLock

open scoped BigOperators

/-
This file records the conservative version of the "analyticity lock" vocabulary.

The finite theorem is genuine: if the finite KAN log-determinant equals the
modeled spectral/log-scale coordinate, then the determinant-trace defect is zero.

The infinite theorem is deliberately packaged as a certificate.  It states the
exact remaining obligation: zero finite defects must pass to the chosen colimit
or regularized determinant interface.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite log determinant of the modeled KAN transfer operator. -/
def logDet (F : InfoGeometry.Quantum.KANFormalization.KANFactor ι) : ℝ :=
  Real.log (Matrix.det (InfoGeometry.Quantum.KANFormalization.KANFactor.total F))

/--
Finite determinant-trace defect.

`spectralLogScale` is the additive logarithmic coordinate carried by the modeled
Hamiltonian/spectrum.  The defect vanishes exactly when `log ∘ det` agrees with
that additive coordinate.
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
Finite sequence of determinant-trace defects, together with the two local facts
needed before any infinite passage: every finite defect is zero and the defects
are compatible across the stage maps.
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

This mirrors the transport pattern used in `DiracColimit`: the global defect is
not evaluated by an infinite determinant here.  Instead, it is represented by a
finite-stage defect through a linear inclusion into the selected limit defect
space.  Once represented, finite zero-defect immediately transports to the
limit.
-/
structure IwasawaAnalyticityLimit (M : FiniteTraceDefectModel) where
  Limit : Type*
  [hAdd : AddCommGroup Limit]
  [hModule : Module ℝ Limit]
  inc : ℕ → (ℝ →ₗ[ℝ] Limit)
  colimitDefect : Limit
  hRepresent : ∃ n, colimitDefect = inc n (M.defect n)

attribute [instance] IwasawaAnalyticityLimit.hAdd IwasawaAnalyticityLimit.hModule

/--
Colimit transport theorem for the Iwasawa analyticity defect.

This is the direct analogue of the old Dirac colimit proof: pull the global
quantity back to a finite stage, use the finite-stage theorem, then push the
zero result forward through the inclusion.
-/
theorem iwasawa_analyticity_limit_lock
    (M : FiniteTraceDefectModel)
    (L : IwasawaAnalyticityLimit M) :
    L.colimitDefect = 0 := by
  rcases L.hRepresent with ⟨n, hrep⟩
  rw [hrep, M.defect_zero n]
  exact (L.inc n).map_zero

/--
Colimit certificate for the analytic lock.

This is the honest infinite interface: a construction of a colimit or
regularized determinant must provide the global defect and prove that the
vanishing compatible finite defects pass to it.
-/
structure ColimitTraceDefectModel extends FiniteTraceDefectModel where
  colimitDefect : ℝ
  colimit_eq_zero_of_finite_zero :
    (∀ n, defect n = 0) → colimitDefect = 0

/--
Infinite Iwasawa analyticity lock, conditional only on the explicit colimit
certificate above.  No infinite determinant or trace-class theorem is smuggled in.
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
Concrete one-line colimit presentation for the Primon/Cuntz defect.

The global defect is represented in the limit space `ℝ` by its finite defect at
stage 0; because finite defects are zero, this concrete model transports the
zero result immediately to the colimit style field.
-/
def finite_iwasawa_colimit_trivial : IwasawaAnalyticityLimit finiteTraceDefectModel :=
  { Limit := ℝ
    , inc := fun _ => LinearMap.id
    , colimitDefect := 0
    , hRepresent := by
        refine ⟨0, ?_⟩
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

/--
If a chosen infinite Primon/Cuntz colimit determinant interface is supplied,
the global determinant-trace defect vanishes.
-/
theorem colimit_iwasawa_analyticity_lock
    (colimitDefect : ℝ)
    (hpass : (∀ n, defect n = 0) → colimitDefect = 0) :
    colimitDefect = 0 := by
  exact hpass defect_zero

end PrimonCuntz

end InfoGeometry.Quantum.IwasawaAnalyticityLock
