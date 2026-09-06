import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Krein.PolarizedSector
import InfoGeometry.Cartan.Involution
import InfoGeometry.Meta.Architecture
import Mathlib.Tactic.NoncommRing

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.GeneralizedMetricCore

Minimal doubled-carrier owner surface for generalized-metric style data.

This file stays at the doubled/Krein level:

- a split involution `η`,
- an involutive polarization `S`,
- the induced metric-like operator `G = η ∘ S`,
- plus/minus projectors attached to `S`,
- exact canonical specialization to the repo's `(J, ε, Jε)` split atom.
-/

namespace InfoGeometry.Canonical.GeneralizedMetricCore

open InfoGeometry.Cartan
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Krein
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Krein.SplitQuadraticSheets

section Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "H2" => InfoGeometry.Krein.DoubledSpace H
local notation "EndH" => H2 →L[ℝ] H2
local notation "IdH" => ContinuousLinearMap.id ℝ H2

/-- Minimal doubled-carrier generalized-metric seed. -/
structure GeneralizedMetricSeed
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  eta : InfoGeometry.Krein.DoubledSpace H →L[ℝ] InfoGeometry.Krein.DoubledSpace H
  polarization : InfoGeometry.Krein.DoubledSpace H →L[ℝ] InfoGeometry.Krein.DoubledSpace H
  metricOperator : InfoGeometry.Krein.DoubledSpace H →L[ℝ] InfoGeometry.Krein.DoubledSpace H
  eta_sq : eta.comp eta = ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace H)
  polarization_sq :
    polarization.comp polarization =
      ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace H)
  eta_polarization_anticommute : eta.comp polarization = -(polarization.comp eta)
  metric_eq_eta_comp_polarization : metricOperator = eta.comp polarization

/-- The `+1` projector induced by the generalized-metric polarization. -/
@[rep_depth krein]
noncomputable def GeneralizedMetricSeed.plusProjector (G : GeneralizedMetricSeed H) : EndH :=
  (⅟ (2 : ℝ)) • (ContinuousLinearMap.id ℝ H2 + G.polarization)

/-- The `-1` projector induced by the generalized-metric polarization. -/
@[rep_depth krein]
noncomputable def GeneralizedMetricSeed.minusProjector (G : GeneralizedMetricSeed H) : EndH :=
  (⅟ (2 : ℝ)) • (ContinuousLinearMap.id ℝ H2 - G.polarization)

/-- The polarization defines a Cartan involution on the doubled carrier. -/
theorem GeneralizedMetricSeed.polarization_is_cartan
    (G : GeneralizedMetricSeed H) :
    IsCartanInvolution G.polarization.toLinearMap := by
  exact congrArg ContinuousLinearMap.toLinearMap G.polarization_sq

@[rep_depth krein] theorem GeneralizedMetricSeed.plusProjector_idempotent
    (G : GeneralizedMetricSeed H) :
    (GeneralizedMetricSeed.plusProjector G).comp (GeneralizedMetricSeed.plusProjector G)
      = GeneralizedMetricSeed.plusProjector G := by
  apply ContinuousLinearMap.ext
  intro u
  have h :=
    LinearMap.congr_fun
      (Pplus_idempotent G.polarization.toLinearMap G.polarization_is_cartan) u
  simp [GeneralizedMetricSeed.plusProjector, Pplus] at h ⊢
  exact h

@[rep_depth krein] theorem GeneralizedMetricSeed.minusProjector_idempotent
    (G : GeneralizedMetricSeed H) :
    (GeneralizedMetricSeed.minusProjector G).comp (GeneralizedMetricSeed.minusProjector G)
      = GeneralizedMetricSeed.minusProjector G := by
  apply ContinuousLinearMap.ext
  intro u
  have h :=
    LinearMap.congr_fun
      (Pminus_idempotent G.polarization.toLinearMap G.polarization_is_cartan) u
  simp only [GeneralizedMetricSeed.minusProjector, Pminus, ContinuousLinearMap.comp_apply] at h ⊢
  exact h

@[rep_depth krein] theorem GeneralizedMetricSeed.plusProjector_add_minusProjector
    (G : GeneralizedMetricSeed H) :
    GeneralizedMetricSeed.plusProjector G + GeneralizedMetricSeed.minusProjector G = IdH := by
  apply ContinuousLinearMap.ext
  intro u
  have h :=
    LinearMap.congr_fun (Pplus_add_Pminus_eq_id G.polarization.toLinearMap) u
  simp [GeneralizedMetricSeed.plusProjector, GeneralizedMetricSeed.minusProjector,
    Pplus, Pminus, ContinuousLinearMap.add_apply] at h ⊢
  exact h

@[rep_depth krein] theorem GeneralizedMetricSeed.plusProjector_comp_minusProjector
    (G : GeneralizedMetricSeed H) :
    (GeneralizedMetricSeed.plusProjector G).comp (GeneralizedMetricSeed.minusProjector G) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have h :=
    LinearMap.congr_fun
      (Pplus_comp_Pminus G.polarization.toLinearMap G.polarization_is_cartan) u
  simp only [GeneralizedMetricSeed.plusProjector, GeneralizedMetricSeed.minusProjector,
    Pplus, Pminus, ContinuousLinearMap.comp_apply, sub_eq_add_neg, smul_add] at h ⊢
  abel_nf at h ⊢
  exact h

@[rep_depth krein] theorem GeneralizedMetricSeed.decompose
    (G : GeneralizedMetricSeed H) (u : H2) :
    u = GeneralizedMetricSeed.plusProjector G u + GeneralizedMetricSeed.minusProjector G u := by
  have h := congrArg (fun F : EndH => F u) (GeneralizedMetricSeed.plusProjector_add_minusProjector G)
  simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply] using h.symm

@[rep_depth krein] theorem GeneralizedMetricSeed.polarization_comp_plusProjector
    (G : GeneralizedMetricSeed H) :
    G.polarization.comp (GeneralizedMetricSeed.plusProjector G)
      = GeneralizedMetricSeed.plusProjector G := by
  apply ContinuousLinearMap.ext
  intro u
  have hs : G.polarization (G.polarization u) = u := by
    have h := congrArg (fun F : EndH => F u) G.polarization_sq
    simpa [ContinuousLinearMap.comp_apply] using h
  calc
    G.polarization (GeneralizedMetricSeed.plusProjector G u)
        = (⅟ (2 : ℝ)) • (G.polarization u + G.polarization (G.polarization u)) := by
            simp [GeneralizedMetricSeed.plusProjector]
    _ = (⅟ (2 : ℝ)) • (u + G.polarization u) := by rw [hs]; simp [add_comm]
    _ = GeneralizedMetricSeed.plusProjector G u := by
          simp [GeneralizedMetricSeed.plusProjector, add_comm]

@[rep_depth krein] theorem GeneralizedMetricSeed.polarization_comp_minusProjector
    (G : GeneralizedMetricSeed H) :
    G.polarization.comp (GeneralizedMetricSeed.minusProjector G)
      = -(GeneralizedMetricSeed.minusProjector G) := by
  apply ContinuousLinearMap.ext
  intro u
  have hs : G.polarization (G.polarization u) = u := by
    have h := congrArg (fun F : EndH => F u) G.polarization_sq
    simpa [ContinuousLinearMap.comp_apply] using h
  calc
    G.polarization (GeneralizedMetricSeed.minusProjector G u)
        = (⅟ (2 : ℝ)) • (G.polarization u - G.polarization (G.polarization u)) := by
            simp [GeneralizedMetricSeed.minusProjector]
    _ = (⅟ (2 : ℝ)) • (G.polarization u - u) := by rw [hs]
    _ = -(GeneralizedMetricSeed.minusProjector G u) := by
          simp [GeneralizedMetricSeed.minusProjector, sub_eq_add_neg, add_comm]

@[rep_depth krein] theorem GeneralizedMetricSeed.eta_comp_plusProjector
    (G : GeneralizedMetricSeed H) :
    G.eta.comp (GeneralizedMetricSeed.plusProjector G)
      = (GeneralizedMetricSeed.minusProjector G).comp G.eta := by
  apply ContinuousLinearMap.ext
  intro u
  have hanti :
      G.eta (G.polarization u) = -(G.polarization (G.eta u)) := by
    have h := congrArg (fun F : EndH => F u) G.eta_polarization_anticommute
    simpa [ContinuousLinearMap.comp_apply] using h
  calc
    G.eta (GeneralizedMetricSeed.plusProjector G u)
        = (⅟ (2 : ℝ)) • (G.eta u + G.eta (G.polarization u)) := by
            simp [GeneralizedMetricSeed.plusProjector]
    _ = (⅟ (2 : ℝ)) • (G.eta u - G.polarization (G.eta u)) := by
          rw [hanti]
          rw [smul_sub]
          simp [sub_eq_add_neg]
    _ = GeneralizedMetricSeed.minusProjector G (G.eta u) := by
          rfl

@[rep_depth krein] theorem GeneralizedMetricSeed.eta_comp_minusProjector
    (G : GeneralizedMetricSeed H) :
    G.eta.comp (GeneralizedMetricSeed.minusProjector G)
      = (GeneralizedMetricSeed.plusProjector G).comp G.eta := by
  apply ContinuousLinearMap.ext
  intro u
  have hanti :
      G.eta (G.polarization u) = -(G.polarization (G.eta u)) := by
    have h := congrArg (fun F : EndH => F u) G.eta_polarization_anticommute
    simpa [ContinuousLinearMap.comp_apply] using h
  calc
    G.eta (GeneralizedMetricSeed.minusProjector G u)
        = (⅟ (2 : ℝ)) • (G.eta u - G.eta (G.polarization u)) := by
            simp [GeneralizedMetricSeed.minusProjector]
    _ = (⅟ (2 : ℝ)) • (G.eta u + G.polarization (G.eta u)) := by
          rw [hanti]
          simp
    _ = GeneralizedMetricSeed.plusProjector G (G.eta u) := by
          simp [GeneralizedMetricSeed.plusProjector]

@[rep_depth krein, simp] theorem GeneralizedMetricSeed.eta_comp_metric_eq_polarization
    (G : GeneralizedMetricSeed H) :
    G.eta.comp G.metricOperator = G.polarization := by
  rw [G.metric_eq_eta_comp_polarization, ← ContinuousLinearMap.comp_assoc, G.eta_sq,
    ContinuousLinearMap.id_comp]

@[rep_depth krein, simp] theorem GeneralizedMetricSeed.metric_comp_polarization_eq_eta
    (G : GeneralizedMetricSeed H) :
    G.metricOperator.comp G.polarization = G.eta := by
  calc
    G.metricOperator.comp G.polarization = (G.eta.comp G.polarization).comp G.polarization := by
      rw [G.metric_eq_eta_comp_polarization]
    _ = G.eta.comp (G.polarization.comp G.polarization) := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = G.eta := by
      rw [G.polarization_sq, ContinuousLinearMap.comp_id]

@[rep_depth krein, simp] theorem GeneralizedMetricSeed.polarization_comp_eta_eq_neg_eta_comp_polarization
    (G : GeneralizedMetricSeed H) :
    G.polarization.comp G.eta = -(G.eta.comp G.polarization) := by
  calc
    G.polarization.comp G.eta = -(-(G.polarization.comp G.eta)) := by simp
    _ = -(G.eta.comp G.polarization) := by rw [G.eta_polarization_anticommute]

@[rep_depth krein, simp] theorem GeneralizedMetricSeed.polarization_comp_metric_eq_neg_eta
    (G : GeneralizedMetricSeed H) :
    G.polarization.comp G.metricOperator = -G.eta := by
  apply ContinuousLinearMap.ext
  intro u
  have hs : G.polarization (G.polarization u) = u := by
    have h := congrArg (fun F : EndH => F u) G.polarization_sq
    simpa [ContinuousLinearMap.comp_apply] using h
  have hanti :
      G.polarization (G.eta (G.polarization u))
        = -(G.eta (G.polarization (G.polarization u))) := by
    calc
      G.polarization (G.eta (G.polarization u))
          = (G.polarization.comp G.eta) (G.polarization u) := by
              rfl
      _ = (-(G.eta.comp G.polarization)) (G.polarization u) := by
            rw [GeneralizedMetricSeed.polarization_comp_eta_eq_neg_eta_comp_polarization]
      _ = -(G.eta (G.polarization (G.polarization u))) := by
            simp [ContinuousLinearMap.comp_apply]
  calc
    G.polarization (G.metricOperator u)
        = G.polarization (G.eta (G.polarization u)) := by
            rw [G.metric_eq_eta_comp_polarization]
            rfl
    _ = -(G.eta (G.polarization (G.polarization u))) := by
          exact hanti
    _ = -(G.eta u) := by rw [hs]

@[rep_depth krein] theorem GeneralizedMetricSeed.metric_sq_eq_neg_id
    (G : GeneralizedMetricSeed H) :
    G.metricOperator.comp G.metricOperator = -IdH := by
  calc
    G.metricOperator.comp G.metricOperator
        = (G.eta.comp G.polarization).comp (G.eta.comp G.polarization) := by
            rw [G.metric_eq_eta_comp_polarization]
    _ = (G.eta.comp (G.polarization.comp G.eta)).comp G.polarization := by
          apply ContinuousLinearMap.ext
          intro u
          have h₁ :
              G.polarization (G.eta (G.polarization u))
                = -(G.eta (G.polarization (G.polarization u))) := by
            calc
              G.polarization (G.eta (G.polarization u))
                  = (G.polarization.comp G.eta) (G.polarization u) := by
                      rfl
              _ = (-(G.eta.comp G.polarization)) (G.polarization u) := by
                    rw [G.polarization_comp_eta_eq_neg_eta_comp_polarization]
              _ = -(G.eta (G.polarization (G.polarization u))) := by
                    simp [ContinuousLinearMap.comp_apply]
          have h₂ :
              G.eta (G.polarization (G.eta (G.polarization u)))
                = G.eta (-(G.eta (G.polarization (G.polarization u)))) := by
            exact congrArg G.eta h₁
          simpa [ContinuousLinearMap.comp_apply] using h₂
    _ = (G.eta.comp (-(G.eta.comp G.polarization))).comp G.polarization := by
          rw [G.polarization_comp_eta_eq_neg_eta_comp_polarization]
    _ = -((G.eta.comp (G.eta.comp G.polarization)).comp G.polarization) := by
          apply ContinuousLinearMap.ext
          intro u
          simp [ContinuousLinearMap.comp_apply]
    _ = -((G.eta.comp G.eta).comp (G.polarization.comp G.polarization)) := by
          rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc,
            ContinuousLinearMap.comp_assoc]
    _ = -IdH := by
          calc
            -((G.eta.comp G.eta).comp (G.polarization.comp G.polarization))
                = -((ContinuousLinearMap.id ℝ H2).comp (ContinuousLinearMap.id ℝ H2)) := by
                    rw [G.eta_sq, G.polarization_sq]
            _ = -IdH := by
                  rw [ContinuousLinearMap.id_comp]

@[rep_depth krein] theorem GeneralizedMetricSeed.metric_conjugates_eta
    (G : GeneralizedMetricSeed H) :
    (G.metricOperator.comp G.eta).comp G.metricOperator = G.eta := by
  have hmetric_eta : G.metricOperator.comp G.eta = -G.polarization := by
    calc
      G.metricOperator.comp G.eta = (G.eta.comp G.polarization).comp G.eta := by
        rw [G.metric_eq_eta_comp_polarization]
      _ = G.eta.comp (G.polarization.comp G.eta) := by
        rw [ContinuousLinearMap.comp_assoc]
      _ = G.eta.comp (-(G.eta.comp G.polarization)) := by
        rw [G.polarization_comp_eta_eq_neg_eta_comp_polarization]
      _ = -(G.eta.comp (G.eta.comp G.polarization)) := by
        apply ContinuousLinearMap.ext
        intro u
        simp [ContinuousLinearMap.comp_apply]
      _ = -((G.eta.comp G.eta).comp G.polarization) := by
        rw [← ContinuousLinearMap.comp_assoc]
      _ = -G.polarization := by
        rw [G.eta_sq, ContinuousLinearMap.id_comp]
  calc
    (G.metricOperator.comp G.eta).comp G.metricOperator = (-G.polarization).comp G.metricOperator := by
      rw [hmetric_eta]
    _ = -(G.polarization.comp G.metricOperator) := by
          apply ContinuousLinearMap.ext
          intro u
          simp
    _ = -(G.polarization.comp (G.eta.comp G.polarization)) := by
          rw [G.metric_eq_eta_comp_polarization]
    _ = -((G.polarization.comp G.eta).comp G.polarization) := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = -((-(G.eta.comp G.polarization)).comp G.polarization) := by
          rw [G.polarization_comp_eta_eq_neg_eta_comp_polarization]
    _ = (G.eta.comp G.polarization).comp G.polarization := by
          apply ContinuousLinearMap.ext
          intro u
          simp [ContinuousLinearMap.comp_apply]
    _ = G.eta.comp (G.polarization.comp G.polarization) := by
          rw [← ContinuousLinearMap.comp_assoc]
    _ = G.eta := by
          rw [G.polarization_sq, ContinuousLinearMap.comp_id]

@[rep_depth krein] theorem GeneralizedMetricSeed.metric_comp_plusProjector
    (G : GeneralizedMetricSeed H) :
    G.metricOperator.comp (GeneralizedMetricSeed.plusProjector G)
      = (GeneralizedMetricSeed.minusProjector G).comp G.metricOperator := by
  apply ContinuousLinearMap.ext
  intro u
  have hmetric_pol :
      G.metricOperator (G.polarization u) = G.eta u := by
    calc
      G.metricOperator (G.polarization u)
          = (G.metricOperator.comp G.polarization) u := by
              rfl
      _ = G.eta u := by
            rw [GeneralizedMetricSeed.metric_comp_polarization_eq_eta]
  have hpol_metric :
      G.polarization (G.metricOperator u) = -(G.eta u) := by
    calc
      G.polarization (G.metricOperator u)
          = (G.polarization.comp G.metricOperator) u := by
              rfl
      _ = (-G.eta) u := by
            rw [GeneralizedMetricSeed.polarization_comp_metric_eq_neg_eta]
      _ = -(G.eta u) := by
            simp
  calc
    G.metricOperator (GeneralizedMetricSeed.plusProjector G u)
        = (⅟ (2 : ℝ)) • (G.metricOperator u + G.metricOperator (G.polarization u)) := by
            simp [GeneralizedMetricSeed.plusProjector]
    _ = (⅟ (2 : ℝ)) • (G.metricOperator u + G.eta u) := by rw [hmetric_pol]
    _ = (⅟ (2 : ℝ)) • (G.metricOperator u - G.polarization (G.metricOperator u)) := by
          rw [hpol_metric]
          rw [smul_sub]
          simp [sub_eq_add_neg]
    _ = GeneralizedMetricSeed.minusProjector G (G.metricOperator u) := by
          rfl

@[rep_depth krein] theorem GeneralizedMetricSeed.metric_comp_minusProjector
    (G : GeneralizedMetricSeed H) :
    G.metricOperator.comp (GeneralizedMetricSeed.minusProjector G)
      = (GeneralizedMetricSeed.plusProjector G).comp G.metricOperator := by
  apply ContinuousLinearMap.ext
  intro u
  have hmetric_pol :
      G.metricOperator (G.polarization u) = G.eta u := by
    calc
      G.metricOperator (G.polarization u)
          = (G.metricOperator.comp G.polarization) u := by
              rfl
      _ = G.eta u := by
            rw [GeneralizedMetricSeed.metric_comp_polarization_eq_eta]
  have hpol_metric :
      G.polarization (G.metricOperator u) = -(G.eta u) := by
    calc
      G.polarization (G.metricOperator u)
          = (G.polarization.comp G.metricOperator) u := by
              rfl
      _ = (-G.eta) u := by
            rw [GeneralizedMetricSeed.polarization_comp_metric_eq_neg_eta]
      _ = -(G.eta u) := by
            simp
  calc
    G.metricOperator (GeneralizedMetricSeed.minusProjector G u)
        = (⅟ (2 : ℝ)) • (G.metricOperator u - G.metricOperator (G.polarization u)) := by
            simp [GeneralizedMetricSeed.minusProjector]
    _ = (⅟ (2 : ℝ)) • (G.metricOperator u - G.eta u) := by rw [hmetric_pol]
    _ = (⅟ (2 : ℝ)) • (G.metricOperator u + G.polarization (G.metricOperator u)) := by
          rw [hpol_metric]
          rw [smul_add]
          simp [sub_eq_add_neg]
    _ = GeneralizedMetricSeed.plusProjector G (G.metricOperator u) := by
          rfl

end Core

section CanonicalSeed

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "H2" => InfoGeometry.Krein.DoubledSpace H
local notation "EndH" => H2 →L[ℝ] H2

/-- Canonical generalized-metric seed on the current doubled-space modular atom. -/
@[rep_depth krein]
noncomputable def tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H where
  eta := modularConjugationJ (E := H)
  polarization := modularSignEpsilon (E := H)
  metricOperator := modularComplexI (E := H)
  eta_sq := modularConjugationJ_sq (E := H)
  polarization_sq := modularSignEpsilon_sq (E := H)
  eta_polarization_anticommute := modularConjugationJ_anticommutes_modularSign (E := H)
  metric_eq_eta_comp_polarization := rfl

@[rep_depth krein, simp] theorem tomitaGeneralizedMetricSeed_eta_eq_modular_j :
    (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H).eta = modular_j (E := H) := rfl

@[rep_depth krein, simp] theorem tomitaGeneralizedMetricSeed_polarization_eq_spectral_epsilon :
    (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H).polarization = spectral_epsilon (E := H) := rfl

@[rep_depth krein, simp] theorem tomitaGeneralizedMetricSeed_metricOperator_eq_dilationOperator :
    (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H).metricOperator = dilationOperator (E := H) := by
  change modularComplexI (E := H) = dilationOperator (E := H)
  exact modularComplexI_eq_dilationOperator (E := H)

@[rep_depth krein, simp] theorem tomitaGeneralizedMetricSeed_metricOperator_eq_complex_i :
    (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H).metricOperator = complex_i (E := H) := by
  change modularComplexI (E := H) = complex_i (E := H)
  exact InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i (E := H)

@[rep_depth krein, simp] theorem tomitaGeneralizedMetricSeed_plusProjector_eq_spectralPlusProj :
    GeneralizedMetricSeed.plusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
      = spectralPlusProj (E := H) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [GeneralizedMetricSeed.plusProjector, spectralPlusProj, tomitaGeneralizedMetricSeed,
      modularSignEpsilon]

@[rep_depth krein, simp] theorem tomitaGeneralizedMetricSeed_minusProjector_eq_spectralMinusProj :
    GeneralizedMetricSeed.minusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H)
      = spectralMinusProj (E := H) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [GeneralizedMetricSeed.minusProjector, spectralMinusProj, tomitaGeneralizedMetricSeed,
      modularSignEpsilon]

@[rep_depth krein] theorem tomitaGeneralizedMetricSeed_plusProjector_mem_plusSheet
    (u : H2) :
    GeneralizedMetricSeed.plusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) u
      ∈ plusSheet (E := H) := by
  simpa using spectralPlusProj_mem_plusSheet (E := H) u

@[rep_depth krein] theorem tomitaGeneralizedMetricSeed_minusProjector_mem_minusSheet
    (u : H2) :
    GeneralizedMetricSeed.minusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) u
      ∈ minusSheet (E := H) := by
  simpa using spectralMinusProj_mem_minusSheet (E := H) u

@[rep_depth krein, simp] theorem tomitaGeneralizedMetricSeed_plusProjector_eq_self_of_mem_plusSheet
    {u : H2} (hu : u ∈ plusSheet (E := H)) :
    GeneralizedMetricSeed.plusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) u = u := by
  rw [tomitaGeneralizedMetricSeed_plusProjector_eq_spectralPlusProj]
  rw [spectralPlusProj_apply_eq_plusPoint, eq_plusPoint_of_mem_plusSheet (E := H) hu]
  simp

@[rep_depth krein, simp] theorem tomitaGeneralizedMetricSeed_minusProjector_eq_self_of_mem_minusSheet
    {u : H2} (hu : u ∈ minusSheet (E := H)) :
    GeneralizedMetricSeed.minusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) u = u := by
  rw [tomitaGeneralizedMetricSeed_minusProjector_eq_spectralMinusProj]
  rw [spectralMinusProj_apply_eq_minusPoint, eq_minusPoint_of_mem_minusSheet (E := H) hu]
  simp

@[rep_depth krein] theorem tomitaGeneralizedMetricSeed_decompose
    (u : H2) :
    u = GeneralizedMetricSeed.plusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) u
          + GeneralizedMetricSeed.minusProjector (tomitaGeneralizedMetricSeed : GeneralizedMetricSeed H) u := by
  simpa using spectral_decomposition (E := H) u

end CanonicalSeed

end InfoGeometry.Canonical.GeneralizedMetricCore
