import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.CurrentSugawaraBridge

namespace InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge
open VirasoroProject

variable {𝕜 A V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [Ring A] [AddCommGroup V] [Module 𝕜 V]

/-- The finite normal-ordered CAR current represented on `V`. -/
def endomorphismCutoffCurrent
    (C : RawCARModeCompletion A)
    (ρ : A →+* Module.End 𝕜 V)
    (N : ℕ) (m : Int) : Module.End 𝕜 V :=
  ρ (C.cutoffCurrent N m)

/-- The represented cutoff is the image of the public finite-window current. -/
theorem endomorphismCutoffCurrent_eq_representedCutoffCurrent
    (C : RawCARModeCompletion A)
    (ρ : A →+* Module.End 𝕜 V)
    (N : ℕ) (m : Int) :
    endomorphismCutoffCurrent C ρ N m =
      ρ (representedCutoffCurrent C N m) :=
  rfl

/-- A represented cutoff current is the finite sum of represented matrix units. -/
theorem endomorphismCutoffCurrent_eq_sum
    (C : RawCARModeCompletion A)
    (ρ : A →+* Module.End 𝕜 V)
    (N : ℕ) (m : Int) :
    endomorphismCutoffCurrent C ρ N m =
      ∑ k ∈ integerWindow N, ρ (C.matrixUnit k (k + m)) := by
  rw [endomorphismCutoffCurrent_eq_representedCutoffCurrent]
  unfold representedCutoffCurrent
  exact map_sum ρ (fun k => C.matrixUnit k (k + m)) (integerWindow N)

/-- Ring representations carry the raw algebra commutator to the endomorphism commutator. -/
theorem endomorphismCutoffCurrent_commutator
    (C : RawCARModeCompletion A)
    (ρ : A →+* Module.End 𝕜 V)
    (N M : ℕ) (m n : Int) :
    (endomorphismCutoffCurrent C ρ N m).commutator
        (endomorphismCutoffCurrent C ρ M n) =
      ρ (InfoGeometry.Canonical.BosonizationConstructiveCurrent.comm
        (C.cutoffCurrent N m) (C.cutoffCurrent M n)) := by
  unfold endomorphismCutoffCurrent
  unfold InfoGeometry.Canonical.BosonizationConstructiveCurrent.comm
    LinearMap.commutator
  simp

/--
Source data sufficient to derive a stabilized represented current.

The finite currents and their representation are definitions.  The two fields
are the genuine additional hypotheses needed to pass from finite cutoffs to an
endomorphism-valued limit: pointwise eventual constancy and disappearance of
the represented cutoff boundary on every vector.
-/
structure StabilizedCurrentSource
    (𝕜 A V : Type*) [Field 𝕜] [CharZero 𝕜]
    [Ring A] [AddCommGroup V] [Module 𝕜 V] where
  source : RawCARModeCompletion A
  ρ : A →+* Module.End 𝕜 V
  cutoff_eventually_constant :
    ∀ (m : Int) (v : V), ∃ y : V,
      ∀ᶠ N : ℕ in atTop, endomorphismCutoffCurrent source ρ N m v = y
  boundary_eventually_zero :
    ∀ (m n : Int) (v : V), ∀ᶠ N : ℕ in atTop,
      ρ (source.cutoffBoundaryTerm N m n) v = 0

namespace StabilizedCurrentSource

/-- The unique eventual value of the represented cutoff action. -/
noncomputable def stabilizedValue
    (S : StabilizedCurrentSource 𝕜 A V) (m : Int) (v : V) : V :=
  Classical.choose (S.cutoff_eventually_constant m v)

/-- Every represented cutoff action is eventually its selected stabilized value. -/
theorem eventually_cutoffCurrent_eq_stabilizedValue
    (S : StabilizedCurrentSource 𝕜 A V) (m : Int) (v : V) :
    ∀ᶠ N : ℕ in atTop,
      endomorphismCutoffCurrent S.source S.ρ N m v =
        S.stabilizedValue m v :=
  Classical.choose_spec (S.cutoff_eventually_constant m v)

/-- The stabilized current is derived from the eventual finite-cutoff action. -/
noncomputable def stabilizedCurrent
    (S : StabilizedCurrentSource 𝕜 A V) (m : Int) : Module.End 𝕜 V where
  toFun := S.stabilizedValue m
  map_add' := by
    intro v w
    have hv := S.eventually_cutoffCurrent_eq_stabilizedValue m v
    have hw := S.eventually_cutoffCurrent_eq_stabilizedValue m w
    have hvw := S.eventually_cutoffCurrent_eq_stabilizedValue m (v + w)
    filter_upwards [hv, hw, hvw] with N hvN hwN hvwN
    rw [← hvwN, map_add, hvN, hwN]
  map_smul' := by
    intro c v
    have hv := S.eventually_cutoffCurrent_eq_stabilizedValue m v
    have hcv := S.eventually_cutoffCurrent_eq_stabilizedValue m (c • v)
    filter_upwards [hv, hcv] with N hvN hcvN
    rw [← hcvN, map_smul, hvN]

/-- The represented finite current eventually agrees pointwise with the derived current. -/
theorem eventually_cutoffCurrent_eq
    (S : StabilizedCurrentSource 𝕜 A V) (m : Int) (v : V) :
    ∀ᶠ N : ℕ in atTop,
      endomorphismCutoffCurrent S.source S.ρ N m v =
        S.stabilizedCurrent m v :=
  S.eventually_cutoffCurrent_eq_stabilizedValue m v

/--
The commutator of the derived stabilized currents is the Heisenberg
commutator.  The proof uses the exact finite-cutoff CAR/Wick commutator,
eventual disappearance of its boundary action, and the polarization crossing
count evaluated for `N ≥ |m|`.
-/
theorem current_commutator
    (S : StabilizedCurrentSource 𝕜 A V) (m n : Int) :
    (S.stabilizedCurrent m).commutator (S.stabilizedCurrent n) =
      if m + n = 0 then
        (m : 𝕜) • (1 : Module.End 𝕜 V)
      else
        0 := by
  ext v
  have hm_v := S.eventually_cutoffCurrent_eq m v
  have hn_v := S.eventually_cutoffCurrent_eq n v
  have hm_Jn := S.eventually_cutoffCurrent_eq m (S.stabilizedCurrent n v)
  have hn_Jm := S.eventually_cutoffCurrent_eq n (S.stabilizedCurrent m v)
  have hboundary := S.boundary_eventually_zero m n v
  have hlarge : ∀ᶠ N : ℕ in atTop, m.natAbs ≤ N :=
    eventually_atTop.2 ⟨m.natAbs, fun _ hN => hN⟩
  filter_upwards [hm_v, hn_v, hm_Jn, hn_Jm, hboundary, hlarge] with
    N hm_vN hn_vN hm_JnN hn_JmN hboundaryN hN
  change
    S.stabilizedCurrent m (S.stabilizedCurrent n v) -
        S.stabilizedCurrent n (S.stabilizedCurrent m v) =
      (if m + n = 0 then
          (m : 𝕜) • (1 : Module.End 𝕜 V)
        else
          0) v
  calc
    S.stabilizedCurrent m (S.stabilizedCurrent n v) -
          S.stabilizedCurrent n (S.stabilizedCurrent m v)
        =
      endomorphismCutoffCurrent S.source S.ρ N m
            (endomorphismCutoffCurrent S.source S.ρ N n v) -
        endomorphismCutoffCurrent S.source S.ρ N n
            (endomorphismCutoffCurrent S.source S.ρ N m v) := by
          rw [hm_vN, hn_vN, hm_JnN, hn_JmN]
    _ =
      S.ρ
          (InfoGeometry.Canonical.BosonizationConstructiveCurrent.comm
            (S.source.cutoffCurrent N m) (S.source.cutoffCurrent N n)) v := by
          rw [← endomorphismCutoffCurrent_commutator]
          rfl
    _ =
      S.ρ
          (S.source.cutoffBoundaryTerm N m n +
            if m + n = 0 then m • S.source.central else 0) v := by
          rw [S.source.cutoffCurrent_commutator_eq_boundary_add_heisenberg_of_natAbs_le
            N m n hN]
    _ =
      (if m + n = 0 then
          (m : 𝕜) • (1 : Module.End 𝕜 V)
        else
          0) v := by
          rw [map_add, LinearMap.add_apply, hboundaryN]
          simp [RawCARModeCompletion.central]

/-- Positive-energy data is the additional input required by Sugawara. -/
structure PositiveEnergy
    (S : StabilizedCurrentSource 𝕜 A V) where
  trunc :
    ∀ v, ∀ᶠ l : Int in atTop, S.stabilizedCurrent l v = 0

/-- A source-derived positive-energy current is a genuine Heisenberg representation. -/
noncomputable def toCurrentHeisenbergRep
    (S : StabilizedCurrentSource 𝕜 A V) (hS : S.PositiveEnergy) :
    CurrentHeisenbergRep 𝕜 V where
  J := S.stabilizedCurrent
  trunc := hS.trunc
  comm := S.current_commutator

/-- The end-to-end source-derived Raw-CAR to Sugawara representation. -/
noncomputable def toSugawaraVirasoroRepresentation
    (S : StabilizedCurrentSource 𝕜 A V) (hS : S.PositiveEnergy) :
    VirasoroAlgebra 𝕜 →ₗ⁅𝕜⁆ Module.End 𝕜 V :=
  (S.toCurrentHeisenbergRep hS).currentSugawaraRepresentation

/-- The resulting Sugawara stress modes satisfy the Virasoro bracket. -/
theorem virasoro_bracket
    (S : StabilizedCurrentSource 𝕜 A V) (hS : S.PositiveEnergy)
    (m n : Int) :
    ((S.toCurrentHeisenbergRep hS).sugawaraStressMode m).commutator
        ((S.toCurrentHeisenbergRep hS).sugawaraStressMode n) =
      (m - n) • (S.toCurrentHeisenbergRep hS).sugawaraStressMode (m + n) +
        if m + n = 0 then
          (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : Module.End 𝕜 V))
        else
          0 :=
  (S.toCurrentHeisenbergRep hS).sugawaraStressMode_virasoroBracket m n

end StabilizedCurrentSource

end InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter
