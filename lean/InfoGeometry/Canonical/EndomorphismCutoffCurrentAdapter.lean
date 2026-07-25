import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.CurrentSugawaraBridge

namespace InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge
open VirasoroProject

variable {𝕜 A V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [Ring A] [AddCommGroup V] [Module 𝕜 V]

/-- Integer scalar multiplication agrees with scalar multiplication by the
integer cast into the coefficient field. -/
theorem int_zsmul_eq_cast_smul (m : Int) (v : V) :
    m • v = (m : 𝕜) • v :=
  (Int.cast_smul_eq_zsmul 𝕜 m v).symm

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
    endomorphismCutoffCurrent C ρ N m = ρ (representedCutoffCurrent C N m) := by
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
Pointwise eventual stabilization of the finite cutoff to `J m`.

This is the nontrivial Wick theorem transfer from ring-valued `comm` to endomorphism-valued
Heisenberg commutators on the carrier `V`.
-/
theorem endomorphismCutoffCurrent_commutator_eq_wick_image
    (C : RawCARModeCompletion A)
    (ρ : A →+* Module.End 𝕜 V)
    (N : ℕ) (m n : Int) (hN : m.natAbs ≤ N) :
    (endomorphismCutoffCurrent C ρ N m).commutator
        (endomorphismCutoffCurrent C ρ N n) =
      ρ (RawCARModeCompletion.cutoffBoundaryTerm C N m n) +
        if m + n = 0 then (m : 𝕜) • (1 : Module.End 𝕜 V) else 0 := by
  rw [endomorphismCutoffCurrent_commutator]
  rw [RawCARModeCompletion.cutoffCurrent_commutator_eq_boundary_add_heisenberg_of_natAbs_le
    C N m n hN]
  rw [map_add]
  congr 1
  by_cases hmn : m + n = 0
  · simp only [hmn, if_pos, map_zsmul, RawCARModeCompletion.central, map_one]
    ext v
    exact int_zsmul_eq_cast_smul m v
  · simp [hmn]

/--
Hypotheses that a mode family `J : Int → Module.End 𝕜 V` arises from
a stabilized source-faithful cutoff `A →+* Module.End V`.
-/
structure StabilizedCurrentSource
    (𝕜 A V : Type*) [Field 𝕜] [CharZero 𝕜]
    [Ring A] [AddCommGroup V] [Module 𝕜 V] where
  source : RawCARModeCompletion A
  ρ : A →+* Module.End 𝕜 V
  J : Int → Module.End 𝕜 V
  trunc :
    ∀ v, ∀ᶠ l : Int in atTop, J l v = 0
  cutoff_eventually_constant :
    ∀ m v, ∀ᶠ N : ℕ in atTop,
      endomorphismCutoffCurrent source ρ N m v = J m v
  boundary_eventually_zero :
    ∀ m n v, ∀ᶠ N : ℕ in atTop,
      ρ (source.cutoffBoundaryTerm N m n) v = 0

namespace StabilizedCurrentSource

variable {𝕜 A V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [Ring A] [AddCommGroup V] [Module 𝕜 V]
variable (S : StabilizedCurrentSource 𝕜 A V)

/-- Pointwise eventual stabilization of the finite cutoff. -/
theorem eventually_cutoffCurrent_eq
    (m : Int) (v : V) :
    ∀ᶠ N : ℕ in atTop,
      endomorphismCutoffCurrent S.source S.ρ N m v = S.J m v :=
  S.cutoff_eventually_constant m v

/-- The commutator of the derived stabilized currents is the Heisenberg
commutator.  The proof uses exact finite-cutoff CAR/Wick expansion,
eventual disappearance of the represented boundary term, and the
inherent polarization-crossing count evaluated for `N ≥ |m|`.
-/
theorem current_commutator
    (m n : Int) :
    (S.J m).commutator (S.J n) =
      if m + n = 0 then
        (m : 𝕜) • (1 : Module.End 𝕜 V)
      else
        0 := by
  ext v
  have hm_v := S.eventually_cutoffCurrent_eq m v
  have hn_v := S.eventually_cutoffCurrent_eq n v
  have hm_Jn := S.eventually_cutoffCurrent_eq m (S.J n v)
  have hn_Jm := S.eventually_cutoffCurrent_eq n (S.J m v)
  have hboundary := S.boundary_eventually_zero m n v
  rcases (eventually_atTop.1 hm_v) with ⟨Nm_v, hm_v_at⟩
  rcases (eventually_atTop.1 hn_v) with ⟨Nn_v, hn_v_at⟩
  rcases (eventually_atTop.1 hm_Jn) with ⟨Nm_Jn, hm_Jn_at⟩
  rcases (eventually_atTop.1 hn_Jm) with ⟨Nn_Jm, hn_Jm_at⟩
  rcases (eventually_atTop.1 hboundary) with ⟨Nb, hboundary_at⟩
  let N := m.natAbs + Nm_v + Nn_v + Nm_Jn + Nn_Jm + Nb
  have hN : m.natAbs ≤ N := by
    dsimp [N]
    omega
  have hmN := hm_v_at N (by dsimp [N]; omega)
  have hnN := hn_v_at N (by dsimp [N]; omega)
  have hmJN := hm_Jn_at N (by dsimp [N]; omega)
  have hnJN := hn_Jm_at N (by dsimp [N]; omega)
  have hbN := hboundary_at N (by dsimp [N]; omega)
  change
    S.J m (S.J n v) - S.J n (S.J m v) =
      (if m + n = 0 then (m : 𝕜) • (1 : Module.End 𝕜 V) else 0) v
  calc
    S.J m (S.J n v) - S.J n (S.J m v) =
        endomorphismCutoffCurrent S.source S.ρ N m
            (endomorphismCutoffCurrent S.source S.ρ N n v) -
          endomorphismCutoffCurrent S.source S.ρ N n
            (endomorphismCutoffCurrent S.source S.ρ N m v) := by
      rw [hmN, hnN, hmJN, hnJN]
    _ = S.ρ
        (InfoGeometry.Canonical.BosonizationConstructiveCurrent.comm
          (S.source.cutoffCurrent N m) (S.source.cutoffCurrent N n)) v := by
      rw [← endomorphismCutoffCurrent_commutator]
      rfl
    _ = S.ρ
        (S.source.cutoffBoundaryTerm N m n +
          if m + n = 0 then m • S.source.central else 0) v := by
      rw [S.source.cutoffCurrent_commutator_eq_boundary_add_heisenberg_of_natAbs_le
        N m n hN]
    _ = _ := by
      rw [map_add, LinearMap.add_apply, hbN]
      by_cases hmn : m + n = 0
      · simp only [hmn, if_pos, map_zsmul, RawCARModeCompletion.central, map_one,
          zero_add, LinearMap.smul_apply]
        exact int_zsmul_eq_cast_smul m v
      · simp [hmn]

/-- Positive-energy data is the additional input required by Sugawara. -/
structure PositiveEnergy
    (S : StabilizedCurrentSource 𝕜 A V) where
  trunc :
    ∀ v, ∀ᶠ l : Int in atTop, S.J l v = 0

/-- A source-derived positive-energy current is a genuine Heisenberg representation. -/
noncomputable def toCurrentHeisenbergRep
    (S : StabilizedCurrentSource 𝕜 A V) (hS : S.PositiveEnergy) :
    CurrentHeisenbergRep 𝕜 V where
  J := S.J
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
