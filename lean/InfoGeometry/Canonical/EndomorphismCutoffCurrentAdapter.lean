import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.SplitCARCurrentSourceAdapter

namespace InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.CurrentSugawaraBridge
open VirasoroProject

variable {𝕜 A V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [Ring A] [AddCommGroup V] [Module 𝕜 V]

/-- Ring homomorphisms preserve integer scalar multiplication on the unit. -/
lemma RingHom.map_int_zsmul_one
    {R S : Type*} [Ring R] [Ring S] [Algebra 𝕜 S]
    (ρ : R →+* S) (m : Int) :
    ρ (m • (1 : R)) = (m : 𝕜) • (1 : S) := by
  simp [Int.cast_smul_eq_zsmul]

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
  unfold InfoGeometry.Canonical.BosonizationConstructiveCurrent.comm LinearMap.commutator
  simp [map_sub, map_mul]

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
  rw [RawCARModeCompletion.cutoffCurrent_commutator_eq_boundary_add_heisenberg_of_natAbs_le C N m n hN]
  rw [map_add]
  congr 1
  by_cases hmn : m + n = 0
  · simp [hmn, RawCARModeCompletion.central]
    ext v
    simp [Algebra.smul_def]
  · simp [hmn]

/--
Hypotheses that a family `J : Int → Module.End 𝕜 V` arises from
a stabilized source-faithful cutoff.
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

/-- Pointwise eventual stabilization to `J m v`. -/
theorem eventually_cutoffCurrent_eq
    (m : Int) (v : V) :
    ∀ᶠ N : ℕ in atTop,
      endomorphismCutoffCurrent S.source S.ρ N m v = S.J m v :=
  S.cutoff_eventually_constant m v

/-- The stabilized current preserves addition because each finite cutoff does,
and the cutoff eventually agrees with `S.J` on any fixed pair of vectors. -/
theorem stabilizedCurrent_add
    (m : Int) (v w : V) :
    S.J m (v + w) = S.J m v + S.J m w := by
  exact (S.J m).map_add v w

/-- Scalar multiplication likewise descends pointwise. -/
theorem stabilizedCurrent_smul
    (m : Int) (c : 𝕜) (v : V) :
    S.J m (c • v) = c • S.J m v := by
  exact (S.J m).map_smul c v

/-- The commutator of the derived stabilized currents is the Heisenberg
commutator.  The proof uses exact finite-cutoff CAR/Wick expansion,
eventual disappearance of the represented boundary term, and the
inherent polarization-crossing count evaluated for `N ≥ |m|`. -/
theorem current_commutator
    (S : StabilizedCurrentSource 𝕜 A V)
    (m n : Int) :
    (S.J m).commutator (S.J n) =
      if m + n = 0 then (m : 𝕜) • (1 : Module.End 𝕜 V) else 0 := by
  apply LinearMap.ext
  intro v
  let F : ℕ → Int → Module.End 𝕜 V :=
    fun N k => endomorphismCutoffCurrent S.source S.ρ N k
  have hgood : ∀ᶠ N : ℕ in atTop,
      m.natAbs ≤ N ∧
      F N n v = S.J n v ∧
      F N m v = S.J m v ∧
      F N m (S.J n v) = S.J m (S.J n v) ∧
      F N n (S.J m v) = S.J n (S.J m v) ∧
      S.ρ (S.source.cutoffBoundaryTerm N m n) v = 0 := by
    filter_upwards [
      eventually_atTop.2 ⟨m.natAbs, fun _ hN => hN⟩,
      S.cutoff_eventually_constant n v,
      S.cutoff_eventually_constant m v,
      S.cutoff_eventually_constant m (S.J n v),
      S.cutoff_eventually_constant n (S.J m v),
      S.boundary_eventually_zero m n v
    ] with N hN hn hm hmJn hnJm hb
    exact ⟨hN, hn, hm, hmJn, hnJm, hb⟩
  obtain ⟨N, hN, hn, hm, hmJn, hnJm, hb⟩ := hgood.exists
  have hfinite :=
    endomorphismCutoffCurrent_commutator_eq_wick_image
      S.source S.ρ N m n hN
  have hcomm :
      (F N m).commutator (F N n) v =
        (S.J m).commutator (S.J n) v := by
    change F N m (F N n v) - F N n (F N m v) =
      S.J m (S.J n v) - S.J n (S.J m v)
    rw [hn, hm, hmJn, hnJm]
  rw [← hcomm, hfinite, LinearMap.add_apply, hb, zero_add]

end StabilizedCurrentSource

end InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter
