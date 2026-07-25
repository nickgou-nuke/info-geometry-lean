import InfoGeometry.Canonical.BosonizationConstructiveCurrent
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
  have h : ∀ (m : Int), ρ (m • (1 : R)) = (m : 𝕜) • (1 : S) := by
    intro m
    induction m using Int.induction_on with
    | zero =>
      simp [RingHom.map_zero]
    | succ m ih =>
      rw [Int.succ_eq_add_one]
      simp [add_smul, one_smul, RingHom.map_add, RingHom.map_one, ih]
      <;> ring_nf at * <;> simp_all [Algebra.smul_def]
      <;> abel
    | neg m ih =>
      rw [Int.neg_eq_neg]
      rw [neg_smul, ih]
      simp [neg_smul, Algebra.smul_def]
      <;> ring_nf at * <;> simp_all [Algebra.smul_def]
      <;> abel
  exact h m

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
  <;>
  simp_all [LinearMap.commutator]
  <;>
  ring_nf
  <;>
  aesop

/-- Ring homomorphisms preserve integer scalar multiplication on the unit. -/
lemma RingHom.map_int_zsmul_one
    {R S : Type*} [Ring R] [Ring S] [Algebra 𝕜 S]
    (ρ : R →+* S) (m : Int) :
    ρ (m • (1 : R)) = (m : 𝕜) • (1 : S) := by
  have h : ∀ (m : Int), ρ (m • (1 : R)) = (m : 𝕜) • (1 : S) := by
    intro m
    induction m using Int.induction_on with
    | zero =>
      simp [RingHom.map_zero]
    | succ m ih =>
      rw [Int.succ_eq_add_one]
      simp [add_smul, one_smul, RingHom.map_add, RingHom.map_one, ih]
      <;> ring_nf at * <;> simp_all [Algebra.smul_def]
      <;> abel
    | neg m ih =>
      rw [Int.neg_eq_neg]
      rw [neg_smul, ih]
      simp [neg_smul, Algebra.smul_def]
      <;> ring_nf at * <;> simp_all [Algebra.smul_def]
      <;> abel
  exact h m

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
  <;>
  simp_all [LinearMap.commutator]
  <;>
  ring_nf
  <;>
  aesop

/-- Ring homomorphisms preserve integer scalar multiplication on the unit. -/
lemma RingHom.map_int_zsmul_one
    {R S : Type*} [Ring R] [Ring S] [Algebra 𝕜 S]
    (ρ : R →+* S) (m : Int) :
    ρ (m • (1 : R)) = (m : 𝕜) • (1 : S) := by
  have h : ∀ (m : Int), ρ (m • (1 : R)) = (m : 𝕜) • (1 : S) := by
    intro m
    induction m using Int.induction_on with
    | zero =>
      simp [RingHom.map_zero]
    | succ m ih =>
      rw [Int.succ_eq_add_one]
      simp [add_smul, one_smul, RingHom.map_add, RingHom.map_one, ih]
      <;> ring_nf at * <;> simp_all [Algebra.smul_def]
      <;> abel
    | neg m ih =>
      rw [Int.neg_eq_neg]
      rw [neg_smul, ih]
      simp [neg_smul, Algebra.smul_def]
      <;> ring_nf at * <;> simp_all [Algebra.smul_def]
      <;> abel
  exact h m

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
  simp [LinearMap.add_apply, map_add, RawCARModeCompletion.central]
  have hs : ρ (if m + n = 0 then m • C.central else 0) =
      if m + n = 0 then (m : 𝕜) • (1 : Module.End 𝕜 V) else 0 := by
    split_ifs with hmn
    · unfold RawCARModeCompletion.central
      simp [RingHom.map_int_zsmul_one, RingHom.map_one]
    · simp [map_zero]
  rw [hs]
  <;>
  simp_all [LinearMap.add_apply]
  <;>
  aesop

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
  have hv := S.eventually_cutoffCurrent_eq m v
  have hw := S.eventually_cutoffCurrent_eq m w
  have hvw := S.eventually_cutoffCurrent_eq m (v + w)
  have h₁ : ∀ᶠ N : ℕ in atTop, endomorphismCutoffCurrent S.source S.ρ N m (v + w) = endomorphismCutoffCurrent S.source S.ρ N m v + endomorphismCutoffCurrent S.source S.ρ N m w := by
    filter_upwards [hvw, hv, hw] with N hvwN hvN hwN
    rw [← hvwN, LinearMap.add_apply, hvN, hwN]
  have h₂ : ∀ᶠ N : ℕ in atTop, S.J m (v + w) = S.J m v + S.J m w := by
    filter_upwards [h₁, hvw, hv, hw] with N hN hvwN hvN hwN
    calc
      S.J m (v + w) = endomorphismCutoffCurrent S.source S.ρ N m (v + w) := by rw [hvwN]
      _ = endomorphismCutoffCurrent S.source S.ρ N m v + endomorphismCutoffCurrent S.source S.ρ N m w := by rw [hN]
      _ = S.J m v + S.J m w := by rw [hvN, hwN]
  -- Extract the result from the filter
  have h₃ : S.J m (v + w) = S.J m v + S.J m w := by
    have h₄ : ∃ N : ℕ, S.J m (v + w) = S.J m v + S.J m w := by
      obtain ⟨N, hN⟩ := (h₂).exists
      exact ⟨N, hN⟩
    obtain ⟨N, hN⟩ := h₃
    exact hN
  exact h₃

/-- Scalar multiplication likewise descends pointwise. -/
theorem stabilizedCurrent_smul
    (m : Int) (c : 𝕜) (v : V) :
    S.J m (c • v) = c • S.J m v := by
  have hv := S.eventually_cutoffCurrent_eq m v
  have hcv := S.eventually_cutoffCurrent_eq m (c • v)
  have h₁ : ∀ᶠ N : ℕ in atTop, endomorphismCutoffCurrent S.source S.ρ N m (c • v) = c • endomorphismCutoffCurrent S.source S.ρ N m v := by
    filter_upwards [hv, hcv] with N hvN hcvN
    rw [← hcvN, LinearMap.map_smul, hvN]
  have h₂ : ∀ᶠ N : ℕ in atTop, S.J m (c • v) = c • S.J m v := by
    filter_upwards [h₁, hv, hcv] with N hN hvN hcvN
    calc
      S.J m (c • v) = endomorphismCutoffCurrent S.source S.ρ N m (c • v) := by rw [hcvN]
      _ = c • endomorphismCutoffCurrent S.source S.ρ N m v := by rw [hN]
      _ = c • S.J m v := by rw [hvN]
  -- Extract the result from the filter
  have h₃ : S.J m (c • v) = c • S.J m v := by
    have h₄ : ∃ N : ℕ, S.J m (c • v) = c • S.J m v := by
      obtain ⟨N, hN⟩ := (h₂).exists
      exact ⟨N, hN⟩
    obtain ⟨N, hN⟩ := h₃
    exact hN
  exact h₃

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
  have hm_v := S.eventually_cutoffCurrent_eq m v
  have hn_v := S.eventually_cutoffCurrent_eq n v
  have hm_Jn := S.eventually_cutoffCurrent_eq m (S.J n v)
  have hn_Jm := S.eventually_cutoffCurrent_eq n (S.J m v)
  have hboundary := S.boundary_eventually_zero m n v
  have hlarge : ∀ᶠ N : ℕ in atTop, m.natAbs ≤ N :=
    eventually_atTop.2 ⟨m.natAbs, fun _ hN => hN⟩
  -- Find a cutoff N large enough for all the eventually conditions
  have h_main : (S.J m).commutator (S.J n) v = (if m + n = 0 then (m : 𝕜) • (1 : Module.End 𝕜 V) else 0) v := by
    have h₁ : ∃ (N : ℕ), m.natAbs ≤ N ∧ endomorphismCutoffCurrent S.source S.ρ N m v = S.J m v ∧ endomorphismCutoffCurrent S.source S.ρ N n v = S.J n v ∧ endomorphismCutoffCurrent S.source S.ρ N m (S.J n v) = S.J m (S.J n v) ∧ endomorphismCutoffCurrent S.source S.ρ N n (S.J m v) = S.J n (S.J m v) ∧ S.ρ (S.source.cutoffBoundaryTerm N m n) v = 0 := by
      have h₁ : ∀ᶠ N : ℕ in atTop, m.natAbs ≤ N := eventually_atTop.2 ⟨m.natAbs, fun _ hN => hN⟩
      have h₂ : ∀ᶠ N : ℕ in atTop, endomorphismCutoffCurrent S.source S.ρ N m v = S.J m v := S.eventually_cutoffCurrent_eq m v
      have h₃ : ∀ᶠ N : ℕ in atTop, endomorphismCutoffCurrent S.source S.ρ N n v = S.J n v := S.eventually_cutoffCurrent_eq n v
      have h₄ : ∀ᶠ N : ℕ in atTop, endomorphismCutoffCurrent S.source S.ρ N m (S.J n v) = S.J m (S.J n v) := S.eventually_cutoffCurrent_eq m (S.J n v)
      have h₅ : ∀ᶠ N : ℕ in atTop, endomorphismCutoffCurrent S.source S.ρ N n (S.J m v) = S.J n (S.J m v) := S.eventually_cutoffCurrent_eq n (S.J m v)
      have h₆ : ∀ᶠ N : ℕ in atTop, S.ρ (S.source.cutoffBoundaryTerm N m n) v = 0 := S.boundary_eventually_zero m n v
      have h₇ : ∀ᶠ N : ℕ in atTop, m.natAbs ≤ N ∧ endomorphismCutoffCurrent S.source S.ρ N m v = S.J m v ∧ endomorphismCutoffCurrent S.source S.ρ N n v = S.J n v ∧ endomorphismCutoffCurrent S.source S.ρ N m (S.J n v) = S.J m (S.J n v) ∧ endomorphismCutoffCurrent S.source S.ρ N n (S.J m v) = S.J n (S.J m v) ∧ S.ρ (S.source.cutoffBoundaryTerm N m n) v = 0 := by
        filter_upwards [h₁, h₂, h₃, h₄, h₅, h₆] with N hN hnv hnv' hm_Jn hn_Jm hb
        exact ⟨hN, hnv, hnv', hm_Jn, hn_Jm, hb⟩
      obtain ⟨N, hN⟩ := (h₇).exists
      exact ⟨N, hN.1, hN.2.1, hN.2.2.1, hN.2.2.2.1, hN.2.2.2.2.1, hN.2.2.2.2.2⟩
    obtain ⟨N, hN1, hN2, hN3, hN4, hN5, hN6⟩ := h₁
    have h₂ : (endomorphismCutoffCurrent S.source S.ρ N m).commutator (endomorphismCutoffCurrent S.source S.ρ N n) = S.ρ (S.source.cutoffBoundaryTerm N m n) + if m + n = 0 then (m : 𝕜) • (1 : Module.End 𝕜 V) else 0 := by
      apply endomorphismCutoffCurrent_commutator_eq_wick_image S.source S.ρ N m n (by exact_mod_cast (by omega : m.natAbs ≤ N))
    calc
      (S.J m).commutator (S.J n) v = (endomorphismCutoffCurrent S.source S.ρ N m).commutator (endomorphismCutoffCurrent S.source S.ρ N n) v := by
        rw [hm_v, hn_v, hm_Jn, hn_Jm]
      _ = (S.ρ (S.source.cutoffBoundaryTerm N m n) + if m + n = 0 then (m : 𝕜) • (1 : Module.End 𝕜 V) else 0) v := by
        rw [h₂]
        <;> simp [LinearMap.add_apply]
      _ = (if m + n = 0 then (m : 𝕜) • (1 : Module.End 𝕜 V) else 0) v := by
        have h₃ : S.ρ (S.source.cutoffBoundaryTerm N m n) v = 0 := by simpa using hN6
        rw [LinearMap.add_apply, h₃]
        <;> split_ifs <;> simp_all [RawCARModeCompletion.central]
        <;> try { contradiction }
        <;> try { aesop }
    exact h_main
  rw [h_main]

end StabilizedCurrentSource

end InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter