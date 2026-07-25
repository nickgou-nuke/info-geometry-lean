import Mathlib.Tactic
import Mathlib.CategoryTheory.Functor.OfSequence

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

/-!
# Souriau/Pauli Thermodynamic Colimit (Finite Fock to Inductive Limit)

This module mirrors `inductive_colimit_uhf_group.lean` but with finite Fock-style
thermodynamic factors:

* ordinary fermion local factor `1 + x`;
* graded (parity/Witten) local factor `1 - x`;
* bosonic reciprocal local factor `(1 - x)⁻¹`.

All statements are finite, algebraic, and theorem-honest.
-/

namespace SouriauThermoColimit

/-- Finite stage of size `n`: amplitudes indexed by `Fin n`. -/
abbrev SouriauFockStage (n : ℕ) : Type := Fin n → ℂ

/-- Local finite factors on a single mode. -/
def souriauOrdinaryLocal (x : ℂ) : ℂ := 1 + x
def souriauGradedLocal (x : ℂ) : ℂ := 1 - x
def souriauBosonLocal (x : ℂ) : ℂ := (1 - x)⁻¹

/-- Finite lists of local factors and their products.
    (Used internally to prove stagewise identities.) -/
def finiteOrdinaryTrace (xs : List ℂ) : ℂ :=
  (xs.map souriauOrdinaryLocal).prod

def finiteGradedSupertrace (xs : List ℂ) : ℂ :=
  (xs.map souriauGradedLocal).prod

def finiteBosonicDeterminant (xs : List ℂ) : ℂ :=
  (xs.map souriauBosonLocal).prod

/-- Basic cubic relation used to classify ternary thermodynamic states. -/
def souriauCubicOperator (q : ℝ) : Prop := q ^ 3 = q

/-- Three thermodynamic branches induced by the cubic relation (`q^3=q`).
    These match the `elliptic / hyperbolic / parabolic` labels used in the
    Pauli causal algebraic dictionary.
-/
inductive OPState where
  | elliptic
  | hyperbolic
  | parabolic
  deriving DecidableEq, Repr

/-- Local factor attached to a named OP state. -/
def souriauStateLocalFromState (s : OPState) (x : ℂ) : ℂ :=
  match s with
  | OPState.elliptic => souriauOrdinaryLocal x
  | OPState.hyperbolic => souriauBosonLocal x
  | OPState.parabolic => souriauGradedLocal x

@[simp] theorem souriauStateLocalFromState_elliptic (x : ℂ) :
    souriauStateLocalFromState OPState.elliptic x = souriauOrdinaryLocal x := by
  rfl

@[simp] theorem souriauStateLocalFromState_hyperbolic (x : ℂ) :
    souriauStateLocalFromState OPState.hyperbolic x = souriauBosonLocal x := by
  rfl

@[simp] theorem souriauStateLocalFromState_parabolic (x : ℂ) :
    souriauStateLocalFromState OPState.parabolic x = souriauGradedLocal x := by
  rfl

/-- Optional mapping from cubic scalar value to state branch. -/
def OPStateFromCubicValue (q : ℝ) : Option OPState :=
  if _hq : q = 1 then some OPState.elliptic else
  if _hq1 : q = -1 then some OPState.hyperbolic else
  if _hq0 : q = 0 then some OPState.parabolic else none

/-- `OP^3 = OP` forces the value into one of the three state branches. -/
theorem souriau_cubic_operator_roots {q : ℝ} (hq : souriauCubicOperator q) :
    q = -1 ∨ q = 0 ∨ q = 1 := by
  have hfac : q * (q - 1) * (q + 1) = 0 := by
    have h' : q ^ 3 - q = 0 := by
      have h'' : q ^ 3 - q = q - q := by
        simpa using congrArg (fun t => t - q) hq
      simpa using h''
    calc
      q * (q - 1) * (q + 1) = q ^ 3 - q := by ring
      _ = 0 := h'
  rcases mul_eq_zero.mp hfac with h01 | h11
  · rcases mul_eq_zero.mp h01 with h0 | h1
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr (by linarith [h1]))
  · exact Or.inl (by linarith [h11])

-- (Optional) witness that the cubic mapping is total on roots of `OP^3=OP`.
-- theorem OPStateFromCubicValue_of_cubic ...
-- omitted here to avoid additional branch normalization obligations.


/-- Local partition label from a numeric state value. -/
def souriauStatePartitionLocal (q : ℝ) (x : ℂ) : ℂ :=
  match OPStateFromCubicValue q with
  | some s => souriauStateLocalFromState s x
  | none => 0

@[simp] theorem souriauStatePartitionLocal_elliptic (x : ℂ) :
    souriauStatePartitionLocal 1 x = souriauOrdinaryLocal x := by
  simp [souriauStatePartitionLocal, OPStateFromCubicValue]

@[simp] theorem souriauStatePartitionLocal_parabolic (x : ℂ) :
    souriauStatePartitionLocal 0 x = souriauGradedLocal x := by
  simp [souriauStatePartitionLocal, OPStateFromCubicValue]

@[simp] theorem souriauStatePartitionLocal_hyperbolic (x : ℂ) :
    souriauStatePartitionLocal (-1) x = souriauBosonLocal x := by
  norm_num [souriauStatePartitionLocal, OPStateFromCubicValue]

/-- State-typed finite partition on a Souriau stage.
    This chooses the local factor at each site by the OP-state value.
-/
def souriauStatePartition {n : ℕ} (v : SouriauFockStage n) (σ : Fin n → OPState) : ℂ :=
  (List.ofFn fun i => souriauStateLocalFromState (σ i) (v i)).prod

/-- Uniform elliptic profile selects the ordinary Pauli local factor `1+x`. -/
theorem souriauStatePartition_elliptic {n : ℕ} (v : SouriauFockStage n) :
    souriauStatePartition v (fun _ => OPState.elliptic) =
      (List.ofFn fun i => 1 + v i).prod := by
  simp [souriauStatePartition, souriauOrdinaryLocal]

/-- Uniform parabolic profile selects the graded factor `1-x`. -/
theorem souriauStatePartition_parabolic {n : ℕ} (v : SouriauFockStage n) :
    souriauStatePartition v (fun _ => OPState.parabolic) =
      (List.ofFn fun i => 1 - v i).prod := by
  simp [souriauStatePartition, souriauGradedLocal]

/-- Uniform hyperbolic profile selects the bosonic reciprocal factor `(1-x)⁻¹`. -/
theorem souriauStatePartition_hyperbolic {n : ℕ} (v : SouriauFockStage n) :
    souriauStatePartition v (fun _ => OPState.hyperbolic) =
      (List.ofFn fun i => (1 - v i)⁻¹).prod := by
  simp [souriauStatePartition, souriauStateLocalFromState_hyperbolic, souriauBosonLocal]

/-- One-mode graded trace: `1 - x`. -/
theorem finite_one_mode_graded (x : ℂ) :
    finiteGradedSupertrace [x] = souriauGradedLocal x := by
  simp [finiteGradedSupertrace, souriauGradedLocal]

/-- Finite boson cancellation in the graded/parity sector, with no local singularity.
    This is the finite analog of `Z_B * Z_gr = 1`.
-/
theorem finite_boson_cancels_graded (xs : List ℂ)
    (hxs : ∀ x ∈ xs, x ≠ 1) :
    finiteBosonicDeterminant xs * finiteGradedSupertrace xs = 1 := by
  induction xs with
  | nil =>
      simp [finiteBosonicDeterminant, finiteGradedSupertrace]
  | cons x xs ih =>
      have hx : x ≠ 1 := hxs x (by exact List.mem_cons_self)
      have htail : ∀ y ∈ xs, y ≠ 1 := by
        intro y hy
        exact hxs y (List.mem_cons_of_mem x hy)
      calc
        finiteBosonicDeterminant (x :: xs) * finiteGradedSupertrace (x :: xs)
            = (souriauBosonLocal x * finiteBosonicDeterminant xs) *
                (souriauGradedLocal x * finiteGradedSupertrace xs) := by
                  simp [finiteBosonicDeterminant, finiteGradedSupertrace, souriauBosonLocal,
                    souriauGradedLocal]
        _ = (souriauBosonLocal x * souriauGradedLocal x) *
                (finiteBosonicDeterminant xs * finiteGradedSupertrace xs) := by
                  ring
        _ = 1 * 1 := by
              rw [ih htail]
              have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
              have hcancel : souriauBosonLocal x * souriauGradedLocal x = 1 := by
                simp [souriauBosonLocal, souriauGradedLocal, hden]
              simp [hcancel]
        _ = 1 := by ring

/-- Stage embedding parameterized by a mode profile: append `modes n` at step `n`. -/
def SouriauEmbed (modes : ℕ → ℂ) (n : ℕ) :
    SouriauFockStage n → SouriauFockStage (n + 1) :=
  fun v i => if h : i.1 < n then v ⟨i.1, h⟩ else modes n

lemma SouriauEmbed_lt (modes : ℕ → ℂ) (n : ℕ) (v : SouriauFockStage n)
    {k : ℕ} (hk : k < n) :
    SouriauEmbed modes n v ⟨k, Nat.lt_succ_of_lt hk⟩ = v ⟨k, hk⟩ := by
  simp [SouriauEmbed, hk]

lemma SouriauEmbed_new (modes : ℕ → ℂ) (n : ℕ) (v : SouriauFockStage n) :
    SouriauEmbed modes n v ⟨n, Nat.lt_succ_self n⟩ = modes n := by
  simp [SouriauEmbed]

/-- Diagram of finite-stage Fock spaces. -/
def SouriauFockDiagram (modes : ℕ → ℂ) : ℕ ⥤ Type :=
  Functor.ofSequence (SouriauEmbed modes)

def SouriauFockColimit (modes : ℕ → ℂ) : Type :=
  colimit (SouriauFockDiagram modes)

/-- Boundary profile (background mode profile + stage correction).
    First `n` entries come from the finite stage; all later entries are the source
    mode profile `modes`.
-/
def SouriauBoundaryProfile : Type := ℕ → ℂ

def boundaryOfFinite (modes : ℕ → ℂ) (n : ℕ) (v : SouriauFockStage n) :
    SouriauBoundaryProfile :=
  fun k => if h : k < n then v ⟨k, h⟩ else modes k

/-- Cocone into the boundary profile, `Functor.ofSequence` form.
    The proof is structurally the same as the UHF boundary cocone.
-/
def souriauBoundaryCocone (modes : ℕ → ℂ) : Cocone (SouriauFockDiagram modes) :=
  { pt := SouriauBoundaryProfile
    ι := NatTrans.ofSequence
      (app := boundaryOfFinite modes)
      (naturality := by
        intro n
        funext b k
        have hmap : (SouriauFockDiagram modes).map (homOfLE (Nat.le_add_right n 1))
            = SouriauEmbed modes n := by
          simpa [SouriauFockDiagram] using (Functor.ofSequence_map_homOfLE_succ
            (f := SouriauEmbed modes) n)
        rw [hmap]
        by_cases hkn : k < n
        · have hkn' : k < n + 1 := Nat.lt_succ_of_lt hkn
          simp [boundaryOfFinite, SouriauEmbed, hkn, hkn']
        · by_cases hkn' : k < n + 1
          · have hk : k = n := Nat.eq_of_lt_succ_of_not_lt hkn' hkn
            subst hk
            simp [boundaryOfFinite, SouriauEmbed]
          · simp [boundaryOfFinite, hkn, hkn']) }

/-- Stagewise finite thermodynamic observables as list-based factors on the mode data. -/
def souriauOrdinaryFermionPartition (n : ℕ) (v : SouriauFockStage n) : ℂ :=
  finiteOrdinaryTrace (List.ofFn v)

def souriauGradedFermionPartition (n : ℕ) (v : SouriauFockStage n) : ℂ :=
  finiteGradedSupertrace (List.ofFn v)

def souriauBosonicPartition (n : ℕ) (v : SouriauFockStage n) : ℂ :=
  finiteBosonicDeterminant (List.ofFn v)

def souriauMoebiusArithmeticIndex (n : ℕ) (v : SouriauFockStage n) : ℂ :=
  souriauGradedFermionPartition n v

def souriauDenominatorZero (n : ℕ) (v : SouriauFockStage n) : Prop :=
  ∃ i : Fin n, v i = 1

def souriauGradedIndexSingularity (n : ℕ) (v : SouriauFockStage n) : Prop :=
  souriauMoebiusArithmeticIndex n v = 0

/-- If some local mode is exactly one, the graded parity/supertrace factor vanishes.
    (`1 - 1 = 0` appears in the finite product.) -/
theorem souriauGradedIndex_zero_of_denominator_zero (n : ℕ) (v : SouriauFockStage n)
    (h : souriauDenominatorZero n v) :
    souriauGradedIndexSingularity n v := by
  rcases h with ⟨i, hi⟩
  unfold souriauGradedIndexSingularity souriauMoebiusArithmeticIndex souriauGradedFermionPartition
  apply (List.prod_eq_zero_iff).2
  have hvmem : souriauGradedLocal (v i) ∈ List.map souriauGradedLocal (List.ofFn v) :=
    List.mem_map_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩)
  simpa [souriauGradedLocal, hi] using hvmem

/-- Conversely, if the graded index is zero, some local denominator vanishes.
    This uses `List.prod_eq_zero_iff` in `ℂ` (NoZeroDivisors).
-/
theorem souriau_denominator_zero_of_gradedIndex_zero (n : ℕ) (v : SouriauFockStage n)
    (h : souriauGradedIndexSingularity n v) :
    souriauDenominatorZero n v := by
  unfold souriauGradedIndexSingularity souriauMoebiusArithmeticIndex souriauGradedFermionPartition at h
  by_contra h'
  have hlist : ∀ x ∈ List.ofFn v, x ≠ 1 := by
    intro x hx
    rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
    intro hx1
    exact h' ⟨i, by simpa [hx1]⟩
  have hcancel : finiteBosonicDeterminant (List.ofFn v) * finiteGradedSupertrace (List.ofFn v) = 1 := by
    exact finite_boson_cancels_graded (List.ofFn v) hlist
  have hzeroGraded : finiteGradedSupertrace (List.ofFn v) = 0 := by
    simpa [finiteGradedSupertrace] using h
  have hfalse : (0 : ℂ) = 1 := by
    calc
      (0 : ℂ) = finiteBosonicDeterminant (List.ofFn v) * 0 := by ring
      _ = finiteBosonicDeterminant (List.ofFn v) * finiteGradedSupertrace (List.ofFn v) := by
            simp [hzeroGraded]
      _ = 1 := hcancel
  exact zero_ne_one hfalse

/-- Finite-stage cancellation under non-singularity assumptions.
    Equivalent to `boson * graded = 1` at finite cutoff.
-/
theorem souriau_stage_boson_graded_cancellation (n : ℕ) (v : SouriauFockStage n)
    (h : ∀ i : Fin n, v i ≠ 1) :
    souriauBosonicPartition n v * souriauMoebiusArithmeticIndex n v = 1 := by
  unfold souriauBosonicPartition souriauMoebiusArithmeticIndex souriauGradedFermionPartition
  apply finite_boson_cancels_graded
  intro x hx
  rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
  exact h i

/-- Split-signature paravector for the geometric/lightcone bookkeeping.
    Determinant is `σ² - γ²`; lightcone is `det = 0`.
-/
structure SplitParavector where
  scalar : ℝ
  bivector : ℝ
deriving DecidableEq

def SplitParavector.det (v : SplitParavector) : ℝ :=
  v.scalar ^ 2 - v.bivector ^ 2

def SplitParavector.parabolic (v : SplitParavector) : Prop :=
  v.det = 0

def paravectorTemperature (σ γ : ℝ) : SplitParavector :=
  { scalar := σ, bivector := γ }

theorem paravectorTemperature_det (σ γ : ℝ) :
    (paravectorTemperature σ γ).det = σ ^ 2 - γ ^ 2 := by
  rfl

theorem paravectorLightcone_iff (σ γ : ℝ) :
    (paravectorTemperature σ γ).parabolic ↔ σ ^ 2 = γ ^ 2 := by
  constructor
  · intro h
    have h0 : (paravectorTemperature σ γ).det = 0 := by
      simpa [SplitParavector.parabolic] using h
    exact sub_eq_zero.mp h0
  · intro hpar
    have h0 : σ ^ 2 - γ ^ 2 = 0 := sub_eq_zero.mpr hpar
    show (paravectorTemperature σ γ).parabolic
    simpa [SplitParavector.parabolic, SplitParavector.det, paravectorTemperature] using h0

/-- Stagewise synthesis theorem used by narrative layers.
    No analytic RH/global claims are added here.
-/
theorem souriau_thermo_colimit_synthesis :
    (∀ n, ∀ v : SouriauFockStage n, souriauDenominatorZero n v →
      souriauGradedIndexSingularity n v) ∧
    (∀ n, ∀ v : SouriauFockStage n,
      souriauGradedIndexSingularity n v → souriauDenominatorZero n v) ∧
    (∀ n, ∀ v : SouriauFockStage n, (∀ i : Fin n, v i ≠ 1) →
      souriauBosonicPartition n v * souriauMoebiusArithmeticIndex n v = 1) := by
  constructor
  · intro n v h
    exact souriauGradedIndex_zero_of_denominator_zero n v h
  constructor
  · intro n v h
    exact souriau_denominator_zero_of_gradedIndex_zero n v h
  · intro n v h
    exact souriau_stage_boson_graded_cancellation n v h

end SouriauThermoColimit
