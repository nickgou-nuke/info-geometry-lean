import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.Tactic
import InfoGeometry.Canonical.FilteredDirectInverseColimit
import InfoGeometry.Canonical.UHFInductiveLimitBoundary
import InfoGeometry.External.Auto.FermionicPrimonPartition

/-!
# Primon Thermodynamic Colimit

This module constructs the finite-stage categorical colimit presentation of
the fermionic Primon gas thermodynamics, satisfying the strict Colimit
Continuum Mandate.

We use the audited diagonal successor embeddings from `UHFInductiveColimitBoundary`
to construct the exact algebraic skeleton:
1. The filtered colimit of the diagonal observables `DiagAlg n`.
2. The compatible finite Gibbs expectation readout descended to that colimit.

No classical analysis, measure theory, or analytic continuation is used. The
colimit readout is structurally defined by compatibility of the finite
expectation values under the algebraic stage maps.
-/

noncomputable section

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveLimitBoundary
open CategoryTheory CategoryTheory.Limits

namespace InfoGeometry.Canonical.PrimonThermodynamicColimit

variable (primes : ℕ → ℕ) (β : ℝ)

/-- Unnormalized Boltzmann weight of a configuration `w : BitWord n` evaluated over the first `n` prime modes. -/
def finiteBoltzmannWeight (n : ℕ) (w : BitWord n) : ℝ :=
  (Finset.univ : Finset (Fin n)).prod fun i => fermionOccupationWeight (primes i) β (w i)

/-- The partition function is the strictly finite sum of unnormalized weights. -/
def finitePartitionFunction (n : ℕ) : ℝ :=
  (Finset.univ : Finset (BitWord n)).sum (finiteBoltzmannWeight primes β n)

/-- The normalized thermodynamic Gibbs state (probability measure on `BitWord n`). -/
def finiteGibbsState (n : ℕ) (w : BitWord n) : ℝ :=
  finiteBoltzmannWeight primes β n w / finitePartitionFunction primes β n

/-- The expected value of a diagonal observable `f : DiagAlg n` at stage `n`. -/
def expectedValue (n : ℕ) (f : DiagAlg n) : ℂ :=
  (Finset.univ : Finset (BitWord n)).sum fun w => f w * (finiteGibbsState primes β n w : ℂ)

/-- The single-prime partition factor at stage `n`. -/
def singlePrimeFactor (n : ℕ) : ℝ :=
  singlePrimeFermionPartition (primes n) β

theorem singlePrimeFactor_pos (n : ℕ) : 0 < singlePrimeFactor primes β n := by
  dsimp [singlePrimeFactor]
  rw [singlePrimeFermionPartition_eq]
  dsimp [fermionPrimeBoltzmannWeight]
  have h1 : (0 : ℝ) ≤ (primes n : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (primes n : ℝ) ^ (-β) := Real.rpow_nonneg h1 _
  linarith

theorem singlePrimeFactor_ne_zero (n : ℕ) : (singlePrimeFactor primes β n : ℂ) ≠ 0 := by
  have hpos := singlePrimeFactor_pos primes β n
  have hne : singlePrimeFactor primes β n ≠ 0 := ne_of_gt hpos
  exact_mod_cast hne

/-- The unnormalized Boltzmann weight factorizes when adding the `n`-th prime mode. -/
theorem finiteBoltzmannWeight_succ (n : ℕ) (w : BitWord (n + 1)) :
    finiteBoltzmannWeight primes β (n + 1) w =
      finiteBoltzmannWeight primes β n (prefixSucc n w) *
        fermionOccupationWeight (primes n) β (w ⟨n, Nat.lt_succ_self n⟩) := by
  dsimp [finiteBoltzmannWeight, prefixSucc]
  rw [Fin.prod_univ_castSucc]
  rfl

variable (n : ℕ)

def bitWordEquiv (n : ℕ) : BitWord (n + 1) ≃ (BitWord n × Bool) where
  toFun w := (prefixSucc n w, w ⟨n, Nat.lt_succ_self n⟩)
  invFun p := extendSucc n p.1 p.2
  left_inv w := by
    ext i
    dsimp [prefixSucc, extendSucc]
    split_ifs with h
    · rfl
    · have hi : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (Nat.le_antisymm (Nat.le_of_lt_succ i.2) (Nat.le_of_not_lt h))
      subst hi
      rfl
  right_inv p := by
    rcases p with ⟨w, b⟩
    ext
    · dsimp; rw [prefixSucc_extendSucc]
    · dsimp [extendSucc]; rw [dif_neg (lt_irrefl n)]

/-- The finite partition function factorizes exactly. -/
theorem finitePartitionFunction_succ :
    finitePartitionFunction primes β (n + 1) =
      finitePartitionFunction primes β n * singlePrimeFactor primes β n := by
  dsimp [finitePartitionFunction, singlePrimeFactor, singlePrimeFermionPartition]
  rw [← Equiv.sum_comp (bitWordEquiv n).symm]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hw : (bitWordEquiv n).symm (w, b) = extendSucc n w b := rfl
  rw [hw]
  have hb : (extendSucc n w b) ⟨n, Nat.lt_succ_self n⟩ = b := by
    dsimp [extendSucc]
    rw [dif_neg (lt_irrefl n)]
  rw [finiteBoltzmannWeight_succ, prefixSucc_extendSucc, hb]

/-- The finite-stage Gibbs partition is the product of its prime-mode factors. -/
theorem finitePartitionFunction_eq_prod_singlePrimeFactor (n : ℕ) :
    finitePartitionFunction primes β n =
      ∏ k ∈ Finset.range n, singlePrimeFactor primes β k := by
  induction n with
  | zero =>
      simp [finitePartitionFunction, finiteBoltzmannWeight]
  | succ n ih =>
      rw [finitePartitionFunction_succ primes β n, ih]
      simp [Finset.prod_range_succ]

/-! ## Finite normalization -/

theorem finitePartitionFunction_pos (n : ℕ) :
    0 < finitePartitionFunction primes β n := by
  induction n with
  | zero =>
      simp [finitePartitionFunction, finiteBoltzmannWeight]
  | succ n ih =>
      rw [finitePartitionFunction_succ]
      exact mul_pos ih (singlePrimeFactor_pos primes β n)

/-! The multiplicative stage readout has an additive Massieu form. -/

/-- The finite Gibbs Massieu potential satisfies the one-mode recurrence. -/
theorem finiteMassieu_succ (n : ℕ) :
    Real.log (finitePartitionFunction primes β (n + 1)) =
      Real.log (finitePartitionFunction primes β n) +
        Real.log (singlePrimeFactor primes β n) := by
  rw [finitePartitionFunction_succ primes β n]
  exact Real.log_mul
    (ne_of_gt (finitePartitionFunction_pos primes β n))
    (ne_of_gt (singlePrimeFactor_pos primes β n))

/-- The finite Gibbs Massieu potential is the sum of one-mode Massieu terms. -/
theorem finiteMassieu_eq_sum_singlePrimeMassieu (n : ℕ) :
    Real.log (finitePartitionFunction primes β n) =
      ∑ k ∈ Finset.range n, Real.log (singlePrimeFactor primes β k) := by
  induction n with
  | zero =>
      have h0 : finitePartitionFunction primes β 0 = 1 := by
        simp [finitePartitionFunction, finiteBoltzmannWeight]
      rw [h0]
      simp
  | succ n ih =>
      rw [finiteMassieu_succ primes β n, ih]
      rw [Finset.sum_range_succ]

theorem finiteBoltzmannWeight_nonneg (n : ℕ) (w : BitWord n) :
    0 ≤ finiteBoltzmannWeight primes β n w := by
  apply Finset.prod_nonneg
  intro i hi
  by_cases h : w i = true
  · simp only [fermionOccupationWeight, h, ↓reduceIte]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · simp [fermionOccupationWeight, h]

theorem finiteGibbsState_nonneg (n : ℕ) (w : BitWord n) :
    0 ≤ finiteGibbsState primes β n w := by
  exact div_nonneg (finiteBoltzmannWeight_nonneg primes β n w)
    (le_of_lt (finitePartitionFunction_pos primes β n))

theorem finiteGibbsState_sum_one (n : ℕ) :
    (Finset.univ : Finset (BitWord n)).sum
        (finiteGibbsState primes β n) = 1 := by
  simp only [finiteGibbsState]
  calc
    (Finset.univ : Finset (BitWord n)).sum
        (fun w => finiteBoltzmannWeight primes β n w /
          finitePartitionFunction primes β n) =
      ((Finset.univ : Finset (BitWord n)).sum
        (finiteBoltzmannWeight primes β n)) /
          finitePartitionFunction primes β n := by
            rw [Finset.sum_div]
    _ = 1 := by
      change finitePartitionFunction primes β n /
          finitePartitionFunction primes β n = 1
      exact div_self (ne_of_gt (finitePartitionFunction_pos primes β n))

/-- At zero inverse temperature, the finite Gibbs readout is the normalized
    diagonal trace already owned by the UHF boundary layer. -/
theorem expectedValue_zero_eq_stageTrace (n : ℕ) (f : DiagAlg n) :
    expectedValue primes 0 n f = stageTrace n f := by
  have hweight : ∀ w : BitWord n,
      finiteBoltzmannWeight primes 0 n w = 1 := by
    intro w
    simp [finiteBoltzmannWeight, fermionOccupationWeight,
      fermionPrimeBoltzmannWeight]
  have hpartition : finitePartitionFunction primes 0 n = (2 ^ n : ℝ) := by
    simp [finitePartitionFunction, hweight]
  unfold expectedValue finiteGibbsState
  simp_rw [hweight]
  rw [hpartition]
  dsimp [stageTrace]
  calc
    (∑ x : BitWord n, f x * ((1 / 2 ^ n : ℝ) : ℂ)) =
        ∑ x : BitWord n, ((1 / 2 ^ n : ℝ) : ℂ) * f x := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = ((1 / 2 ^ n : ℝ) : ℂ) * ∑ x : BitWord n, f x := by
          rw [Finset.mul_sum]
    _ = (1 / (2 ^ n : ℂ)) * ∑ x : BitWord n, f x := by
          congr 1
          norm_num
    _ = (2 ^ n : ℂ)⁻¹ * ∑ x : BitWord n, f x := by rw [one_div]

/-- The expected value is invariant under the diagonal successor embedding. -/
theorem expectedValue_compatible_succ (f : DiagAlg n) :
    expectedValue primes β (n + 1) (diagEmbedSucc n f) = expectedValue primes β n f := by
  dsimp [expectedValue, finiteGibbsState]
  rw [← Equiv.sum_comp (bitWordEquiv n).symm]
  rw [Fintype.sum_prod_type]
  rw [finitePartitionFunction_succ primes β n]
  push_cast
  have h_pull_f : ∀ w b, diagEmbedSucc n f ((bitWordEquiv n).symm (w, b)) = f w := by
    intro w b
    dsimp [diagEmbedSucc, bitWordEquiv]
    rw [prefixSucc_extendSucc]
  simp_rw [h_pull_f]
  apply Finset.sum_congr rfl
  intro w _
  have hw_weight : ∀ b, finiteBoltzmannWeight primes β (n + 1) ((bitWordEquiv n).symm (w, b)) =
      finiteBoltzmannWeight primes β n w * fermionOccupationWeight (primes n) β b := by
    intro b
    have h1 : (bitWordEquiv n).symm (w, b) = extendSucc n w b := rfl
    rw [h1, finiteBoltzmannWeight_succ, prefixSucc_extendSucc]
    have hb : (extendSucc n w b) ⟨n, Nat.lt_succ_self n⟩ = b := by dsimp [extendSucc]; rw [dif_neg (lt_irrefl n)]
    rw [hb]
  simp_rw [hw_weight]
  have h_frac_eq : (fun b => f w * (↑(finiteBoltzmannWeight primes β n w * fermionOccupationWeight (primes n) β b) / (↑(finitePartitionFunction primes β n) * ↑(singlePrimeFactor primes β n)))) =
      fun b => (f w * ↑(finiteBoltzmannWeight primes β n w) / ↑(finitePartitionFunction primes β n)) * ((fermionOccupationWeight (primes n) β b : ℂ) / (singlePrimeFactor primes β n : ℂ)) := by
    ext b
    push_cast
    ring
  rw [h_frac_eq, ← Finset.mul_sum]
  have h_sum_b : (Finset.univ : Finset Bool).sum (fun b => (fermionOccupationWeight (primes n) β b : ℂ) / (singlePrimeFactor primes β n : ℂ)) = 1 := by
    rw [← Finset.sum_div]
    have h_single : (Finset.univ : Finset Bool).sum (fun b => (fermionOccupationWeight (primes n) β b : ℂ)) = (singlePrimeFactor primes β n : ℂ) := by
      dsimp [singlePrimeFactor, singlePrimeFermionPartition]
      push_cast
      rfl
    rw [h_single]
    exact div_self (singlePrimeFactor_ne_zero primes β n)
  rw [h_sum_b]
  ring

/-! ## Native filtered colimit of the finite Gibbs observables -/

def thermoDiagEmbedLE
    {i j : ℕ} (hij : i ≤ j) :
    DiagAlg i →ₗ[ℂ] DiagAlg j where
  toFun f w := f (fun k => w ⟨k.1, Nat.lt_of_lt_of_le k.2 hij⟩)
  map_add' f g := by
    ext w
    rfl
  map_smul' c f := by
    ext w
    rfl

theorem thermoDiagEmbedLE_id (i : ℕ) :
    thermoDiagEmbedLE (le_refl i) = LinearMap.id := by
  ext f w
  rfl

theorem thermoDiagEmbedLE_comp
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (thermoDiagEmbedLE hjk).comp (thermoDiagEmbedLE hij) =
      thermoDiagEmbedLE (le_trans hij hjk) := by
  ext f w
  rfl

def primonThermoSystem :
    FilteredColimit.DirectInductiveSystem ℂ ℕ DiagAlg where
  f := fun {i j} hij => thermoDiagEmbedLE hij
  f_id := thermoDiagEmbedLE_id
  f_comp := by
    intro i j k hij hjk
    exact thermoDiagEmbedLE_comp hij hjk

abbrev primonThermoModuleDiagram : ℕ ⥤ ModuleCat ℂ :=
  FilteredColimit.Native.moduleDiagram primonThermoSystem

abbrev primonThermoColimit : Type :=
  (colimit primonThermoModuleDiagram : ModuleCat ℂ)

/-- The finite Gibbs expectation as a linear functional at one stage. -/
def stageExpectedValueLinear (primes : ℕ → ℕ) (β : ℝ) (n : ℕ) :
    DiagAlg n →ₗ[ℂ] ℂ where
  toFun f := expectedValue primes β n f
  map_add' f g := by
    dsimp [expectedValue]
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    dsimp [expectedValue]
    simp [mul_assoc, Finset.mul_sum]

@[simp] theorem stageExpectedValueLinear_apply
    (primes : ℕ → ℕ) (β : ℝ) (n : ℕ) (f : DiagAlg n) :
    stageExpectedValueLinear primes β n f = expectedValue primes β n f :=
  rfl

theorem stageExpectedValueLinear_one
    (primes : ℕ → ℕ) (β : ℝ) (n : ℕ) :
    stageExpectedValueLinear primes β n (1 : DiagAlg n) = 1 := by
  dsimp [stageExpectedValueLinear, expectedValue]
  simp only [one_mul]
  have h := finiteGibbsState_sum_one primes β n
  exact_mod_cast h

/-- A finite Gibbs expectation reads a constant observable as that constant. -/
theorem stageExpectedValueLinear_const
    (primes : ℕ → ℕ) (β : ℝ) (n : ℕ) (c : ℂ) :
    stageExpectedValueLinear primes β n (fun _ : BitWord n => c) = c := by
  have hconst : (fun _ : BitWord n => c) = c • (1 : DiagAlg n) := by
    ext w
    simp
  rw [hconst, map_smul, stageExpectedValueLinear_one]
  simp

theorem stageExpectedValue_compatible
    (primes : ℕ → ℕ) (β : ℝ)
    {i j : ℕ} (hij : i ≤ j) (f : DiagAlg i) :
    stageExpectedValueLinear primes β j (thermoDiagEmbedLE hij f) =
      stageExpectedValueLinear primes β i f := by
  induction hij with
  | refl => rfl
  | @step j hij ih =>
      calc
        stageExpectedValueLinear primes β (j + 1)
            (thermoDiagEmbedLE (Nat.le.step hij) f) =
            stageExpectedValueLinear primes β (j + 1)
              (diagEmbedSucc j (thermoDiagEmbedLE hij f)) := by
                rfl
        _ = stageExpectedValueLinear primes β j (thermoDiagEmbedLE hij f) := by
          exact expectedValue_compatible_succ primes β j
            (thermoDiagEmbedLE hij f)
        _ = stageExpectedValueLinear primes β i f := ih

def gibbsExpectationCocone (primes : ℕ → ℕ) (β : ℝ) :
    FilteredColimit.InductiveCocone ℂ primonThermoSystem ℂ :=
  ⟨(fun n => stageExpectedValueLinear primes β n), by
    intro i j hij
    apply LinearMap.ext
    intro f
    exact stageExpectedValue_compatible primes β hij f⟩

/-- The Gibbs expectation descends to the native categorical colimit. -/
noncomputable def gibbsExpectationColimit
    (primes : ℕ → ℕ) (β : ℝ) : primonThermoColimit →ₗ[ℂ] ℂ :=
  (FilteredColimit.Native.descendModuleCocone
    primonThermoSystem (gibbsExpectationCocone primes β)).hom

theorem gibbsExpectationColimit_on_stage
    (primes : ℕ → ℕ) (β : ℝ) (n : ℕ) (f : DiagAlg n) :
    gibbsExpectationColimit primes β
        ((colimit.ι primonThermoModuleDiagram n).hom f) =
      expectedValue primes β n f := by
  have h := colimit.ι_desc
    (FilteredColimit.Native.moduleCocone primonThermoSystem
      (gibbsExpectationCocone primes β)) n
  exact congrArg (fun g => g f) h

/-- The descended Gibbs readout is independent of the finite stage used to
represent an observable. -/
theorem gibbsExpectationColimit_on_embedded_stage
    (primes : ℕ → ℕ) (β : ℝ)
    {i j : ℕ} (hij : i ≤ j) (f : DiagAlg i) :
    gibbsExpectationColimit primes β
        ((colimit.ι primonThermoModuleDiagram j).hom
          (thermoDiagEmbedLE hij f)) =
      expectedValue primes β i f := by
  rw [gibbsExpectationColimit_on_stage]
  exact stageExpectedValue_compatible primes β hij f

/-- The colimit Gibbs readout specializes at zero inverse temperature to the
    normalized UHF stage trace on every injected finite observable. -/
theorem gibbsExpectationColimit_zero_on_stage_eq_stageTrace
    (primes : ℕ → ℕ) (n : ℕ) (f : DiagAlg n) :
    gibbsExpectationColimit primes 0
        ((colimit.ι primonThermoModuleDiagram n).hom f) =
      stageTrace n f := by
  rw [gibbsExpectationColimit_on_stage,
    expectedValue_zero_eq_stageTrace]

theorem gibbsExpectationColimit_on_one
    (primes : ℕ → ℕ) (β : ℝ) (n : ℕ) :
    gibbsExpectationColimit primes β
        ((colimit.ι primonThermoModuleDiagram n).hom (1 : DiagAlg n)) = 1 := by
  rw [gibbsExpectationColimit_on_stage]
  exact stageExpectedValueLinear_one primes β n

/-! The same normalization, now read directly on the native colimit. -/

theorem gibbsExpectationColimit_on_const
    (primes : ℕ → ℕ) (β : ℝ) (n : ℕ) (c : ℂ) :
    gibbsExpectationColimit primes β
        ((colimit.ι primonThermoModuleDiagram n).hom
          (fun _ : BitWord n => c)) = c := by
  rw [gibbsExpectationColimit_on_stage]
  exact stageExpectedValueLinear_const primes β n c

/-- The descended Gibbs expectation is uniquely determined by all finite-stage
    expectation values. -/
theorem gibbsExpectationColimit_unique
    (primes : ℕ → ℕ) (β : ℝ)
    (F : primonThermoColimit →ₗ[ℂ] ℂ)
    (hF : ∀ (n : ℕ) (f : DiagAlg n),
      F ((colimit.ι primonThermoModuleDiagram n).hom f) =
        expectedValue primes β n f) :
    F = gibbsExpectationColimit primes β := by
  have hhom :
      ModuleCat.ofHom F =
        ModuleCat.ofHom (gibbsExpectationColimit primes β) := by
    apply colimit.hom_ext
    intro n
    apply ModuleCat.hom_ext
    ext f
    change F ((colimit.ι primonThermoModuleDiagram n).hom f) =
      gibbsExpectationColimit primes β
        ((colimit.ι primonThermoModuleDiagram n).hom f)
    rw [hF n f, gibbsExpectationColimit_on_stage]
  exact congrArg
    (fun g : ModuleCat.of ℂ primonThermoColimit ⟶ ModuleCat.of ℂ ℂ => g.hom)
    hhom

end InfoGeometry.Canonical.PrimonThermodynamicColimit
end noncomputable section
