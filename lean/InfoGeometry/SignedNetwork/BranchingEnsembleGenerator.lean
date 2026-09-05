import InfoGeometry.SignedNetwork.ExactCancellation
import InfoGeometry.SignedNetwork.BalancedPairKernel

/-!
# A signed pair-branching generator on actual finite ensembles

The state is the existing `Counts C`, not its signed quotient. Each particle
is retained and generates two children with opposite relative signs. The
nonnegative event intensities are built from the existing balanced pair rate.

This owner proves the ensemble generator identity, finite total rates,
population Lyapunov identities, and invariance of the linear drift under exact
cancellation. These are local jump-generator theorems, not a construction of
an infinite-time stochastic process or a claim of nonexplosion by definition.
-/

noncomputable section

namespace InfoGeometry.SignedNetwork.BranchingEnsembleGenerator

open InfoGeometry.SignedNetwork.ExactCancellation
open InfoGeometry.SignedNetwork.BalancedPairKernel

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The zero-rate case is included in the total pair intensity. -/
theorem total_pairRate_all (w : C → ℝ) (hw : ∑ a, w a = 0) :
    (∑ a, ∑ b, pairRate w a b) = positiveMass w := by
  by_cases hγ : positiveMass w = 0
  · have hw0 := zero_column_of_zero_mass w hw hγ
    subst w
    simp [pairRate, positivePart, negativePart, positiveMass]
  · exact total_pairRate w hw hγ

/-- A nonnegative population has one indicator unit at a specified cell. -/
def atom (a x : C) : ℕ := if x = a then 1 else 0

@[simp] theorem atom_cast (a x : C) :
    (atom a x : ℝ) = if x = a then 1 else 0 := by
  by_cases hx : x = a <;> simp [atom, hx]

/-- A positive parent creates a positive child at `a` and a negative child at `b`.
The parent is not removed. -/
def birthPositive (p : Counts C) (a b : C) : Counts C :=
  ⟨fun x => p.positive x + atom a x, fun x => p.negative x + atom b x⟩

/-- A negative parent reverses both child signs, not the routing direction. -/
def birthNegative (p : Counts C) (a b : C) : Counts C := birthPositive p b a

/-- Real-valued unscaled signed readout, reusing the existing integer readout. -/
def signedReal (p : Counts C) (x : C) : ℝ := (signed p x : ℝ)

/-- The actual unsigned number of active samples. -/
def population (p : Counts C) : ℕ := ∑ x, p.positive x + p.negative x

def mass (p : Counts C) : ℝ := (population p : ℝ)

@[simp] theorem signedReal_eq (p : Counts C) (x : C) :
    signedReal p x = (p.positive x : ℝ) - (p.negative x : ℝ) := by
  simp [signedReal, signed]

@[simp] theorem signedReal_cancel (p : Counts C) (x : C) :
    signedReal (cancel p) x = signedReal p x := by
  simp only [signedReal, signed_cancel]

@[simp] theorem signedReal_addNullPairs (p : Counts C) (k : C → ℕ) (x : C) :
    signedReal (addNullPairs p k) x = signedReal p x := by
  simp only [signedReal, signed_addNullPairs]

/-- The positive-parent increment is an actual difference of ensemble readouts. -/
theorem signedReal_birthPositive_sub (p : Counts C) (a b x : C) :
    signedReal (birthPositive p a b) x - signedReal p x =
      (atom a x : ℝ) - (atom b x : ℝ) := by
  simp only [signedReal_eq, birthPositive, Nat.cast_add]
  ring

/-- The negative-parent increment is exactly the opposite one. -/
theorem signedReal_birthNegative_sub (p : Counts C) (a b x : C) :
    signedReal (birthNegative p a b) x - signedReal p x =
      -((atom a x : ℝ) - (atom b x : ℝ)) := by
  rw [birthNegative, signedReal_birthPositive_sub]
  ring

@[simp] theorem population_birthPositive (p : Counts C) (a b : C) :
    population (birthPositive p a b) = population p + 2 := by
  simp [population, birthPositive, atom, Finset.sum_add_distrib,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

@[simp] theorem population_birthNegative (p : Counts C) (a b : C) :
    population (birthNegative p a b) = population p + 2 := by
  exact population_birthPositive p b a

/-- Pruning cannot increase the number of active samples. -/
theorem population_cancel_le (p : Counts C) : population (cancel p) ≤ population p := by
  apply Finset.sum_le_sum
  intro x _hx
  dsimp [cancel]
  omega

theorem mass_nonneg (p : Counts C) : 0 ≤ mass p := by
  exact Nat.cast_nonneg _

theorem mass_eq_sum (p : Counts C) :
    mass p = ∑ x, ((p.positive x : ℝ) + (p.negative x : ℝ)) := by
  simp [mass, population, Nat.cast_sum, Nat.cast_add]

/-- Parent cell, positive-relative child, negative-relative child, and parent
sign index. `0` denotes a positive parent and `1` a negative parent. -/
abbrev Event (C : Type*) := C × C × C × Fin 2

/-- The jump acts on the full count state, not on a prescribed signed increment. -/
def applyEvent (p : Counts C) (e : Event C) : Counts C :=
  if e.2.2.2 = 0 then birthPositive p e.2.1 e.2.2.1
  else birthNegative p e.2.1 e.2.2.1

/-- Intensities count all eligible parents. Impossible parent choices have rate zero. -/
def eventRate (L : Matrix C C ℝ) (p : Counts C) (e : Event C) : ℝ :=
  (if e.2.2.2 = 0 then (p.positive e.1 : ℝ) else (p.negative e.1 : ℝ)) *
    pairRate (fun x => L x e.1) e.2.1 e.2.2.1

/-- The total marked-event rate. Self-jumps, if present after pruning, are retained. -/
def totalRate (L : Matrix C C ℝ) (p : Counts C) : ℝ := ∑ e, eventRate L p e

/-- Generator on scalar observables of the full count state. -/
def generator (L : Matrix C C ℝ) (F : Counts C → ℝ) (p : Counts C) : ℝ :=
  ∑ e, eventRate L p e * (F (applyEvent p e) - F p)

/-- Same intensities, with exact cancellation applied after every event. -/
def generatorAfterCancel (L : Matrix C C ℝ) (F : Counts C → ℝ)
    (p : Counts C) : ℝ :=
  ∑ e, eventRate L p e * (F (cancel (applyEvent p e)) - F p)

/-- The specified finite linear drift, with columns interpreted as parent cells. -/
def linearDrift (L : Matrix C C ℝ) (p : Counts C) (x : C) : ℝ :=
  ∑ b, L x b * signedReal p b

theorem eventRate_nonneg (L : Matrix C C ℝ) (p : Counts C) (e : Event C) :
    0 ≤ eventRate L p e := by
  unfold eventRate
  apply mul_nonneg
  · split_ifs <;> exact Nat.cast_nonneg _
  · exact pairRate_nonneg _ _ _

theorem totalRate_nonneg (L : Matrix C C ℝ) (p : Counts C) :
    0 ≤ totalRate L p :=
  Finset.sum_nonneg (fun e _ => eventRate_nonneg L p e)

theorem eventRate_le_totalRate (L : Matrix C C ℝ) (p : Counts C) (e : Event C) :
    eventRate L p e ≤ totalRate L p :=
  Finset.single_le_sum (fun f _ => eventRate_nonneg L p f) (Finset.mem_univ e)

/-- Zero total rate is genuinely absorbing, not a division-by-zero convention. -/
theorem eventRate_eq_zero_of_totalRate_eq_zero
    (L : Matrix C C ℝ) (p : Counts C) (hq : totalRate L p = 0) (e : Event C) :
    eventRate L p e = 0 := by
  apply le_antisymm _ (eventRate_nonneg L p e)
  simpa [hq] using eventRate_le_totalRate L p e

theorem generator_eq_zero_of_totalRate_eq_zero
    (L : Matrix C C ℝ) (p : Counts C) (hq : totalRate L p = 0)
    (F : Counts C → ℝ) : generator L F p = 0 := by
  unfold generator
  simp only [eventRate_eq_zero_of_totalRate_eq_zero L p hq, zero_mul,
    Finset.sum_const_zero]

@[simp] theorem population_applyEvent (p : Counts C) (e : Event C) :
    population (applyEvent p e) = population p + 2 := by
  unfold applyEvent
  split_ifs <;> simp

@[simp] theorem mass_applyEvent (p : Counts C) (e : Event C) :
    mass (applyEvent p e) = mass p + 2 := by
  simp [mass, population_applyEvent]

/-- The total intensity equals the sum of all individual birth rates. -/
theorem totalRate_eq (L : Matrix C C ℝ)
    (hL : ∀ b, ∑ a, L a b = 0) (p : Counts C) :
    totalRate L p =
      ∑ b, ((p.positive b : ℝ) + (p.negative b : ℝ)) *
        positiveMass (fun a => L a b) := by
  unfold totalRate
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  change (∑ b, ∑ a, ∑ d,
    ((p.positive b : ℝ) * pairRate (fun x => L x b) a d +
      (p.negative b : ℝ) * pairRate (fun x => L x b) a d)) = _
  apply Finset.sum_congr rfl
  intro b _hb
  simp_rw [← add_mul, ← Finset.mul_sum]
  rw [total_pairRate_all _ (hL b)]

/-- The mean signed increment of one parent's pair law. -/
theorem pairRate_atom_difference (w : C → ℝ) (hw : ∑ a, w a = 0) (x : C) :
    (∑ a, ∑ b, pairRate w a b * ((atom a x : ℝ) - (atom b x : ℝ))) = w x := by
  have ha : (∑ a, ∑ b, pairRate w a b * (atom a x : ℝ)) =
      ∑ b, pairRate w x b := by
    rw [Finset.sum_comm]
    simp [atom_cast, mul_ite]
  have hb : (∑ a, ∑ b, pairRate w a b * (atom b x : ℝ)) =
      ∑ a, pairRate w a x := by
    simp [atom_cast, mul_ite]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [ha, hb]
  exact pairRate_recovers_column_all w hw x

/-- The ensemble jump generator acts on the signed coordinate as the given
finite linear generator. The stochastic first-moment equation is not assumed. -/
theorem generator_signedReal (L : Matrix C C ℝ)
    (hL : ∀ b, ∑ a, L a b = 0) (p : Counts C) (x : C) :
    generator L (fun n => signedReal n x) p = linearDrift L p x := by
  unfold generator linearDrift
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  change (∑ b, ∑ a, ∑ d,
    ((p.positive b : ℝ) * pairRate (fun y => L y b) a d *
        (signedReal (birthPositive p a d) x - signedReal p x) +
      (p.negative b : ℝ) * pairRate (fun y => L y b) a d *
        (signedReal (birthNegative p a d) x - signedReal p x))) = _
  apply Finset.sum_congr rfl
  intro b _hb
  simp only [signedReal_birthPositive_sub, signedReal_birthNegative_sub]
  calc
    _ = ((p.positive b : ℝ) - (p.negative b : ℝ)) *
        (∑ a, ∑ d, pairRate (fun y => L y b) a d *
          ((atom a x : ℝ) - (atom d x : ℝ))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro d _hd
      ring
    _ = L x b * signedReal p b := by
      rw [pairRate_atom_difference _ (hL b) x, signedReal_eq]
      ring

/-- After-jump pruning leaves every signed-coordinate drift unchanged. -/
theorem generatorAfterCancel_signedReal (L : Matrix C C ℝ)
    (hL : ∀ b, ∑ a, L a b = 0) (p : Counts C) (x : C) :
    generatorAfterCancel L (fun n => signedReal n x) p = linearDrift L p x := by
  unfold generatorAfterCancel
  simp only [signedReal_cancel]
  exact generator_signedReal L hL p x

/-- Removing null pairs before generating the next event changes the event
rate but not the physical-time drift of the signed coordinate. -/
theorem generator_signedReal_cancel_input (L : Matrix C C ℝ)
    (hL : ∀ b, ∑ a, L a b = 0) (p : Counts C) (x : C) :
    generator L (fun n => signedReal n x) (cancel p) =
      generator L (fun n => signedReal n x) p := by
  rw [generator_signedReal L hL, generator_signedReal L hL]
  simp only [linearDrift, signedReal_cancel]

/-- A balanced signed drift vanishes at an absorbing ensemble. -/
theorem linearDrift_eq_zero_of_totalRate_eq_zero (L : Matrix C C ℝ)
    (hL : ∀ b, ∑ a, L a b = 0) (p : Counts C) (hq : totalRate L p = 0) :
    linearDrift L p = 0 := by
  funext x
  rw [← generator_signedReal L hL]
  exact generator_eq_zero_of_totalRate_eq_zero L p hq _

/-- First population Lyapunov identity; every marked birth adds two samples. -/
theorem generator_mass (L : Matrix C C ℝ) (p : Counts C) :
    generator L mass p = 2 * totalRate L p := by
  unfold generator totalRate
  simp only [mass_applyEvent, add_sub_cancel_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  ring

/-- Second population identity, available for later uniform-integrability estimates. -/
theorem generator_mass_sq (L : Matrix C C ℝ) (p : Counts C) :
    generator L (fun n => mass n ^ 2) p =
      (4 * mass p + 4) * totalRate L p := by
  unfold generator totalRate
  simp only [mass_applyEvent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  ring

/-- Any finite upper bound on the per-particle rates bounds the ensemble rate. -/
theorem totalRate_le (L : Matrix C C ℝ) (hL : ∀ b, ∑ a, L a b = 0)
    (Γ : ℝ) (hΓ : ∀ b, positiveMass (fun a => L a b) ≤ Γ) (p : Counts C) :
    totalRate L p ≤ Γ * mass p := by
  rw [totalRate_eq L hL, mass_eq_sum]
  calc
    _ ≤ ∑ b, ((p.positive b : ℝ) + (p.negative b : ℝ)) * Γ := by
      apply Finset.sum_le_sum
      intro b _hb
      exact mul_le_mul_of_nonneg_left (hΓ b) (by positivity)
    _ = Γ * ∑ b, ((p.positive b : ℝ) + (p.negative b : ℝ)) := by
      rw [← Finset.sum_mul]
      ring

/-- An explicit finite bound; it avoids a nonempty-cell assumption needed by a maximum. -/
def uniformRateBound (L : Matrix C C ℝ) : ℝ :=
  ∑ b, positiveMass (fun a => L a b)

theorem uniformRateBound_nonneg (L : Matrix C C ℝ) : 0 ≤ uniformRateBound L := by
  apply Finset.sum_nonneg
  intro b _hb
  exact Finset.sum_nonneg (fun a _ => positivePart_nonneg _ a)

theorem individualRate_le_uniformRateBound (L : Matrix C C ℝ) (b : C) :
    positiveMass (fun a => L a b) ≤ uniformRateBound L := by
  apply Finset.single_le_sum _ (Finset.mem_univ b)
  intro d _hd
  exact Finset.sum_nonneg (fun a _ => positivePart_nonneg _ a)

/-- A derived linear rate bound, not a nonexplosion hypothesis. -/
theorem totalRate_le_uniformRateBound (L : Matrix C C ℝ)
    (hL : ∀ b, ∑ a, L a b = 0) (p : Counts C) :
    totalRate L p ≤ uniformRateBound L * mass p :=
  totalRate_le L hL _ (individualRate_le_uniformRateBound L) p

/-- The local Lyapunov inequality needed by the stopped-process argument. -/
theorem generator_mass_le (L : Matrix C C ℝ)
    (hL : ∀ b, ∑ a, L a b = 0) (p : Counts C) :
    generator L mass p ≤ (2 * uniformRateBound L) * mass p := by
  rw [generator_mass]
  nlinarith [totalRate_le_uniformRateBound L hL p]

/-- Exact pruning also satisfies the same population drift bound. -/
theorem generatorAfterCancel_mass_le (L : Matrix C C ℝ)
    (hL : ∀ b, ∑ a, L a b = 0) (p : Counts C) :
    generatorAfterCancel L mass p ≤ (2 * uniformRateBound L) * mass p := by
  apply le_trans _ (generator_mass_le L hL p)
  unfold generatorAfterCancel generator
  apply Finset.sum_le_sum
  intro e _he
  apply mul_le_mul_of_nonneg_left _ (eventRate_nonneg L p e)
  apply sub_le_sub_right
  exact_mod_cast population_cancel_le (applyEvent p e)

end InfoGeometry.SignedNetwork.BranchingEnsembleGenerator
