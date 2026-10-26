/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.MassSpectrometry.RationalCandidate

/-!
# Explicit atom-inventory and charge balance

Inventory coordinates are caller-declared atom/isotope species. These checks
concern the supplied inventories; they do not infer them from a molecular graph
or validate valence. A zero loss charge enforces neutrality separately.
-/

namespace InfoGeometry.MassSpectrometry

/-- Proof-free fragment inventories and declared losses on directed edges. -/
structure CandidateChemistry (n a : ℕ) where
  inventory : Fin n → Fin a → ℕ
  lossInventory : Fin n → Fin n → Fin a → ℕ
  charge : Fin n → ℤ
  lossCharge : Fin n → Fin n → ℤ

namespace CandidateChemistry
variable {n k a : ℕ} (chem : CandidateChemistry n a) (c : RationalCandidate n k)

/-- Exact element/isotope counts and charge balance on every declared edge. -/
def Conserves : Prop :=
  ∀ u v, c.edge u v = true →
    (∀ s, chem.inventory u s = chem.inventory v s + chem.lossInventory u v s) ∧
    chem.charge u = chem.charge v + chem.lossCharge u v

instance : Decidable (chem.Conserves c) := by unfold Conserves; infer_instance

def check : Bool := decide (chem.Conserves c)

@[simp] theorem check_eq_true_iff : chem.check c = true ↔ chem.Conserves c := by
  simp [check]

/-- Neutral losses are an additional check, not a consequence of mass descent. -/
def checkNeutralLosses : Bool :=
  decide (∀ u v, c.edge u v = true → chem.lossCharge u v = 0)

theorem neutralLoss_charge_preserved (hc : chem.check c = true)
    (hn : chem.checkNeutralLosses c = true) {u v : Fin n} (he : c.edge u v = true) :
    chem.charge u = chem.charge v := by
  have hzero := of_decide_eq_true hn u v he
  have hcharge := ((chem.check_eq_true_iff c).mp hc u v he).2
  simpa [hzero] using hcharge

/-- Checked inventories cannot grow along any nonempty fragmentation path. -/
theorem inventory_mono_along_path (hc : chem.check c = true)
    {u v : Fin n} (path : Relation.TransGen (fun x y => c.edge x y = true) u v)
    (s : Fin a) : chem.inventory v s ≤ chem.inventory u s := by
  have hedge : ∀ x y, c.edge x y = true → chem.inventory y s ≤ chem.inventory x s := by
    intro x y hxy
    have h := ((chem.check_eq_true_iff c).mp hc x y hxy).1 s
    omega
  induction path with
  | single h => exact hedge _ _ h
  | tail _ h ih => exact le_trans (hedge _ _ h) ih

/-- Inventory conservation implies conservation of any declared additive
species mass model. No empirical atomic-mass table is assumed. -/
theorem additive_mass_balance (hc : chem.check c = true)
    (mass : Fin a → ℚ) {u v : Fin n} (he : c.edge u v = true) :
    (∑ s, (chem.inventory u s : ℚ) * mass s) =
      (∑ s, (chem.inventory v s : ℚ) * mass s) +
        ∑ s, (chem.lossInventory u v s : ℚ) * mass s := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [((chem.check_eq_true_iff c).mp hc u v he).1 s, Nat.cast_add, add_mul]

/-- Optional explicit link between candidate masses and the declared additive
inventory model. The caller supplies the species masses and unit convention. -/
def checkMassModel (mass : Fin a → ℚ) : Bool :=
  decide (∀ u, c.fragmentMass u = ∑ s, (chem.inventory u s : ℚ) * mass s)

/-- Checking the mass link turns inventory conservation into a statement about
the candidate's own mass valuation, not an unrelated inventory readout. -/
theorem fragment_mass_balance (hc : chem.check c = true) (mass : Fin a → ℚ)
    (hm : chem.checkMassModel c mass = true) {u v : Fin n} (he : c.edge u v = true) :
    c.fragmentMass u - c.fragmentMass v =
      ∑ s, (chem.lossInventory u v s : ℚ) * mass s := by
  have hmass : ∀ x, c.fragmentMass x =
      ∑ s, (chem.inventory x s : ℚ) * mass s := of_decide_eq_true hm
  rw [hmass u, hmass v, chem.additive_mass_balance c hc mass he]
  ring

end CandidateChemistry
end InfoGeometry.MassSpectrometry
