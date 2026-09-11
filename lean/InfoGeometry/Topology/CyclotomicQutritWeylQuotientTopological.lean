import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.CyclotomicCliffordPauliQutritTopological

/-!
# Quotient readout for qutrit Weyl words

The order-three clock and shift make every Weyl word depend only on its two
exponents modulo `3`.  This owner exposes the resulting factorization through
the finite residue space `Fin 3 × Fin 3` with its discrete topology.
-/

namespace InfoGeometry.Topology.CyclotomicQutritWeylQuotientTopological

open InfoGeometry.Canonical
open InfoGeometry.Topology.CyclotomicCliffordPauliQutritTopological

noncomputable section

def exponentResidue (n : ℕ) : Fin 3 :=
  ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩

def qutritWeylResidue (r : Fin 3 × Fin 3) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  qutritWeyl r.1.1 r.2.1

theorem qutritClock_pow_mod_three (n : ℕ) :
    qutritClock ^ n = qutritClock ^ (n % 3) := by
  rw [← Nat.mod_add_div n 3, pow_add, pow_mul, qutritClock_cube]
  simp

theorem qutritShift_pow_mod_three (n : ℕ) :
    qutritShift ^ n = qutritShift ^ (n % 3) := by
  rw [← Nat.mod_add_div n 3, pow_add, pow_mul, qutritShift_cube]
  simp

/-- Weyl words factor through the finite residue pair. -/
theorem topologicalQutritWeyl_factor_through_residue (a b : ℕ) :
    topologicalQutritWeyl a b =
      qutritWeylResidue (exponentResidue a, exponentResidue b) := by
  simp only [topologicalQutritWeyl, qutritWeylResidue, exponentResidue,
    qutritWeyl]
  rw [qutritClock_pow_mod_three, qutritShift_pow_mod_three]

/-- The residue map is continuous from the discrete exponent lattice. -/
def exponentResiduePair (p : ℕ × ℕ) : Fin 3 × Fin 3 :=
  (exponentResidue p.1, exponentResidue p.2)

/-- Every finite residue pair has a natural-number representative. -/
theorem exponentResiduePair_surjective :
    Function.Surjective exponentResiduePair := by
  intro r
  refine ⟨(r.1.1, r.2.1), ?_⟩
  apply Prod.ext
  · apply Fin.ext
    exact Nat.mod_eq_of_lt r.1.2
  · apply Fin.ext
    exact Nat.mod_eq_of_lt r.2.2

/-- The finite residue Weyl readout is continuous. -/
theorem continuous_qutritWeylResidue :
    Continuous qutritWeylResidue := by
  exact continuous_of_discreteTopology

/-- The natural Weyl readout factors through the finite residue readout. -/
theorem topologicalQutritWeyl_factorization
    (p : ℕ × ℕ) :
    topologicalQutritWeyl p.1 p.2 =
      qutritWeylResidue (exponentResiduePair p) := by
  exact topologicalQutritWeyl_factor_through_residue p.1 p.2

theorem continuous_exponentResiduePair :
    Continuous exponentResiduePair := by
  exact continuous_of_discreteTopology

theorem isOpenMap_exponentResiduePair :
    IsOpenMap exponentResiduePair := by
  intro s hs
  exact isOpen_discrete _

theorem isQuotientMap_exponentResiduePair :
    Topology.IsQuotientMap exponentResiduePair := by
  exact IsOpenMap.isQuotientMap isOpenMap_exponentResiduePair
    continuous_exponentResiduePair exponentResiduePair_surjective

/-- The finite Weyl readout has the quotient universal property. -/
theorem continuous_qutritWeylResidue_iff :
    Continuous qutritWeylResidue ↔
      Continuous (qutritWeylResidue ∘ exponentResiduePair) :=
  isQuotientMap_exponentResiduePair.continuous_iff

theorem continuous_qutritWeylResidue_comp :
    Continuous (qutritWeylResidue ∘ exponentResiduePair) := by
  apply continuous_topologicalQutritWeyl.congr
  intro p
  simpa [Function.comp_def] using topologicalQutritWeyl_factorization p

theorem isLocallyConstant_exponentResiduePair :
    IsLocallyConstant exponentResiduePair := by
  exact IsLocallyConstant.of_discrete (f := exponentResiduePair)

end
end InfoGeometry.Topology.CyclotomicQutritWeylQuotientTopological
